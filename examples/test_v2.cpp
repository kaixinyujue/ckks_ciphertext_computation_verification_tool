//
// test on 2024/10/12.
//
#include <iostream>
#include <fstream>
#include <filesystem>
#include <vector>
#include <random>
#include <string>
#include <cmath>
#include <boost/math/distributions/normal.hpp>
#include <ringsnark/gadgetlib/protoboard.hpp>
#include <ringsnark/seal/seal_ring.hpp>
#include <ringsnark/seal/seal_util.hpp>
#include <ringsnark/zk_proof_systems/groth16/groth16.hpp>
#include <ringsnark/zk_proof_systems/rinocchio/rinocchio.hpp>

#include "poly_arith.h"
#include "seal/seal.h"

#define UNSIZEMAX 4294967295
#define ModulusDegree 4096
#define Inner_N 12288
#define S_P 50
#define EI 1
#define DEVICE_MEMORY_MAX 50000000
#define ConfidenceLevel 0.99


using namespace std;
using namespace seal;
using namespace ringsnark;
typedef ringsnark::seal::RingElem R;
typedef ringsnark::seal::EncodingElem E;


std::string sl_path0;
bool e_des;

class Circuit {
public:
    // ######################## 第一步 初始化电路
    Circuit(ringsnark::protoboard<R> &pb, vector<vector<size_t>> coeff, vector<vector<size_t>> ex, vector<vector<size_t>> aj) {
        // 变量与电路板直接建立关系，相当于把组件插入到电路板上，allocate方法第二个参数类似于注释，方便查看日志
        //计算一共有多少变量
        // cout << "entering into: " << __FUNCTION__  << endl;
        coefficient = coeff;
        exp = ex;
        size_t numInput = 0;

        if(aj.size()==0){
            no_aj = true;
            // cout<< "no_aj"<<endl;
        }
        else{
            no_aj = false;
            for(int i=0;i<aj[0].size();i++){
                aj0.push_back(1.0*aj[0][i]);
            }
        }

        for(int i=0;i<coefficient.size();i++){
            for(int j=0;j<coefficient[i].size();j++){
                if(numInput<coefficient[i][j]){
                    numInput = coefficient[i][j];
                }
            }
        }
        numInput++;

        ex_unfold = 3;
        if(aj.size()>1){  //exist e^x
            cout<<"exist e^x"<<endl;
            factorflag = false;
            factorial(ex_unfold);
            for(int i=0; i<EI; i++){
                ex_to_x(aj, numInput);

                vector<size_t> aj1;
                for(int j=0; j<aj0.size();j++){
                    aj1.push_back(1);
                }
                aj.pop_back();
                aj.push_back(aj1);
            }
        }

        num_input = numInput; // 只包括输入，不包括输出
        size_t num = 0;
        if(coefficient.size() != exp.size()) {
            cout << "error: the size of coefficient is not equal to exp" << endl;
            return;
        }
        for(int i = 0; i < exp.size(); i++) {
            for(int j = 0; j < exp[i].size(); j++) {
                if(exp[i][j] > 1) {
                    num += (exp[i][j] - 1) * 9;
                }
            }
        }
        
        for(int i = 0; i < coefficient.size(); i++) {
            num += (coefficient[i].size() - 1) * 9;
        }

        num += (coefficient.size() - 1) * 2;
        if(!no_aj){
            num += coefficient.size() * 2;
        }
        else if(coefficient.size()==1 && coefficient[0].size()==1 && exp[0][0]==1){
            num += 2;
        }

        //num包含输出
        // cout << "num: " << num << endl;
        num_var = num_input*2 + num;
        vars = ringsnark::pb_variable_array<R>(num_var, ringsnark::pb_variable<R>());
        vars.allocate(pb, num_var , "vars");

        num_avar = coefficient.size();
        // avar= ringsnark::pb_variable_array<R>(num_avar, ringsnark::pb_variable<R>());
        // avar.allocate(pb, num_avar , "avar");

        pb.set_input_sizes((num_input + 1) * 2) ;  // vars[4] is private, all other values are public
        // zkSNARKs需要区分public input与private witness，set_input_sizes用来干这个事情，输入参数为n（从1开始计数），表明前n个参数是public input，其余都是private

        constant_one.allocate(pb, "one");
        // cout << "exit: " << __FUNCTION__  << endl;
    }

    void aj_to_aplain(SEALContext context, double scale, ringsnark::protoboard<R>& pb){

        ringsnark::pb_variable<R> constant_relin0 = ringsnark::pb_variable<R>();
        ringsnark::pb_variable<R> constant_relin1 = ringsnark::pb_variable<R>();
        relinR.push_back(constant_relin0);
        relinR[0].allocate(pb, "constant_relin0");
        relinR.push_back(constant_relin1);
        relinR[1].allocate(pb, "constant_relin1");

        if(no_aj){
            return;
        }

        CKKSEncoder encoder(context);
        Plaintext apt;

        for(int i=0;i<aj0.size();i++){
            encoder.encode(aj0[i], scale, apt);
            a_plain.push_back(apt);

            ringsnark::pb_variable<R> constant_tmp = ringsnark::pb_variable<R>();
            aR.push_back(constant_tmp);
            aR[i].allocate(pb, "constant_" + std::to_string(i));
            // pb.val(aR[i]) = ringsnark::seal::RingElem(aj0[i]);
        }
    }

    void generate_r1cs_constraints(ringsnark::protoboard<R>& pb)  {
        // 组件以及插入到了电路板上，下面需要按照约束链接几个组件
        // 注意，此处r1cs_constraint方法只涉及乘法，如果要计算加法可以把sym_2 = y + x看成是sym_2 = (y + x) * 1，符合电路到QAP的变换知识
        // x*x = sym_1
        // cout << "entering into: " << __FUNCTION__  << endl;
        size_t index_for_output = num_input * 2;
        size_t index = (num_input + 1) * 2;
        size_t last_idx = index;
        vector<vector<size_t>> var_for_mul;
        vector<size_t> var_for_add;
        vector<size_t> var_a;
        //ji
        vector<size_t> temp_val;
        // cout << "debug: " << endl;
        // cout << "coefficient.size(): " << coefficient.size() << endl;
        //如果没有加法
        if(coefficient.size() == 1) {
            //如果没有乘法
            if(coefficient[0].size() == 1) {
                if(exp[0][0] == 1) {
                    if(no_aj){
                        last_idx = cipherText_r1cs_mul(pb, index, coefficient[0][0]*2, UNSIZEMAX, true, index_for_output);
                    }
                    else{
                        last_idx = cipherText_r1cs_mul(pb, index, coefficient[0][0]*2, UNSIZEMAX, true);
                        last_idx = cipherText_r1cs_mul(pb, index, last_idx, 0, true, index_for_output);
                    }
                    // pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[coefficient[0][0]], constant_one, avar[0]));
                    // pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(avar[0], aR[0], vars[index_for_output]));
                }else if(exp[0][0] == 2) {
                    if(no_aj){
                        last_idx = cipherText_r1cs_mul(pb, index, coefficient[0][0]*2, coefficient[0][0]*2, false, index_for_output);
                    }
                    else{
                        last_idx = cipherText_r1cs_mul(pb, index, coefficient[0][0]*2, coefficient[0][0]*2);
                        last_idx = cipherText_r1cs_mul(pb, index, last_idx, 0, true, index_for_output);
                    }
                    // pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[coefficient[0][0]], vars[coefficient[0][0]], avar[0]));
                    // pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(avar[0], aR[0], vars[index_for_output]));
                }else {
                    for(int i = 2; i <= exp[0][0]; i++) {
                        if(i == 2) {
                            last_idx = cipherText_r1cs_mul(pb, index, coefficient[0][0]*2, coefficient[0][0]*2);
                            // pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[coefficient[0][0]], vars[coefficient[0][0]], vars[index]));
                            // index++;
                        }else if(i != exp[0][0]) {
                            last_idx = cipherText_r1cs_mul(pb, index, coefficient[0][0]*2, last_idx);
                            // pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[coefficient[0][0]], vars[index - 1], vars[index]));
                            // index++;
                        }else {
                            if(no_aj){
                                last_idx = cipherText_r1cs_mul(pb, index, coefficient[0][0]*2, last_idx, false, index_for_output);
                            }
                            else{
                                last_idx = cipherText_r1cs_mul(pb, index, coefficient[0][0]*2, last_idx);
                                last_idx = cipherText_r1cs_mul(pb, index, last_idx, 0, true, index_for_output);
                            }
                            // pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[coefficient[0][0]], vars[index - 1], avar[0]));
                            // pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(avar[0], aR[0], vars[index_for_output]));
                        }
                    }

                }
            }
                //如果有乘法
            else {
                for(int i = 0; i < coefficient[0].size(); i++) {
                    //进行幂运算
                    if (exp[0][i] == 1) {
                        temp_val.push_back(coefficient[0][i]*2);
                    } else if (exp[0][i] == 2) {
                        last_idx = cipherText_r1cs_mul(pb, index, coefficient[0][i]*2, coefficient[0][i]*2);
                        temp_val.push_back(last_idx);
                        // pb.add_r1cs_constraint(
                        //         ringsnark::r1cs_constraint<R>(vars[coefficient[0][i]], vars[coefficient[0][i]],
                        //                                       vars[index]));
                        // index++;
                        // temp_val.push_back(index - 1);
                    } else {
                        for (int j = 2; j <= exp[0][i]; j++) {
                            if (j == 2) {
                                last_idx = cipherText_r1cs_mul(pb, index, coefficient[0][i]*2, coefficient[0][i]*2);
                                // pb.add_r1cs_constraint(
                                //         ringsnark::r1cs_constraint<R>(vars[coefficient[0][i]], vars[coefficient[0][i]],
                                //                                       vars[index]));
                                // index++;
                            } else if (j != exp[0][i]) {
                                last_idx = cipherText_r1cs_mul(pb, index, coefficient[0][i]*2, last_idx);
                                // pb.add_r1cs_constraint(
                                //         ringsnark::r1cs_constraint<R>(vars[coefficient[0][i]], vars[index - 1],
                                //                                       vars[index]));
                                // index++;
                            } else {
                                last_idx = cipherText_r1cs_mul(pb, index, coefficient[0][i]*2, last_idx);
                                temp_val.push_back(last_idx);
                                // pb.add_r1cs_constraint(
                                //         ringsnark::r1cs_constraint<R>(vars[coefficient[0][i]], vars[index - 1],
                                //                                       vars[index]));
                                // index++;
                                // temp_val.push_back(index - 1);
                            }
                        }
                    }
                }
                //进行乘法运算
                if(temp_val.size() == 2) {
                    // cout << "size of vars:"<< vars.size() << endl;
                    if(no_aj){
                        last_idx = cipherText_r1cs_mul(pb, index, temp_val[0], temp_val[1], false, index_for_output);
                    }
                    else{
                        last_idx = cipherText_r1cs_mul(pb, index, temp_val[0], temp_val[1]);
                        last_idx = cipherText_r1cs_mul(pb, index, last_idx, 0, true, index_for_output);
                    }
                    // cout << "gr1cs_debug2" << endl;
                    // pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[temp_val[0]], vars[temp_val[1]], avar[0]));
                    // pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(avar[0], aR[0], vars[index_for_output]));
                }else {
                    for(int j = 1; j < temp_val.size(); j++) {
                        if(j == 1) {
                            last_idx = cipherText_r1cs_mul(pb, index, temp_val[j - 1], temp_val[j]);
                            // pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[temp_val[j - 1]], vars[temp_val[j]], vars[index]));
                            // index++;
                        }else if(j != temp_val.size() - 1) {
                            last_idx = cipherText_r1cs_mul(pb, index, temp_val[j], last_idx);
                            // pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[temp_val[j]], vars[index - 1], vars[index]));
                            // index++;
                        }else {
                            if(no_aj){
                                last_idx = cipherText_r1cs_mul(pb, index, temp_val[j], last_idx, false, index_for_output);
                            }
                            else{
                                last_idx = cipherText_r1cs_mul(pb, index, temp_val[j], last_idx);
                                last_idx = cipherText_r1cs_mul(pb, index, last_idx, 0, true, index_for_output);
                            }
                            // pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[temp_val[j]], vars[index - 1], avar[0]));
                            // pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(avar[0], aR[0], vars[index_for_output]));
                        }
                    }
                }
            }
        }
            //如果有加法
        else {
            for(int i = 0; i < coefficient.size(); i++) {
                temp_val.clear();
                if(exp[i].size() != coefficient[i].size()) {
                    cout << "exp" << i << "is not equal to coe" << endl;
                    exit(1);
                }
                for(int j = 0; j < coefficient[i].size(); j++) {
                    if(exp[i][j] > 1){
                        for(int k = 2; k <= exp[i][j]; k++) {
                            if(k == 2) {
                                last_idx = cipherText_r1cs_mul(pb, index, coefficient[i][j]*2, coefficient[i][j]*2);
                                // pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[coefficient[i][j]], vars[coefficient[i][j]], vars[index]));
                                // index++;
                                if(exp[i][j] == 2) {
                                    temp_val.push_back(last_idx);
                                    // temp_val.push_back(index - 1);
                                }
                                cout << "k: " << "\t";
                            }
                            else if(k != exp[i][j]){
                                last_idx = cipherText_r1cs_mul(pb, index, coefficient[i][j]*2, last_idx);
                                // pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[coefficient[i][j]], vars[index - 1], vars[index]));
                                // index++;
                            }
                            else {
                                last_idx = cipherText_r1cs_mul(pb, index, coefficient[i][j]*2, last_idx);
                                temp_val.push_back(last_idx);
                                // temp_val.push_back(index);
                                // pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[coefficient[i][j]], vars[index - 1], vars[index]));
                                // index++;
                            }
                        }
                    }
                    else{
                        temp_val.push_back(coefficient[i][j]*2);
                        // temp_val.push_back(coefficient[i][j]);
                    }
                }
                var_for_mul.push_back(temp_val);
            }
            // cout << endl;
            // cout << "debug: " << endl;
            // cout << "var_for_mul.size(): " << var_for_mul.size() << endl;
            // for(int i = 0 ; i < var_for_mul.size(); i++) {
            //     cout << var_for_mul[i].size() << "\t";
            // }
            // cout << endl;

            for(int i = 0; i < coefficient.size(); i++) {
                temp_val.clear();
                //如果是单变量d,即j只能为0
                if(var_for_mul[i].size() == 1){
                    // cout << i << ":no j" << "\t"
                    var_for_add.push_back(var_for_mul[i][0]);
                }
                else {
                    for(int j = 1; j < var_for_mul[i].size(); j++) {
                        cout << i << ":" << j << "\t";
                        if (j == 1 && var_for_mul[i].size() == 2) {
                            last_idx = cipherText_r1cs_mul(pb, index, var_for_mul[i][j - 1], var_for_mul[i][j]);
                            var_for_add.push_back(last_idx);
                            // pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[var_for_mul[i][j - 1]], vars[var_for_mul[i][j]], vars[index]));
                            // index++;
                            // var_for_add.push_back(index - 1);
                        }
                        else if (j == 1 && var_for_mul[i].size() > 2) {
                            last_idx = cipherText_r1cs_mul(pb, index, var_for_mul[i][j - 1], var_for_mul[i][j]);
                            // pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[var_for_mul[i][j - 1]], vars[var_for_mul[i][j]], vars[index]));
                            // index++;
                        }
                        else if(j != var_for_mul[i].size() - 1){
                            last_idx = cipherText_r1cs_mul(pb, index, last_idx, var_for_mul[i][j]);
                            // pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[index - 1], vars[var_for_mul[i][j]], vars[index]));
                            // index++;
                        }
                        else {
                            last_idx = cipherText_r1cs_mul(pb, index, last_idx, var_for_mul[i][j]);
                            var_for_add.push_back(last_idx);
                            // pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[index - 1], vars[var_for_mul[i][j]], vars[index]));
                            // index++;
                            // var_for_add.push_back(index - 1);
                        }
                    }
                }
            }
            cout << endl;

            if(no_aj){
                var_a = var_for_add;
            }
            else{
                for(int i=0;i<num_avar;i++) {
                    last_idx = cipherText_r1cs_mul(pb, index, var_for_add[i], i, true);
                    var_a.push_back(last_idx);
                    // pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[var_for_add[i]], aR[i], avar[i]));
                }
            }

            if(var_for_add.size() == 0) {
                std::cout << "var_for_add.size = 0" << std::endl;
            }else if(var_for_add.size() == 1) {
                std::cout << "var_for_add.size = 1" << std::endl;
            }else {
                for(int i = 1; i < var_for_add.size(); i++) {
                    if(i == 1 && var_for_add.size() == 2){
                        last_idx = cipherText_r1cs_add(pb, index, var_a[i - 1], var_a[i], index_for_output);
                        // pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(avar[i - 1] + avar[i], constant_one, vars[index_for_output]));
                    }else if(i == 1 && var_for_add.size() > 2) {
                        last_idx = cipherText_r1cs_add(pb, index, var_a[i - 1], var_a[i]);
                        // pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(avar[i - 1] + avar[i], constant_one, vars[index]));
                        // index++;
                    }else if(i != var_for_add.size() - 1){
                        last_idx = cipherText_r1cs_add(pb, index, last_idx, var_a[i]);
                        // pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[index - 1] + avar[i], constant_one, vars[index]));
                        // index++;
                    }else {
                        last_idx = cipherText_r1cs_add(pb, index, last_idx, var_a[i], index_for_output);
                        // pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[index - 1] + avar[i], constant_one, vars[index_for_output]));
                    }
                }
            }
        }

        // int final_var_num = last_idx;
        // cout << "exit : " << __FUNCTION__  << endl;
    }

    void generate_r1cs_witness(ringsnark::protoboard<R>& pb) {
        // 为public input和private witness设置值，x=3，out=35，其他的按照逻辑关系求解即可
        // cout << "entering into: " << __FUNCTION__  << endl;
        // cout<<"no_aj:"<<no_aj<<endl;
        // cout<<"polys size:"<<polys.size()<<endl;
        values.resize(polys.size());
        for(int i = 0; i < polys.size(); i++) {
            values[i] = ringsnark::seal::RingElem(polys[i]);
        }

        // vector<ringsnark::seal::RingElem> avalue(num_avar);
        // for(int i = 0; i < num_avar; i++) {
        //     avalue[i] = ringsnark::seal::RingElem(apoly[i]);
        // }

        vector<ringsnark::seal::RingElem> relin_value(2);
        relin_value[0] = ringsnark::seal::RingElem(relin_poly[0]);
        relin_value[1] = ringsnark::seal::RingElem(relin_poly[1]);

        //输入的值
        //计算中间结果d
        // cout<<"vars size:"<<vars.size()<<endl;
        for(int i = 0; i < polys.size(); i++) {
            pb.val(vars[i]) = values[i];
        }

        // for(int i = 0; i < num_avar; i++) {
        //     pb.val(avar[i]) = avalue[i];
        // }

        pb.val(relinR[0]) = relin_value[0];
        pb.val(relinR[1]) = relin_value[1];

        R rONE = R::one();
        pb.val(constant_one) = rONE;
        /*
        pb.val(out) = 35;

        pb.val(x) = 3;
        pb.val(sym_1) = 9;
        pb.val(y) = 27;
        pb.val(sym_2) = 30;
        */

        if(!no_aj){
            for(int i=0;i<num_avar;i++){
                pb.val(aR[i]) = ringsnark::seal::RingElem(poly_as[i]);
            }
        }
       

        // cout << "exit: " << __FUNCTION__  << endl;
    }

    void copy_polys_from_A(vector<unsigned long long> &a, SEALContext context){
        vector<vector<uint64_t>> tmpa;
        vector<uint64_t> tmp;
        for(int i=0;i<num_var;i++){
            tmp.clear();
            for(int j=0;j<Inner_N;j++){
                tmp.push_back(a[i*Inner_N + j]);
            }
            tmpa.push_back(tmp);
        }

        vector<vector<uint64_t>> relin_vector;
        for(int i=0;i<2;i++){
            tmp.clear();
            for(int j=0;j<Inner_N;j++){
                tmp.push_back(a[num_var*Inner_N + i*Inner_N + j]);
            }
            relin_vector.push_back(tmp);
        }

        //用于存储输入输出以及中间变量的值
        // cout<<"seal_poly_debug1"<<endl;
        polys = vector<::polytools::SealPoly>(num_var, polytools::SealPoly(context));
        // cout<<"seal_poly_debug1"<<endl;

        for(int i = 0; i < tmpa.size(); i++) {
            polys[i] = polytools::SealPoly(context, tmpa[i], &(context.first_parms_id()));
        }

        // cout<<"seal_poly_debug1";

        relin_poly = vector<::polytools::SealPoly>(2, polytools::SealPoly(context));
        relin_poly[0] = polytools::SealPoly(context, relin_vector[0], &(context.first_parms_id()));
        relin_poly[1] = polytools::SealPoly(context, relin_vector[1], &(context.first_parms_id()));

    }


private:
    size_t num_input; //输入变量的数量
    size_t num_var;   //全部变量的数量
    vector<vector<size_t>> coefficient;
    vector<vector<size_t>> exp;
    ringsnark::pb_variable_array<R> vars;
    ringsnark::pb_variable<R> constant_one = ringsnark::pb_variable<R>();
    vector<::polytools::SealPoly> polys;
    vector<ringsnark::seal::RingElem> values;
    vector<double> aj0;
    vector<Plaintext> a_plain;
    vector<ringsnark::pb_variable<R>> aR;
    size_t num_avar;
    vector<::polytools::SealPoly> poly_as;
    vector<ringsnark::pb_variable<R>> relinR;
    vector<::polytools::SealPoly> relin_poly;
    vector<double> factorv;
    bool factorflag;
    bool no_aj;
    size_t ex_unfold;


    void dispvector2(vector<vector<size_t>> c){
        for(int i=0;i<c.size();i++){
            for(int j=0;j<c[i].size();j++){
                cout<<c[i][j]<<" ";
            }
            cout<<endl;
        }
    }

    double factorial(size_t x){
        double y = 1;
        if(factorflag){
            y = factorv[x];
        }
        else{
            factorv.push_back(y);
            for(size_t i=1;i<=x;i++){
                y *= i;
                factorv.push_back(y);
            }
            factorflag = true;
        }
        return y;
    }

    void ex_to_x(vector<vector<size_t>> &aj,size_t &numInput){
        size_t terms = aj[1].size();
        for(int i=0;i<terms;i++){
            size_t x = aj[1][i];
            if(x==UNSIZEMAX){
                continue;
            }

            bool x_exit = false;
            size_t j;
            for(j=0;j<coefficient[i].size();j++){
                if(coefficient[i][j]==x){
                    x_exit = true;
                    break;
                }
            }

            for(size_t k=1; k<=ex_unfold; k++){
                vector<size_t> termf = coefficient[i];
                vector<size_t> terme = exp[i];
                double a0 = aj0[i];

                if(x_exit){
                    terme[j] += k;
                }
                else{
                    termf.push_back(x);
                    terme.push_back(k);
                }
                a0 /= factorial(k);
                
                coefficient.push_back(termf);
                exp.push_back(terme);
                aj0.push_back(a0);

                numInput += termf.size();
            }
        }
        cout<<"coefficient:"<<endl;
        dispvector2(coefficient);
        cout<<"exp:"<<endl;
        dispvector2(exp);
        cout<<"aj0"<<endl;
        for(int i=0;i<aj0.size();i++){
            cout<<aj0[i]<<" ";
        }
        cout<<endl;
    }

    size_t cipherText_r1cs_mul(ringsnark::protoboard<R>& pb, size_t &index, size_t ciher_idx1, size_t ciher_idx2, bool use_plain=false, size_t idx_output=UNSIZEMAX){
        size_t result_idx;

        if(use_plain){
            if(ciher_idx2==UNSIZEMAX){
                if(idx_output!=UNSIZEMAX){
                    pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[ciher_idx1], constant_one, vars[idx_output]));
                    pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[ciher_idx1 + 1], constant_one, vars[idx_output + 1]));
                    return idx_output;
                }
                pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[ciher_idx1], constant_one, vars[index]));
                pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[ciher_idx1+ 1], constant_one, vars[index+ 1]));
            }
            else{
                if(idx_output!=UNSIZEMAX){
                    pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[ciher_idx1], aR[ciher_idx2], vars[idx_output]));
                    pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[ciher_idx1 + 1], aR[ciher_idx2], vars[idx_output + 1]));
                    return idx_output;
                }
                pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[ciher_idx1], aR[ciher_idx2], vars[index]));
                pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[ciher_idx1 + 1], aR[ciher_idx2], vars[index + 1]));
            }
            result_idx = index;
            index += 2;
            return result_idx;
        }

        pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[ciher_idx1], vars[ciher_idx2], vars[index]));
        pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[ciher_idx1 + 1], vars[ciher_idx2], vars[index + 1]));
        pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[ciher_idx1], vars[ciher_idx2 + 1], vars[index + 2]));
        pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[ciher_idx1 + 1], vars[ciher_idx2 + 1], vars[index + 3]));
        pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[index + 1] + vars[index + 2], constant_one, vars[index + 4]));
        pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(relinR[0] , vars[index + 3], vars[index + 5]));
        pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(relinR[1] , vars[index + 3], vars[index + 6]));
        
        // cout << "r1cs_mul_debug1" << endl;

        if(idx_output!=UNSIZEMAX){
            pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[index] + vars[index + 5], constant_one, vars[idx_output]));
            pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[index + 4] + vars[index + 6], constant_one, vars[idx_output + 1]));
            index += 7;
            return idx_output;
        }

        pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[index] + vars[index + 5], constant_one, vars[index + 7]));
        pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[index + 4] + vars[index + 6], constant_one, vars[index + 8]));
        
        result_idx = index + 7;
        index += 9;
        return result_idx;
    }

    size_t cipherText_r1cs_add(ringsnark::protoboard<R>& pb, size_t &index, size_t ciher_idx1, size_t ciher_idx2, size_t idx_output=UNSIZEMAX){
        size_t result_idx;

        if(idx_output!=UNSIZEMAX){
            pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[ciher_idx1] + vars[ciher_idx2], constant_one, vars[idx_output]));
            pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[ciher_idx1 + 1] + vars[ciher_idx2 + 1], constant_one, vars[idx_output + 1]));
            return idx_output;
        }
        
        pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[ciher_idx1] + vars[ciher_idx2], constant_one, vars[index]));
        pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[ciher_idx1 + 1] + vars[ciher_idx2 + 1], constant_one, vars[index + 1]));
        
        result_idx = index;
        index += 2;
        return result_idx;
    }

    size_t cipherText_poly_mul(polytools::SealPoly &poly, size_t &index, size_t ciher_idx1, size_t ciher_idx2, bool use_plain=false, size_t idx_output=UNSIZEMAX){
        size_t result_idx;

        if(use_plain){
            if(ciher_idx2==UNSIZEMAX){
                if(idx_output!=UNSIZEMAX){
                    poly = polys[ciher_idx1];
                    polys[idx_output] = poly;

                    poly = polys[ciher_idx1 + 1];
                    polys[idx_output + 1] = poly;

                    return idx_output;
                }
                
                poly = polys[ciher_idx1];
                polys[index] = poly;

                poly = polys[ciher_idx1 + 1];
                polys[index + 1] = poly;
            }
            else{
                if(idx_output!=UNSIZEMAX){
                    poly = polys[ciher_idx1];
                    poly.multiply_inplace(poly_as[ciher_idx2]);
                    polys[idx_output] = poly;

                    poly = polys[ciher_idx1 + 1];
                    poly.multiply_inplace(poly_as[ciher_idx2]);
                    polys[idx_output + 1] = poly;

                    return idx_output;
                }

                poly = polys[ciher_idx1];
                poly.multiply_inplace(poly_as[ciher_idx2]);
                polys[index] = poly;

                poly = polys[ciher_idx1 + 1];
                poly.multiply_inplace(poly_as[ciher_idx2]);
                polys[index + 1] = poly;
            }
            result_idx = index;
            index += 2;
            return result_idx;
        }

        poly = polys[ciher_idx1];
        poly.multiply_inplace(polys[ciher_idx2]);
        polys[index] = poly;

        poly = polys[ciher_idx1];
        poly.multiply_inplace(polys[ciher_idx2 + 1]);
        polys[index + 1] = poly;

        poly = polys[ciher_idx1 + 1];
        poly.multiply_inplace(polys[ciher_idx2]);
        polys[index + 2] = poly;

        poly = polys[ciher_idx1 + 1];
        poly.multiply_inplace(polys[ciher_idx2 + 1]);
        polys[index + 3] = poly;
        
        poly = polys[index + 1];
        poly.add_inplace(polys[index + 2]);
        polys[index + 4] = poly;

        poly = relin_poly[0];
        poly.multiply_inplace(polys[index + 3]);
        polys[index + 5] = poly;

        poly = relin_poly[1];
        poly.multiply_inplace(polys[index + 3]);
        polys[index + 6] = poly;

        if(idx_output!=UNSIZEMAX){
            poly = polys[index];
            poly.add_inplace(polys[index + 5]);
            polys[idx_output] = poly;

            poly = polys[index + 4];
            poly.add_inplace(polys[index + 6]);
            polys[idx_output + 1] = poly;

            index += 7;
            return idx_output;
        }

        poly = polys[index];
        poly.add_inplace(polys[index + 5]);
        polys[index + 7] = poly;

        poly = polys[index + 4];
        poly.add_inplace(polys[index + 6]);
        polys[index + 8] = poly;

        result_idx = index + 7;
        index += 9;
        return result_idx;
    }

    size_t cipherText_poly_add(polytools::SealPoly &poly, size_t &index, size_t ciher_idx1, size_t ciher_idx2, size_t idx_output=UNSIZEMAX){
        size_t result_idx;

        if(idx_output!=UNSIZEMAX){
            poly = polys[ciher_idx1];
            poly.add_inplace(polys[ciher_idx2]);
            polys[idx_output] = poly;

            poly = polys[ciher_idx1 + 1];
            poly.add_inplace(polys[ciher_idx2 + 1]);
            polys[idx_output + 1] = poly;

            return idx_output;
        }

        poly = polys[ciher_idx1];
        poly.add_inplace(polys[ciher_idx2]);
        polys[index] = poly;

        poly = polys[ciher_idx1 + 1];
        poly.add_inplace(polys[ciher_idx2 + 1]);
        polys[index + 1] = poly;
    
        result_idx = index;
        index += 2;
        return result_idx;
    }

};

size_t getCipherNum(string comp){
    size_t cnu = std::stoi(comp) >> 13;
    if(cnu<2){
        cnu = 2;
    }
    return cnu;
}

class CircuitE {
public:
    CircuitE(ringsnark::protoboard<R> &pb, vector<vector<size_t>> coeff, vector<vector<size_t>> ex, vector<vector<size_t>> aj, size_t numInput, size_t ee) {
        // 变量与电路板直接建立关系，相当于把组件插入到电路板上，allocate方法第二个参数类似于注释，方便查看日志
        //计算一共有多少变量
        // cout << "entering into: " << __FUNCTION__  << endl;
        coefficient = coeff;
        exp = ex;
        ex_unfold = ee;

        for(int i=0;i<aj[0].size();i++){
            aj0.push_back(1.0*aj[0][i]);
        }

        if(aj.size()>1){  //exist e^x
            factorflag = false;
            factorial(ex_unfold);
            for(int i=0; i<EI; i++){
                ex_to_x(aj, numInput);

                vector<size_t> aj1;
                for(int j=0; j<aj0.size();j++){
                    aj1.push_back(1);
                }
                aj.pop_back();
                aj.push_back(aj1);
            }
        }

        num_input = numInput; // 只包括输入，不包括输出
        size_t num = 0;
        if(coefficient.size() != exp.size()) {
            cout << "error: the size of coefficient is not equal to exp" << endl;
            return;
        }
        for(int i = 0; i < exp.size(); i++) {
            for(int j = 0; j < exp[i].size(); j++) {
                if(exp[i][j] > 1) {
                    num += exp[i][j] - 1;
                }
            }
        }
        for(int i = 0; i < coefficient.size(); i++) {
            num += coefficient[i].size() - 1;
        }
        num += coefficient.size() - 1;
        //num包含输出
        // cout << "num: " << num << endl;
        num_var = num_input + num;
        vars = ringsnark::pb_variable_array<R>(num_var, ringsnark::pb_variable<R>());
        vars.allocate(pb, num_var , "vars");

        num_avar = coefficient.size();
        avar= ringsnark::pb_variable_array<R>(num_avar, ringsnark::pb_variable<R>());
        avar.allocate(pb, num_avar , "avar");

        pb.set_input_sizes(num_input + 1); 

        constant_one.allocate(pb, "one");
        // cout << "exit: " << __FUNCTION__  << endl;
    }

    void dispvector2(vector<vector<size_t>> c){
        for(int i=0;i<c.size();i++){
            for(int j=0;j<c[i].size();j++){
                cout<<c[i][j]<<" ";
            }
            cout<<endl;
        }
    }

    double factorial(size_t x){
        double y = 1;
        if(factorflag){
            y = factorv[x];
        }
        else{
            factorv.push_back(y);
            for(size_t i=1;i<=x;i++){
                y *= i;
                factorv.push_back(y);
            }
            factorflag = true;
        }
        return y;
    }

    void ex_to_x(vector<vector<size_t>> &aj,size_t &numInput){
        size_t terms = aj[1].size();
        for(int i=0;i<terms;i++){
            size_t x = aj[1][i];
            if(x==UNSIZEMAX){
                continue;
            }

            bool x_exit = false;
            size_t j;
            for(j=0;j<coefficient[i].size();j++){
                if(coefficient[i][j]==x){
                    x_exit = true;
                    break;
                }
            }

            for(size_t k=1;k<=ex_unfold;k++){
                vector<size_t> termf = coefficient[i];
                vector<size_t> terme = exp[i];
                double a0 = aj0[i];

                if(x_exit){
                    terme[j] += k;
                }
                else{
                    termf.push_back(x);
                    terme.push_back(k);
                }
                a0 /= factorial(k);
                
                coefficient.push_back(termf);
                exp.push_back(terme);
                aj0.push_back(a0);

                numInput += termf.size();
            }
        }
    }

    void aj_to_aplain(SEALContext context, double scale, ringsnark::protoboard<R>& pb){
        
        CKKSEncoder encoder(context);
        
        Plaintext apt;
        for(int i=0;i<aj0.size();i++){
            encoder.encode(aj0[i], scale, apt);
            a_plain.push_back(apt);

            ringsnark::pb_variable<R> constant_tmp = ringsnark::pb_variable<R>();
            aR.push_back(constant_tmp);
            aR[i].allocate(pb, "constant_" + std::to_string(i));
            // pb.val(aR[i]) = ringsnark::seal::RingElem(aj0[i]);
        }
    }

    void generate_r1cs_constraints(ringsnark::protoboard<R>& pb)  {
        // 组件以及插入到了电路板上，下面需要按照约束链接几个组件
        // 注意，此处r1cs_constraint方法只涉及乘法，如果要计算加法可以把sym_2 = y + x看成是sym_2 = (y + x) * 1，符合电路到QAP的变换知识
        // x*x = sym_1
        // cout << "entering into: " << __FUNCTION__  << endl;
        size_t index_for_output = num_input;
        size_t index = num_input + 1;
        vector<vector<size_t>> var_for_mul;
        vector<size_t> var_for_add;
        //ji
        vector<size_t> temp_val;
        // cout << "debug: " << endl;
        // cout << "coefficient.size(): " << coefficient.size() << endl;
        //如果没有加法
        if(coefficient.size() == 1) {
            //如果没有乘法
            if(coefficient[0].size() == 1) {
                if(exp[0][0] == 1) {
                    pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[coefficient[0][0]], constant_one, avar[0]));
                    pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(avar[0], aR[0], vars[index_for_output]));
                }else if(exp[0][0] == 2) {
                    pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[coefficient[0][0]], vars[coefficient[0][0]], avar[0]));
                    pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(avar[0], aR[0], vars[index_for_output]));
                }else {
                    for(int i = 2; i <= exp[0][0]; i++) {
                        if(i == 2) {
                            pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[coefficient[0][0]], vars[coefficient[0][0]], vars[index]));
                            index++;
                        }else if(i != exp[0][0]) {
                            pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[coefficient[0][0]], vars[index - 1], vars[index]));
                            index++;
                        }else {
                            pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[coefficient[0][0]], vars[index - 1], avar[0]));
                            pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(avar[0], aR[0], vars[index_for_output]));
                        }
                    }

                }
            }
                //如果有乘法
            else {
                for(int i = 0; i < coefficient[0].size(); i++) {
                    //进行幂运算
                    if (exp[0][i] == 1) {
                        temp_val.push_back(coefficient[0][i]);
                    } else if (exp[0][i] == 2) {
                        pb.add_r1cs_constraint(
                                ringsnark::r1cs_constraint<R>(vars[coefficient[0][i]], vars[coefficient[0][i]],
                                                              vars[index]));
                        index++;
                        temp_val.push_back(index - 1);
                    } else {
                        for (int j = 2; j <= exp[0][i]; j++) {
                            if (j == 2) {
                                pb.add_r1cs_constraint(
                                        ringsnark::r1cs_constraint<R>(vars[coefficient[0][i]], vars[coefficient[0][i]],
                                                                      vars[index]));
                                index++;
                            } else if (j != exp[0][i]) {
                                pb.add_r1cs_constraint(
                                        ringsnark::r1cs_constraint<R>(vars[coefficient[0][i]], vars[index - 1],
                                                                      vars[index]));
                                index++;
                            } else {
                                pb.add_r1cs_constraint(
                                        ringsnark::r1cs_constraint<R>(vars[coefficient[0][i]], vars[index - 1],
                                                                      vars[index]));
                                index++;
                                temp_val.push_back(index - 1);
                            }
                        }
                    }
                }
                //进行乘法运算
                if(temp_val.size() == 2) {
                    pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[temp_val[0]], vars[temp_val[1]], avar[0]));
                    pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(avar[0], aR[0], vars[index_for_output]));
                }else {
                    for(int j = 1; j < temp_val.size(); j++) {
                        if(j == 1) {
                            pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[temp_val[j - 1]], vars[temp_val[j]], vars[index]));
                            index++;
                        }else if(j != temp_val.size() - 1) {
                            pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[temp_val[j]], vars[index - 1], vars[index]));
                            index++;
                        }else {
                            pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[temp_val[j]], vars[index - 1], avar[0]));
                            pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(avar[0], aR[0], vars[index_for_output]));
                        }
                    }
                }
            }
        }
            //如果有加法
        else {
            for(int i = 0; i < coefficient.size(); i++) {
                temp_val.clear();
                if(exp[i].size() != coefficient[i].size()) {
                    cout << "exp" << i << "is not equal to coe" << endl;
                    exit(1);
                }
                for(int j = 0; j < coefficient[i].size(); j++) {
                    if(exp[i][j] > 1){
                        for(int k = 2; k <= exp[i][j]; k++) {
                            if(k == 2) {
                                pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[coefficient[i][j]], vars[coefficient[i][j]], vars[index]));
                                index++;
                                if(exp[i][j] == 2) {
                                    temp_val.push_back(index - 1);
                                }
                                // cout << "k: " << endl;
                            }
                            else if(k != exp[i][j]){
                                pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[coefficient[i][j]], vars[index - 1], vars[index]));
                                index++;
                            }
                            else {
                                temp_val.push_back(index);
                                pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[coefficient[i][j]], vars[index - 1], vars[index]));
                                index++;
                            }
                        }
                    }
                    else{
                        temp_val.push_back(coefficient[i][j]);
                    }
                }
                var_for_mul.push_back(temp_val);
            }
            // cout << "debug: " << endl;
            // cout << "var_for_mul.size(): " << var_for_mul.size() << endl;
            // for(int i = 0 ; i < var_for_mul.size(); i++) {
            //     cout << var_for_mul[i].size() << endl;
            // }

            for(int i = 0; i < coefficient.size(); i++) {
                temp_val.clear();
                //如果是单变量d,即j只能为0
                if(var_for_mul[i].size() == 1){
                    // cout << i << ":no j" << endl;
                    var_for_add.push_back(var_for_mul[i][0]);
                }
                else {
                    for(int j = 1; j < var_for_mul[i].size(); j++) {
                        // cout << i << ":" << j << endl;
                        if (j == 1 && var_for_mul[i].size() == 2) {
                            pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[var_for_mul[i][j - 1]], vars[var_for_mul[i][j]], vars[index]));
                            index++;
                            var_for_add.push_back(index - 1);
                        }
                        else if (j == 1 && var_for_mul[i].size() > 2) {
                            pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[var_for_mul[i][j - 1]], vars[var_for_mul[i][j]], vars[index]));
                            index++;
                        }
                        else if(j != var_for_mul[i].size() - 1){
                            pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[index - 1], vars[var_for_mul[i][j]], vars[index]));
                            index++;
                        }
                        else {
                            pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[index - 1], vars[var_for_mul[i][j]], vars[index]));
                            index++;
                            var_for_add.push_back(index - 1);
                        }
                    }
                }
            }

            for(int i=0;i<num_avar;i++) {
                pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[var_for_add[i]], aR[i], avar[i]));
            }

            if(var_for_add.size() == 0) {
                std::cout << "var_for_add.size = 0" << std::endl;
            }else if(var_for_add.size() == 1) {
                std::cout << "var_for_add.size = 1" << std::endl;
            }else {
                for(int i = 1; i < var_for_add.size(); i++) {
                    if(i == 1 && var_for_add.size() == 2){
                        pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(avar[i - 1] + avar[i], constant_one, vars[index_for_output]));
                        cout << "after_Add " << endl;
                    }else if(i == 1 && var_for_add.size() > 2) {
                        pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(avar[i - 1] + avar[i], constant_one, vars[index]));
                        index++;
                    }else if(i != var_for_add.size() - 1){
                        pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[index - 1] + avar[i], constant_one, vars[index]));
                        index++;
                    }else {
                        pb.add_r1cs_constraint(ringsnark::r1cs_constraint<R>(vars[index - 1] + avar[i], constant_one, vars[index_for_output]));
                    }
                }
            }
        }

        // int final_var_num = index;
        // cout << "exit : " << __FUNCTION__  << endl;
    }


    
    void compute_seal_poly(SEALContext context, vector<Ciphertext> input_ctxt){
        // cout << "entering into: " << __FUNCTION__  << endl;
        vector<vector<size_t>> var_for_mul;
        vector<size_t> var_for_add;
        vector<size_t> temp_val;
        //用于存储输入输出以及中间变量的值
        polys = vector<::polytools::SealPoly>(num_var, polytools::SealPoly(context));
        size_t index = 0;
       
        for(int i = 0; i < input_ctxt.size(); i++) {
            polys[index] = polytools::SealPoly(context, input_ctxt[i], 0);
            index++;
            polys[index] = polytools::SealPoly(context, input_ctxt[i], 1);
            index++;
        }

        apoly = vector<::polytools::SealPoly>(num_avar, polytools::SealPoly(context));
        poly_as = vector<::polytools::SealPoly>(num_avar, polytools::SealPoly(context));
        for(int i=0; i<num_avar; i++) {
            poly_as[i] = polytools::SealPoly(context, a_plain[i]);
        }

        auto poly3=polytools::SealPoly(context, input_ctxt[0], 0);
        while(index<num_input){
            polys[index] = poly3;
            index++;
        }

        size_t index_for_output = index;
        index++;
        auto poly = polytools::SealPoly(context);

        //如果没有加法
        if(coefficient.size() == 1) {
            //如果没有乘法
            if(coefficient[0].size() == 1) {
                if(exp[0][0] == 1) {
                    poly = polys[coefficient[0][0]];
                    apoly[0] = poly;
                    poly.multiply_inplace(poly_as[0]);
                    polys[index_for_output] = poly;
                }else if(exp[0][0] == 2) {
                    poly = polys[coefficient[0][0]];
                    poly.multiply_inplace(poly);
                    apoly[0] = poly;
                    poly.multiply_inplace(poly_as[0]);
                    polys[index_for_output] = poly;
                }else {
                    for(int i = 2; i <= exp[0][0]; i++) {
                        if(i == 2) {
                            poly = polys[coefficient[0][0]];
                            poly.multiply_inplace(poly);
                            polys[index] = poly;
                            index++;
                        }else if(i != exp[0][0]) {
                            poly = polys[coefficient[0][0]];
                            poly.multiply_inplace(polys[index - 1]);
                            polys[index] = poly;
                            index++;
                        }else {
                            poly = polys[coefficient[0][0]];
                            poly.multiply_inplace(polys[index - 1]);
                            apoly[0] = poly;
                            poly.multiply_inplace(poly_as[0]);
                            polys[index_for_output] = poly;
                        }
                    }
                }
            }
                //如果有乘法
            else {
                for(int i = 0; i < coefficient[0].size(); i++) {
                    //进行幂运算
                    if (exp[0][i] == 1) {
                        temp_val.push_back(coefficient[0][i]);
                    } else if (exp[0][i] == 2) {
                        poly = polys[coefficient[0][i]];
                        poly.multiply_inplace(poly);
                        polys[index] = poly;
                        index++;
                        temp_val.push_back(index - 1);
                    } else {
                        for (int j = 2; j <= exp[0][i]; j++) {
                            if (j == 2) {
                                poly = polys[coefficient[0][i]];
                                poly.multiply_inplace(poly);
                                polys[index] = poly;
                                index++;
                            } else if (j != exp[0][i]) {
                                poly = polys[coefficient[0][i]];
                                poly.multiply_inplace(polys[index - 1]);
                                polys[index] = poly;
                                index++;
                            } else {
                                poly = polys[coefficient[0][i]];
                                poly.multiply_inplace(polys[index - 1]);
                                polys[index] = poly;
                                index++;
                                temp_val.push_back(index - 1);
                            }
                        }
                    }
                }
                //进行乘法运算
                if(temp_val.size() == 2) {
                    poly = polys[temp_val[0]];
                    poly.multiply_inplace(polys[temp_val[1]]);
                    apoly[0] = poly;
                    poly.multiply_inplace(poly_as[0]);
                    polys[index_for_output] = poly;
                }else {
                    for(int j = 1; j < temp_val.size(); j++) {
                        if(j == 1) {
                            poly = polys[temp_val[j]];
                            poly.multiply_inplace(polys[temp_val[j - 1]]);
                            polys[index] = poly;
                            index++;
                        }else if(j != temp_val.size() - 1) {
                            poly = polys[temp_val[j]];
                            poly.multiply_inplace(polys[index - 1]);
                            polys[index] = poly;
                            index++;
                        }else {
                            poly = polys[temp_val[j]];
                            poly.multiply_inplace(polys[index - 1]);
                            apoly[0] = poly;
                            poly.multiply_inplace(poly_as[0]);
                            polys[index_for_output] = poly;
                        }
                    }
                }
            }
        }
            //如果有加法
        else {
            for(int i = 0; i < coefficient.size(); i++) {
                temp_val.clear();
                for(int j = 0; j < coefficient[i].size(); j++) {
                    if(exp[i][j] > 1){
                        for(int k = 2; k <= exp[i][j]; k++) {
                            if(k == 2) {
                                poly = polys[coefficient[i][j]];
                                poly.multiply_inplace(poly);
                                polys[index] = poly;
                                index++;
                                if(exp[i][j] == 2)
                                    temp_val.push_back(index - 1);
                            }
                            else if(k != exp[i][j]){
                                poly =  polys[index - 1];
                                poly.multiply_inplace(polys[coefficient[i][j]]);
                                polys[index] = poly;
                                index++;
                            }
                            else {
                                poly =  polys[index - 1];
                                poly.multiply_inplace(polys[coefficient[i][j]]);
                                polys[index] = poly;
                                index++;
                                temp_val.push_back(index - 1);
                            }
                        }
                    }
                    else{
                        temp_val.push_back(coefficient[i][j]);
                    }
                }
                var_for_mul.push_back(temp_val);
            }

            for(int i = 0; i < coefficient.size(); i++) {

                if(var_for_mul[i].size() == 0) {
                    cout << i << "var_for_mul is 0" << endl;
                    continue;
                }
                if(var_for_mul[i].size() == 1) {
                    var_for_add.push_back(var_for_mul[i][0]);
                    continue;
                }
                for(int j = 1; j < var_for_mul[i].size(); j++) {
                    if(j == 1 && var_for_mul[i].size() == 2) {
                        poly = polys[var_for_mul[i][j]];
                        poly.multiply_inplace(polys[var_for_mul[i][j - 1]]);
                        polys[index] = poly;
                        index++;
                        var_for_add.push_back(index - 1);
                    }else if(j == 1 && var_for_mul[i].size() > 2){
                        poly = polys[var_for_mul[i][j]];
                        poly.multiply_inplace(polys[var_for_mul[i][j - 1]]);
                        polys[index] = poly;
                        index++;
                    }else if(j != var_for_mul[i].size() - 1){
                        poly = polys[index - 1];
                        poly.multiply_inplace(polys[var_for_mul[i][j]]);
                        polys[index] = poly;
                        index++;
                    }
                    else if(j == var_for_mul[i].size() - 1) {
                        poly = polys[index - 1];
                        poly.multiply_inplace(polys[var_for_mul[i][j]]);
                        polys[index] = poly;
                        index++;
                        var_for_add.push_back(index - 1);
                    }
                }
            }

            for(int i=0; i<num_avar;i++){
                poly = polys[var_for_add[i]];
                poly.multiply_inplace(poly_as[i]);
                apoly[i] = poly;
            }

            if(var_for_add.size() == 0) {
                std::cout << "var_for_add.size = 0" << std::endl;
            }else if(var_for_add.size() == 1) {
                std::cout << "var_for_add.size = 1" << std::endl;
            }else {
                for(int i = 1; i < var_for_add.size(); i++) {
                    if(i == 1 && var_for_add.size() == 2){
                        poly = apoly[i];
                        poly.add_inplace(apoly[i - 1]);
                        polys[index_for_output] = poly;
                    }else if(i == 1 && var_for_add.size() > 2){
                        poly = apoly[i];
                        poly.add_inplace(apoly[i - 1]);
                        polys[index] = poly;
                        index++;
                    }else if(i != var_for_add.size() - 1){
                        poly = apoly[i];
                        poly.add_inplace(polys[index - 1]);
                        polys[index] = poly;
                        index++;
                    }else {
                        poly = apoly[i];
                        poly.add_inplace(polys[index - 1]);
                        polys[index_for_output] = poly;
                    }
                }
            }
        }

        if(e_des){
            polys[index_for_output] = polys[0];
        }

        // int final_var_num = index;
        // cout << "exit: " << __FUNCTION__  << endl;
    }
    
    void compute_seal_poly_map(SEALContext context, SEALContext context_encode, vector<Ciphertext> input_ctxt){
        // cout << "entering into: " << __FUNCTION__  << endl;
        vector<vector<size_t>> var_for_mul;
        vector<size_t> var_for_add;
        vector<size_t> temp_val;
        //用于存储输入输出以及中间变量的值
        cout<<"seal_poly_debug1"<<endl;
        polys = vector<::polytools::SealPoly>(num_var, polytools::SealPoly(context_encode));
        cout<<"seal_poly_debug1"<<endl;
        size_t index = 0;
        auto modulus=context_encode.first_context_data()->parms().coeff_modulus();
        vector<uint64_t> modulus_encode(modulus.size());
        for(size_t i=0;i<modulus.size();i++){
            modulus_encode[i]=modulus[i].value();
        }
        for(int i = 0; i < input_ctxt.size(); i++) {
            auto poly1=polytools::SealPoly(context, input_ctxt[i], 0);
            auto polylist=poly1.get_coeff_list(modulus_encode);
            polys[index] = polytools::SealPoly(context_encode, polylist, &(context_encode.first_parms_id()));
            index++;
            poly1=polytools::SealPoly(context, input_ctxt[i], 1);
            polylist=poly1.get_coeff_list(modulus_encode);
            polys[index] = polytools::SealPoly(context_encode, polylist, &(context_encode.first_parms_id()));
            index++;
        }
        cout<<"seal_poly_debug1";

        apoly = vector<::polytools::SealPoly>(num_avar, polytools::SealPoly(context_encode));
        poly_as = vector<::polytools::SealPoly>(num_avar, polytools::SealPoly(context_encode));
        for(int i=0; i<num_avar; i++) {
            auto poly2 = polytools::SealPoly(context, a_plain[i]);
            auto polylist2 = poly2.get_coeff_list(modulus_encode);
            poly_as[i] = polytools::SealPoly(context_encode, polylist2, &(context_encode.first_parms_id()));
        }

        auto poly3=polytools::SealPoly(context, input_ctxt[0], 0);
        auto polylist3=poly3.get_coeff_list(modulus_encode);
        while(index<num_input){
            polys[index] = polytools::SealPoly(context_encode, polylist3, &(context_encode.first_parms_id()));
            index++;
        }

        size_t index_for_output = index;
        index++;
        auto poly = polytools::SealPoly(context_encode);

        //如果没有加法
        if(coefficient.size() == 1) {
            //如果没有乘法
            if(coefficient[0].size() == 1) {
                if(exp[0][0] == 1) {
                    poly = polys[coefficient[0][0]];
                    apoly[0] = poly;
                    poly.multiply_inplace(poly_as[0]);
                    polys[index_for_output] = poly;
                }else if(exp[0][0] == 2) {
                    poly = polys[coefficient[0][0]];
                    poly.multiply_inplace(poly);
                    apoly[0] = poly;
                    poly.multiply_inplace(poly_as[0]);
                    polys[index_for_output] = poly;
                }else {
                    for(int i = 2; i <= exp[0][0]; i++) {
                        if(i == 2) {
                            poly = polys[coefficient[0][0]];
                            poly.multiply_inplace(poly);
                            polys[index] = poly;
                            index++;
                        }else if(i != exp[0][0]) {
                            poly = polys[coefficient[0][0]];
                            poly.multiply_inplace(polys[index - 1]);
                            polys[index] = poly;
                            index++;
                        }else {
                            poly = polys[coefficient[0][0]];
                            poly.multiply_inplace(polys[index - 1]);
                            apoly[0] = poly;
                            poly.multiply_inplace(poly_as[0]);
                            polys[index_for_output] = poly;
                        }
                    }
                }
            }
                //如果有乘法
            else {
                for(int i = 0; i < coefficient[0].size(); i++) {
                    //进行幂运算
                    if (exp[0][i] == 1) {
                        temp_val.push_back(coefficient[0][i]);
                    } else if (exp[0][i] == 2) {
                        poly = polys[coefficient[0][i]];
                        poly.multiply_inplace(poly);
                        polys[index] = poly;
                        index++;
                        temp_val.push_back(index - 1);
                    } else {
                        for (int j = 2; j <= exp[0][i]; j++) {
                            if (j == 2) {
                                poly = polys[coefficient[0][i]];
                                poly.multiply_inplace(poly);
                                polys[index] = poly;
                                index++;
                            } else if (j != exp[0][i]) {
                                poly = polys[coefficient[0][i]];
                                poly.multiply_inplace(polys[index - 1]);
                                polys[index] = poly;
                                index++;
                            } else {
                                poly = polys[coefficient[0][i]];
                                poly.multiply_inplace(polys[index - 1]);
                                polys[index] = poly;
                                index++;
                                temp_val.push_back(index - 1);
                            }
                        }
                    }
                }
                //进行乘法运算
                if(temp_val.size() == 2) {
                    poly = polys[temp_val[0]];
                    poly.multiply_inplace(polys[temp_val[1]]);
                    apoly[0] = poly;
                    poly.multiply_inplace(poly_as[0]);
                    polys[index_for_output] = poly;
                }else {
                    for(int j = 1; j < temp_val.size(); j++) {
                        if(j == 1) {
                            poly = polys[temp_val[j]];
                            poly.multiply_inplace(polys[temp_val[j - 1]]);
                            polys[index] = poly;
                            index++;
                        }else if(j != temp_val.size() - 1) {
                            poly = polys[temp_val[j]];
                            poly.multiply_inplace(polys[index - 1]);
                            polys[index] = poly;
                            index++;
                        }else {
                            poly = polys[temp_val[j]];
                            poly.multiply_inplace(polys[index - 1]);
                            apoly[0] = poly;
                            poly.multiply_inplace(poly_as[0]);
                            polys[index_for_output] = poly;
                        }
                    }
                }
            }
        }
            //如果有加法
        else {
            for(int i = 0; i < coefficient.size(); i++) {
                temp_val.clear();
                for(int j = 0; j < coefficient[i].size(); j++) {
                    if(exp[i][j] > 1){
                        for(int k = 2; k <= exp[i][j]; k++) {
                            if(k == 2) {
                                poly = polys[coefficient[i][j]];
                                poly.multiply_inplace(poly);
                                polys[index] = poly;
                                index++;
                                if(exp[i][j] == 2)
                                    temp_val.push_back(index - 1);
                            }
                            else if(k != exp[i][j]){
                                poly =  polys[index - 1];
                                poly.multiply_inplace(polys[coefficient[i][j]]);
                                polys[index] = poly;
                                index++;
                            }
                            else {
                                poly =  polys[index - 1];
                                poly.multiply_inplace(polys[coefficient[i][j]]);
                                polys[index] = poly;
                                index++;
                                temp_val.push_back(index - 1);
                            }
                        }
                    }
                    else{
                        temp_val.push_back(coefficient[i][j]);
                    }
                }
                var_for_mul.push_back(temp_val);
            }

            for(int i = 0; i < coefficient.size(); i++) {

                if(var_for_mul[i].size() == 0) {
                    cout << i << "var_for_mul is 0" << endl;
                    continue;
                }
                if(var_for_mul[i].size() == 1) {
                    var_for_add.push_back(var_for_mul[i][0]);
                    continue;
                }
                for(int j = 1; j < var_for_mul[i].size(); j++) {
                    if(j == 1 && var_for_mul[i].size() == 2) {
                        poly = polys[var_for_mul[i][j]];
                        poly.multiply_inplace(polys[var_for_mul[i][j - 1]]);
                        polys[index] = poly;
                        index++;
                        var_for_add.push_back(index - 1);
                    }else if(j == 1 && var_for_mul[i].size() > 2){
                        poly = polys[var_for_mul[i][j]];
                        poly.multiply_inplace(polys[var_for_mul[i][j - 1]]);
                        polys[index] = poly;
                        index++;
                    }else if(j != var_for_mul[i].size() - 1){
                        poly = polys[index - 1];
                        poly.multiply_inplace(polys[var_for_mul[i][j]]);
                        polys[index] = poly;
                        index++;
                    }
                    else if(j == var_for_mul[i].size() - 1) {
                        poly = polys[index - 1];
                        poly.multiply_inplace(polys[var_for_mul[i][j]]);
                        polys[index] = poly;
                        index++;
                        var_for_add.push_back(index - 1);
                    }
                }
            }

            for(int i=0; i<num_avar;i++){
                poly = polys[var_for_add[i]];
                poly.multiply_inplace(poly_as[i]);
                apoly[i] = poly;
            }

            if(var_for_add.size() == 0) {
                std::cout << "var_for_add.size = 0" << std::endl;
            }else if(var_for_add.size() == 1) {
                std::cout << "var_for_add.size = 1" << std::endl;
            }else {
                for(int i = 1; i < var_for_add.size(); i++) {
                    if(i == 1 && var_for_add.size() == 2){
                        poly = apoly[i];
                        poly.add_inplace(apoly[i - 1]);
                        polys[index_for_output] = poly;
                    }else if(i == 1 && var_for_add.size() > 2){
                        poly = apoly[i];
                        poly.add_inplace(apoly[i - 1]);
                        polys[index] = poly;
                        index++;
                    }else if(i != var_for_add.size() - 1){
                        poly = apoly[i];
                        poly.add_inplace(polys[index - 1]);
                        polys[index] = poly;
                        index++;
                    }else {
                        poly = apoly[i];
                        poly.add_inplace(polys[index - 1]);
                        polys[index_for_output] = poly;
                    }
                }
            }
        }


        // int final_var_num = index;
        // cout << "exit: " << __FUNCTION__  << endl;
    }

    void generate_r1cs_witness(ringsnark::protoboard<R>& pb) {
        // 为public input和private witness设置值，x=3，out=35，其他的按照逻辑关系求解即可
        // cout << "entering into: " << __FUNCTION__  << endl;
        values.resize(polys.size());
        for(int i = 0; i < polys.size(); i++) {
            values[i] = ringsnark::seal::RingElem(polys[i]);
        }

        vector<ringsnark::seal::RingElem> avalue(num_avar);
        for(int i = 0; i < num_avar; i++) {
            avalue[i] = ringsnark::seal::RingElem(apoly[i]);
        }

        //输入的值
        for(int i = 0; i < polys.size(); i++) {
            pb.val(vars[i]) = values[i];
        }
        for(int i = 0; i < num_avar; i++) {
            pb.val(avar[i]) = avalue[i];
        }
        R rONE = R::one();
        pb.val(constant_one) = rONE;

       for(int i=0;i<num_avar;i++){
            pb.val(aR[i]) = ringsnark::seal::RingElem(poly_as[i]);
        }

        // cout << "exit: " << __FUNCTION__  << endl;
    }


private:
    size_t num_input; //输入变量的数量
    size_t num_var;   //全部变量的数量
    vector<vector<size_t>> coefficient;
    vector<vector<size_t>> exp;
    ringsnark::pb_variable_array<R> vars;
    ringsnark::pb_variable<R> constant_one = ringsnark::pb_variable<R>();
    vector<::polytools::SealPoly> polys;
    vector<ringsnark::seal::RingElem> values;
    vector<double> aj0;
    vector<Plaintext> a_plain;
    vector<ringsnark::pb_variable<R>> aR;
    ringsnark::pb_variable_array<R> avar;
    size_t num_avar;
    vector<::polytools::SealPoly> poly_as;
    vector<::polytools::SealPoly> apoly;
    vector<double> factorv;
    bool factorflag;
    size_t ex_unfold;
};

void is_e_des(std::string filename){
    if (std::filesystem::exists(filename)) {
        e_des = true;
    }
}

void clear_e_cache(std::string filename){
    if (std::filesystem::exists(filename)) {
        std::filesystem::remove(filename);
    }
}

int e_steps(string e02e, string save_path) {
    e_des = false;
    is_e_des("e_test.txt");

    //params
    EncryptionParameters params(scheme_type::ckks);
    auto poly_modulus_degree = ModulusDegree;
    auto inner_poly_modulus_degree = 2* poly_modulus_degree;

    params.set_poly_modulus_degree(poly_modulus_degree);
    double scale=pow(2.0, S_P);


    params.set_coeff_modulus(default_double_batching_modulus(poly_modulus_degree, inner_poly_modulus_degree));
    SEALContext context(params);

    // print_params(params);
    // cout<<"params"<<endl;

    R::set_context(context);
    E::set_context(inner_poly_modulus_degree);
    
    ringsnark::protoboard<R> pb;

    vector<vector<size_t>> coefficient = {{0, 1}};
    vector<vector<size_t>> exp = {{1, 1}};
    vector<vector<size_t>> aj = {{1}, {1}};
    size_t e_02 = getCipherNum(e02e);

    auto encoder = CKKSEncoder(context);
    KeyGenerator keygen(context);
    auto secret_key = keygen.secret_key();
    PublicKey public_key;
    keygen.create_public_key(public_key);

    Encryptor encryptor(context, public_key);
    Evaluator evaluator(context);

    auto tables =context.get_context_data(context.first_parms_id())->small_ntt_tables();
    size_t slot_count = encoder.slot_count();
    // cout<<"slot count: "<<slot_count<<endl;
    vector<double> vs(slot_count);
    Plaintext ptxt;
    Ciphertext ctxt;
    vector<Ciphertext> cipherVec;

    for(int i=0;i<slot_count;i++)
    {
        vs[i]=i;
    }
    encoder.encode(vs,scale,ptxt);
    encryptor.encrypt(ptxt,ctxt);
    cipherVec.push_back(ctxt);

    clock_t start_clock = clock();

    CircuitE circuite = CircuitE(pb, coefficient, exp, aj, 2, e_02);

    circuite.aj_to_aplain(context, scale, pb);

    circuite.generate_r1cs_constraints(pb);
    clock_t r1cs_constrains_finish = clock();
    
    cout << "R1CS satisfied: " << std::boolalpha << pb.is_satisfied() << endl;
    cout << endl;

    cout << "=== Rinocchio ===" << endl;
    clock_t generator_begin = clock();
    auto keypair =ringsnark::rinocchio::generator<R, E>(pb.get_constraint_system());
    clock_t generator_finish = clock();
    cout << "Size of pk:\t" << keypair.pk.size_in_bits() << " bits" << endl;
    cout << "Size of vk:\t" << keypair.vk.size_in_bits() << " bits" << endl;


    clock_t poly_compute_begin = clock();
    circuite.compute_seal_poly(context, cipherVec);//keti2
    clock_t poly_compute_finish = clock();

    circuite.generate_r1cs_witness(pb);

    auto proof = ringsnark::rinocchio::prover(keypair.pk, pb.primary_input(), pb.auxiliary_input());
    clock_t prover_finish = clock();
    

    bool verif =
            ringsnark::rinocchio::verifier(keypair.vk, pb.primary_input(), proof);
    clock_t verify_finish = clock();

    cout << "r1cs_consraint time is: " << ((double)r1cs_constrains_finish - start_clock) / CLOCKS_PER_SEC <<"s"<< endl;
    cout << "generator time is: " << ((double)generator_finish - generator_begin) / CLOCKS_PER_SEC <<"s"<< endl;
    cout << "poly compute time is: " << ((double)poly_compute_finish - poly_compute_begin) / CLOCKS_PER_SEC <<"s"<<  endl;

    cout << "Size of proof:\t" << proof.size_in_bits() << " bits" << endl;
    cout << "prover time is:\t" << ((double)prover_finish - poly_compute_finish) / CLOCKS_PER_SEC <<"s"<< endl;
    cout << "verify time is:\t" << ((double)verify_finish - prover_finish) / CLOCKS_PER_SEC <<"s"<< endl;
    cout << "Verification passed: " << std::boolalpha << verif << endl;

    std::ofstream outFile(save_path, std::ios::app);
    if (!outFile) {
        std::cout << "无法打开文件"<<save_path<<"进行写入。" << std::endl;
        return 1;
    }
    outFile<<"==============================================================================="<<endl;
    outFile<< "Operation type:\t-e" << endl;
    outFile<< "Calculate scale:\t" << e02e << endl;
    outFile<< "scale=\t2^" << S_P << endl;
    outFile<< "Size of pk:\t" << keypair.pk.size_in_bits() << " bits" << endl;
    outFile<< "Size of vk:\t" << keypair.vk.size_in_bits() << " bits" << endl;
    outFile<< "Size of proof:\t" << proof.size_in_bits() << " bits" << endl;

    outFile<< "setup time is:\t"<< ((double)generator_finish - start_clock) / CLOCKS_PER_SEC <<"s"<<endl;
    outFile<< "prove time is:\t"<< ((double)prover_finish - poly_compute_finish) / CLOCKS_PER_SEC <<"s"<<endl;
    outFile<< "verify time is:\t"<< ((double)verify_finish - prover_finish) / CLOCKS_PER_SEC <<"s"<<endl;
    outFile<< "Verification passed: " << std::boolalpha << verif << endl;
    outFile<<endl<<endl;

    outFile.close();
    cout << "The calculation verification log has been stored in file: " << save_path << endl;
    return 0;
}

size_t getNfromA(size_t a_size, string type){
    size_t n = 0;
    size_t as_n = a_size/Inner_N;
    string a_s = "-a";
    string m_d = "-m";
    if(type==a_s){
        n = as_n/4 - 1;
    } else if(type==m_d){
        n = (as_n - 4)/9;
    }
    return n;
}

vector<unsigned long long> readCSV(string csv_path){
    std::vector<unsigned long long> data;
    unsigned long long data_size;

    // 创建一个ifstream对象用于读取文件
    std::ifstream inFile(csv_path, std::ios::binary);

     // 检查文件是否成功打开
    if (!inFile) {
        std::cerr << "无法打开文件!" << std::endl;
        return data;
    }

    // 读取数据到数组
    inFile.read(reinterpret_cast<char*>(&data_size), sizeof(unsigned long long));
    data.resize(data_size);
    inFile.read(reinterpret_cast<char*>(data.data()), data_size * sizeof(unsigned long long));

    // 检查是否读取成功
    if (!inFile) {
        std::cerr << "读取文件失败!" << std::endl;
    }
    // 关闭文件
    inFile.close();

    return data;
}

size_t getSampNum(size_t c_n, std::string cal_num, std::string cal_type){
    boost::math::normal_distribution<double> dist(0.0, 1.0);
    double z_value = boost::math::quantile(dist, ConfidenceLevel);
    double zs = std::pow(z_value, 2);
    double coefficient = ConfidenceLevel * z_value * (1 - ConfidenceLevel) * z_value;
    size_t n = static_cast<size_t>(std::ceil(ConfidenceLevel*coefficient*zs*(1-ConfidenceLevel)*c_n));
    if(n < 2){
        n = 2;
    }
    std::string mul_div = "-m";
    size_t cal_nt = std::stoi(cal_num);
    if(cal_type==mul_div && cal_nt > DEVICE_MEMORY_MAX){
        double samp_device = (cal_nt/DEVICE_MEMORY_MAX) << 13;
        n *= samp_device;
        n = n >> 13;
        n += 1;
    }
    return n;
}

void idx2poly(vector<unsigned long long> &data, size_t idx, size_t num, vector<unsigned long long> &res,size_t resb){
    size_t lenth = num*Inner_N;
    size_t begin = idx*Inner_N;
    size_t resbeg = resb*Inner_N;
    for(size_t i=0;i<lenth;i++){
        res[resbeg+i] = data[begin + i];
    }
}

vector<size_t> get_as_idxs(size_t ii, size_t n_c){
    vector<size_t> index_list;
    if(ii==0){
        index_list.push_back(0);
        index_list.push_back(1);
        if(ii==n_c-1){
            index_list.push_back(2);
        }
        else{
            index_list.push_back(n_c+2);
        }
    }
    else{
        index_list.push_back(ii+1);
        index_list.push_back(n_c+ii+1);
        if(ii==n_c-1){
            index_list.push_back(n_c+1);
        }
        else{
            index_list.push_back(n_c+ii+2);
        }
    }
    
    for(int i=0;i<index_list.size();i++){
        index_list[i] = 2*index_list[i];
    }
    return index_list;
}

vector<size_t> get_md_idxs(size_t ii, size_t n_c){
    vector<size_t> index_list;
    index_list.push_back(0);
    if(ii==0){
        index_list.push_back(0);
        index_list.push_back(4);
        if(ii==n_c-1){
            index_list.push_back(2);
        }
        else{
            index_list.push_back(11);
        }
    }
    else{
        index_list.push_back(9*ii + 2);
        index_list.push_back(9*ii + 4);
        if(ii==n_c-1){
            index_list.push_back(2);
        }
        else{
            index_list.push_back(9*ii + 11);
        }
    }
    return index_list;
}

string retainNumbers(string str) {
    string result;
    for (char c : str) {
        // 如果字符是数字，则添加到结果字符串中
        if (std::isdigit(c)) {
            result += c;
        }
    }
    return result;
}

typedef struct Setup_output{
    SEALContext context;
    ringsnark::rinocchio::proving_key<R, E> pk;
    ringsnark::rinocchio::verification_key<R, E> vk;
    ringsnark::protoboard<R> pb;
    Circuit circuit;
    double setup_time;
}SetupOut;

typedef struct Prove_output{
    ringsnark::rinocchio::proof<R, E> proof;
    r1cs_primary_input<R> pm;
    double prove_time;
}ProveOut;

SetupOut Setup(int poly_modulus_degree, double scale, vector<vector<size_t>> coefficient, vector<vector<size_t>> exp, vector<vector<size_t>> aj){
    //加密方案用的params
    EncryptionParameters params(scheme_type::ckks);
    
    // auto poly_modulus_degree = 8192;
    auto inner_poly_modulus_degree = 2* poly_modulus_degree;

    params.set_poly_modulus_degree(poly_modulus_degree);
    // double scale=pow(2.0,50);

    std::vector<Modulus> custom_coeff_modulus = {
        Modulus(1073872897),
        Modulus(1074266113),
        Modulus(1077477377),
        Modulus(1079443457),
        // Modulus(1080360961),
        // Modulus(1081212929),
        // Modulus(1082982401),
        // Modulus(1079443457)
    };
    // params.set_coeff_modulus(default_double_batching_modulus(poly_modulus_degree, inner_poly_modulus_degree));
    params.set_coeff_modulus(custom_coeff_modulus);
    SEALContext context(params, true, sec_level_type::none);
    // SEALContext context(params);

    // print_params(params);
    // cout<<"params"<<endl;

    R::set_context(context);
    E::set_context(inner_poly_modulus_degree);
    auto coeff_modulus = context.get_context_data(context.first_parms_id())->parms().coeff_modulus();
    ringsnark::protoboard<R> pb;

    clock_t start_clock = clock();

    Circuit circuit = Circuit(pb, coefficient, exp, aj);

    circuit.aj_to_aplain(context, scale, pb);

    circuit.generate_r1cs_constraints(pb);
    clock_t r1cs_constrains_finish = clock();
    
    

    // cout << "#Inputs\t" << pb.num_inputs() << endl;
    // cout << "#Variables\t" << pb.num_variables() << endl;
    // cout << "#Constraints\t" << pb.num_constraints() << endl;
    cout << "R1CS satisfied: " << std::boolalpha << pb.is_satisfied() << endl;
    cout << endl;
    
    cout << "=== Rinocchio ===" << endl;
    clock_t generator_begin = clock();
    auto keypair =ringsnark::rinocchio::generator<R, E>(pb.get_constraint_system());
    clock_t generator_finish = clock();
    cout << "Size of pk:\t" << keypair.pk.size_in_bits() << " bits" << endl;
    cout << "Size of vk:\t" << keypair.vk.size_in_bits() << " bits" << endl;


    cout << "r1cs_consraint time is: " << ((double)r1cs_constrains_finish - start_clock) / CLOCKS_PER_SEC <<"s"<< endl;
    cout << "generator time is: " << ((double)generator_finish - generator_begin) / CLOCKS_PER_SEC <<"s"<< endl;

    double setupT = ((double)generator_finish - start_clock) / CLOCKS_PER_SEC;

    SetupOut output0 = {context, keypair.pk, keypair.vk, pb, circuit, setupT};
    return output0;
}

Circuit Comute(SEALContext context, Circuit circuit, vector<unsigned long long> &data, size_t ii, size_t n_comp, string type){
    vector<unsigned long long> da;
    size_t relnKidx = data.size()/Inner_N - 2;

    if(type=="-m"){
        da.resize(Inner_N*15);
        vector<size_t> idxs = get_md_idxs(ii,n_comp);
        idx2poly(data, idxs[0], 2, da, 0);
        idx2poly(data, idxs[1], 2, da, 2);
        idx2poly(data, idxs[2], 7, da, 6);
        idx2poly(data, idxs[3], 2, da, 4);
        idx2poly(data, relnKidx, 2, da, 13);
    }
    else{
        da.resize(Inner_N*8);
        vector<size_t> idxs = get_as_idxs(ii,n_comp);
        idx2poly(data, idxs[0], 2, da, 0);
        idx2poly(data, idxs[1], 2, da, 2);
        idx2poly(data, idxs[2], 2, da, 4);
        idx2poly(data, relnKidx, 2, da, 6);
    }

    circuit.copy_polys_from_A(da, context);

    // cout << "poly compute"<<  endl;

    return circuit;
}

ProveOut Prove(ringsnark::protoboard<R> pb, Circuit circuit, ringsnark::rinocchio::proving_key<R, E> pk){
    clock_t poly_compute_finish = clock();

    circuit.generate_r1cs_witness(pb);

    auto proof = ringsnark::rinocchio::prover(pk, pb.primary_input(), pb.auxiliary_input());
    clock_t prover_finish = clock();
    // cout << "Size of proof:\t" << proof.size_in_bits() << " bits" << endl;

    // cout << "prover time is: " << ((double)prover_finish - poly_compute_finish) / CLOCKS_PER_SEC << endl;
    double prover_time = ((double)prover_finish - poly_compute_finish) / CLOCKS_PER_SEC;

    ProveOut output = {proof, pb.primary_input(), prover_time};
    
    return output;
}

bool Verify(ringsnark::rinocchio::verification_key<R, E> vk, r1cs_primary_input<R> pm, ringsnark::rinocchio::proof<R, E> proof, double &verify_time){
    clock_t prover_finish = clock();

    bool verif = ringsnark::rinocchio::verifier(vk, pm, proof);
    clock_t verify_finish = clock();

    // cout << "Verification passed: " << std::boolalpha << verif << endl;
    // cout << "verify time is: " << ((double)verify_finish - prover_finish) / CLOCKS_PER_SEC << endl;
    verify_time = ((double)verify_finish - prover_finish) / CLOCKS_PER_SEC;

    return verif;
}

ringsnark::seal::RingElem testVerify(ringsnark::rinocchio::verification_key<R, E> vk, r1cs_primary_input<R> pm, ringsnark::rinocchio::proof<R, E> proof, double &verify_time){
    clock_t prover_finish = clock();

    ringsnark::seal::RingElem verif = ringsnark::rinocchio::test_verifier(vk, pm, proof);
    clock_t verify_finish = clock();

    // cout << "Verification passed: " << std::boolalpha << verif << endl;
    // cout << "verify time is: " << ((double)verify_finish - prover_finish) / CLOCKS_PER_SEC << endl;
    verify_time = ((double)verify_finish - prover_finish) / CLOCKS_PER_SEC;

    return verif;
}

void saveSizet(size_t siz, string filePath, string numName){
    string dir = filePath;
    if (!dir.empty() && dir.back() == '/') {
        dir.erase(dir.size() - 1);  // 去除最后一个字符
    }
    std::filesystem::create_directories(dir);
    std::ofstream ofs(filePath + numName, std::ios::binary);
    ofs.write(reinterpret_cast<const char*>(&siz), sizeof(size_t));
    ofs.close();
}

size_t loadSizet(string filePath, string numName){
    size_t siz;
    std::ifstream ifs(filePath + numName, std::ios::binary);
    if (!ifs) {
        std::cerr << "Error opening file for reading:" << filePath + numName << std::endl;
        return 0;
    }
    ifs.read(reinterpret_cast<char*>(&siz), sizeof(size_t));
    ifs.close();
    return siz;
}

SEALContext creat_context(size_t modulus_degree){
    EncryptionParameters params2(scheme_type::ckks);
    // auto inner_poly_modulus_degree2 = 2* modulus_degree;
    params2.set_poly_modulus_degree(modulus_degree);
    std::vector<Modulus> custom_coeff_modulus2 = {
        Modulus(1073872897),
        Modulus(1074266113),
        Modulus(1077477377),
        Modulus(1079443457),
        // Modulus(1080360961),
        // Modulus(1081212929),
        // Modulus(1082982401),
        // Modulus(1079443457)
    };
    params2.set_coeff_modulus(custom_coeff_modulus2);
    SEALContext context2(params2, true, sec_level_type::none);
    return context2;
}

void SavepkSpows(const ringsnark::rinocchio::proving_key<R, E> &pk, std::string filePath){
    size_t sp_size = pk.s_pows.size();
    saveSizet(sp_size, filePath, "sps.bin");

    vector<E> sptmp = pk.s_pows;
    for(size_t i=0;i<sp_size;i++){
        std::string istr = std::to_string(i);
        std::string savepath = filePath + "sp_"+ istr + "/";
        sptmp[i].saveElem(savepath);
    }
}


vector<E> LoadpkSpows(std::string filePath, SEALContext &context){
    size_t sp_size = loadSizet(filePath, "sps.bin");

    vector<E> sptmp;
    for(size_t i=0;i<sp_size;i++){
        std::string istr = std::to_string(i);
        std::string savepath = filePath + "sp_"+ istr + "/";
        E etmp;
        etmp.loadElem(savepath, context);
        sptmp.push_back(etmp);
    }
    return sptmp;
}

void saveRvector(vector<R> &vr, string filePath, string numName, string ass){
    size_t vr_size = vr.size();
    saveSizet(vr_size, filePath, numName);

    for(size_t i=0;i<vr_size;i++){
        string istr = std::to_string(i);
        string save_path = filePath + ass + istr + "/";
        vr[i].saveR(save_path);
    }
}

vector<R> LoadRvector(string filePath, string numName, string ass, SEALContext &context){
    size_t vr_size = loadSizet(filePath, numName);

    vector<R> vr;
    for(size_t i=0;i<vr_size;i++){
        string istr = std::to_string(i);
        string load_path = filePath + ass + istr + "/";
        R rtmp;
        rtmp.loadR(load_path, context);
        vr.push_back(rtmp);
    }
    return vr;
}


void save_linear_combination(const ringsnark::linear_combination<R> &lc, string filePath){
    size_t ts = lc.terms.size();
    saveSizet(ts, filePath, "lc_term_size.bin");
    for(size_t i=0;i<ts;i++){
        string istr = std::to_string(i);
        size_t vart = lc.terms[i].index;
        R coe = lc.terms[i].coeff;
        saveSizet(vart, filePath + "lc_term_" + istr +"/", "idx.bin");
        coe.saveR(filePath + "lc_term_" + istr +"/");
    }
}

ringsnark::linear_combination<R> load_linear_combination(string filePath, SEALContext &context){
    size_t ts = loadSizet(filePath, "lc_term_size.bin");
    ringsnark::linear_combination<R> lc;
    lc.terms.clear();
    for(size_t i=0;i<ts;i++){
        string istr = std::to_string(i);
        size_t vart = loadSizet(filePath + "lc_term_" + istr +"/", "idx.bin");
        R coe;
        coe.loadR(filePath + "lc_term_" + istr +"/", context);
        ringsnark::variable<R> va(vart);
        ringsnark::linear_term<R> term0(va, coe);
        lc.terms.push_back(term0);
    }
    return lc;
}


void savepk_r1cs(const ringsnark::rinocchio::proving_key<R, E> &pk, std::string filePath){
    size_t psize = pk.constraint_system.primary_input_size;
    size_t asize = pk.constraint_system.auxiliary_input_size;
    saveSizet(psize, filePath, "psize.bin");
    saveSizet(asize, filePath, "asize.bin");

    size_t c_size = pk.constraint_system.constraints.size();
    saveSizet(c_size, filePath, "constraints_size.bin");

    for(size_t i=0;i<c_size;i++){
        string istr = std::to_string(i);
        string sp0 = filePath + "cs_" + istr + "/";
        save_linear_combination(pk.constraint_system.constraints[i].a, sp0 + "line_a/");
        save_linear_combination(pk.constraint_system.constraints[i].b, sp0 + "line_b/");
        save_linear_combination(pk.constraint_system.constraints[i].c, sp0 + "line_c/");
    }
}

ringsnark::r1cs_constraint_system<R> loadpk_r1cs(std::string filePath, SEALContext &context){
    size_t psize = loadSizet(filePath, "psize.bin");
    size_t asize = loadSizet(filePath, "asize.bin");

    ringsnark::r1cs_constraint_system<R> r1cs_sys;
    r1cs_sys.primary_input_size = psize;
    r1cs_sys.auxiliary_input_size = asize;
    r1cs_sys.constraints.clear();

    size_t c_size = loadSizet(filePath, "constraints_size.bin");
    for(size_t i=0;i<c_size;i++){
        string istr = std::to_string(i);
        string sp0 = filePath + "cs_" + istr + "/";
        linear_combination<R> la = load_linear_combination(sp0 + "line_a/", context);
        linear_combination<R> lb = load_linear_combination(sp0 + "line_b/", context);
        linear_combination<R> lc = load_linear_combination(sp0 + "line_c/", context);
        ringsnark::r1cs_constraint<R> rc(la, lb, lc);
        r1cs_sys.constraints.push_back(rc);
    }
    return r1cs_sys;
}

void SaveOnePK(const ringsnark::rinocchio::proving_key<R, E> &pk, std::string filePath){
    savepk_r1cs(pk, filePath + "r1cs_sys/");
    SavepkSpows(pk, filePath + "s_pows/");
}

ringsnark::rinocchio::proving_key<R, E> LoadOnePK(std::string filePath, SEALContext &context){
    ringsnark::r1cs_constraint_system<R> r1cs =  loadpk_r1cs(filePath + "r1cs_sys/", context);
    vector<E> s_pows = LoadpkSpows(filePath + "s_pows/", context);
    E::PublicKey ep;
    ringsnark::rinocchio::proving_key<R, E> pk(r1cs, s_pows, ep);
    return pk;
}

void SaveOneSKenc(const ringsnark::rinocchio::verification_key<R, E> &vk, std::string filePath){
    size_t sks = vk.sk_enc.size();
    saveSizet(sks, filePath, "sks.bin");

    for(size_t i=0;i<sks;i++){
        string skn = std::to_string(i);
        // std::ofstream ofs1(filePath + "sk_" + skn + ".bin", std::ios::binary);
        // if(!ofs1){
        //     std::cerr << "Error opening file for writing: " << filePath + "sk_" + skn + ".bin" << std::endl;
        //     return;
        // }
        // vk.sk_enc[i].save(ofs1);
        // ofs1.close();
        vk.sk_enc[i].my_save(filePath + "sk_" + skn + "/");
    }
}

E::SecretKey LoadOneSKenc(std::string filePath, SEALContext &context){
    size_t sks = loadSizet(filePath, "sks.bin");

    E::SecretKey sk_enc;
    for(size_t i=0;i<sks;i++){
        ::seal::SecretKey sk1;
        string skn = std::to_string(i);
        // std::ifstream ifs1(filePath + "sk_" + skn + ".bin", std::ios::binary);
        // if(!ifs1){
        //     std::cerr << "Error opening file for reading: " << filePath + "sk_" + skn + ".bin" << std::endl;
        //     return sk_enc;
        // }
        // sk1.load(context, ifs1);
        // ifs1.close();

        sk1.my_load(filePath + "sk_" + skn + "/");
        sk_enc.push_back(sk1);
        // sk_enc[i] = sk1;
    }
    return sk_enc;
}

void SaveOneQRPinst(ringsnark::rinocchio::verification_key<R, E> &vk, std::string filePath){
    size_t num_var = vk.qrp_inst.num_inputs();
    size_t degree = vk.qrp_inst.degree();
    size_t num_inputs = vk.qrp_inst.num_inputs();
    saveSizet(num_var, filePath, "num_var.bin");
    saveSizet(degree, filePath, "degree.bin");
    saveSizet(num_inputs, filePath, "num_inputs.bin");

    R qrp_s =  vk.qrp_inst.t;
    R qrp_zt =  vk.qrp_inst.Zt;
    qrp_s.saveR(filePath + "qrp_s/");
    qrp_zt.saveR(filePath + "qrp_zt/");

    vector<R> qrp_at = vk.qrp_inst.At;
    saveRvector(qrp_at, filePath + "qrp_at/", "ats.bin", "at_");
    vector<R> qrp_bt = vk.qrp_inst.Bt;
    saveRvector(qrp_bt, filePath + "qrp_bt/", "bts.bin", "bt_");
    vector<R> qrp_ct = vk.qrp_inst.Ct;
    saveRvector(qrp_ct, filePath + "qrp_ct/", "cts.bin", "ct_");
    vector<R> qrp_ht = vk.qrp_inst.Ht;
    saveRvector(qrp_ht, filePath + "qrp_ht/", "hts.bin", "ht_");

    vector<R> qrp_aiot = vk.qrp_inst.Aio_t;
    saveRvector(qrp_aiot, filePath + "qrp_aiot/", "aiots.bin", "aiot_");
    vector<R> qrp_biot = vk.qrp_inst.Bio_t;
    saveRvector(qrp_biot, filePath + "qrp_biot/", "biots.bin", "biot_");
    vector<R> qrp_ciot = vk.qrp_inst.Cio_t;
    saveRvector(qrp_ciot, filePath + "qrp_ciot/", "ciots.bin", "ciot_");

    size_t qrp_dm = vk.qrp_inst.domain->get_m();
    vector<R> qrp_dvalues = vk.qrp_inst.domain->get_values();
    vector<R> qrp_dlagd = vk.qrp_inst.domain->get_lagrange_denominator();
    saveSizet(qrp_dm, filePath + "qrp_dm/", "m.bin");
    saveRvector(qrp_dvalues, filePath + "qrp_dvalues/", "values.bin", "val_");
    saveRvector(qrp_dlagd, filePath + "qrp_dlagd/", "lagd.bin", "ld_");

}

qrp_instance_evaluation<R> LoadOneQRPinst(std::string filePath, SEALContext &context){
    size_t num_var = loadSizet(filePath, "num_var.bin");
    size_t degree = loadSizet(filePath, "degree.bin");
    size_t num_inputs = loadSizet(filePath, "num_inputs.bin");

    R qrp_s;
    R qrp_zt;
    qrp_s.loadR(filePath + "qrp_s/", context);
    qrp_zt.loadR(filePath + "qrp_zt/", context);

    vector<R> qrp_at = LoadRvector(filePath + "qrp_at/", "ats.bin", "at_", context);
    vector<R> qrp_bt = LoadRvector(filePath + "qrp_bt/", "bts.bin", "bt_", context);
    vector<R> qrp_ct = LoadRvector(filePath + "qrp_ct/", "cts.bin", "ct_", context);
    vector<R> qrp_ht = LoadRvector(filePath + "qrp_ht/", "hts.bin", "ht_", context);
    

    vector<R> qrp_aiot = LoadRvector(filePath + "qrp_aiot/", "aiots.bin", "aiot_", context);
    vector<R> qrp_biot = LoadRvector(filePath + "qrp_biot/", "biots.bin", "biot_", context);
    vector<R> qrp_ciot = LoadRvector(filePath + "qrp_ciot/", "ciots.bin", "ciot_", context);

    size_t qrp_dm = loadSizet(filePath + "qrp_dm/", "m.bin");
    vector<R> qrp_dvalues = LoadRvector(filePath + "qrp_dvalues/", "values.bin", "val_", context);
    vector<R> qrp_dlagd = LoadRvector(filePath + "qrp_dlagd/", "lagd.bin", "ld_", context);

    std::shared_ptr<evaluation_domain<R>> domain_ptr = std::make_shared<evaluation_domain<R>>(qrp_dm);
    domain_ptr->set_values(qrp_dvalues);
    domain_ptr->set_lagrange_denominator(qrp_dlagd);

    qrp_instance_evaluation<R> qrp_inst(domain_ptr, num_var, degree, num_inputs, qrp_s, qrp_at, qrp_bt, qrp_ct, qrp_ht, qrp_zt);

    size_t aiots = qrp_aiot.size();
    qrp_inst.Aio_t.resize(aiots);
    for(size_t i=0;i<aiots;i++){
        qrp_inst.Aio_t[i] = qrp_aiot[i];
    }

    size_t biots = qrp_biot.size();
    qrp_inst.Bio_t.resize(biots);
    for(size_t i=0;i<biots;i++){
        qrp_inst.Bio_t[i] = qrp_biot[i];
    }

    size_t ciots = qrp_ciot.size();
    qrp_inst.Cio_t.resize(ciots);
    for(size_t i=0;i<ciots;i++){
        qrp_inst.Cio_t[i] = qrp_ciot[i];
    }

    return qrp_inst;
}

void SaveOneVK(ringsnark::rinocchio::verification_key<R, E> &vk, size_t pvnum){
    std::string pvns = std::to_string(pvnum);
    std::string file_path0 = sl_path0 + "/pv" + pvns + "/vk/";

    SaveOnePK(vk.pk, file_path0 + "pk/");
    
    R s_tmp = vk.s;
    bool scomplete =  s_tmp.saveR(file_path0 + "s/");

    SaveOneSKenc(vk, file_path0 + "sk_enc/");

    SaveOneQRPinst(vk, file_path0 + "qrp_inst/");
}


ringsnark::rinocchio::verification_key<R, E> LoadOneVK(size_t pvnum, SEALContext &context){
    std::string pvns = std::to_string(pvnum);
    std::string file_path0 = sl_path0 + "/pv" + pvns + "/vk/";

    // cout << "vk_debug1"<< endl;
    ringsnark::rinocchio::proving_key<R, E> pk = LoadOnePK(file_path0 + "pk/", context);

    // cout << "vk_debug2"<< endl;
    R s_tmp;
    bool scomplete = s_tmp.loadR(file_path0 + "s/", context);

    // cout << "vk_debug3"<< endl;

    E::SecretKey sk_enc = LoadOneSKenc(file_path0 + "sk_enc/", context);

    // cout << "vk_debug4"<< endl;

    qrp_instance_evaluation<R> qrp_inst = LoadOneQRPinst(file_path0 + "qrp_inst/", context);

    // cout << "vk_debug5"<< endl;

    ringsnark::rinocchio::verification_key<R, E> vk(pk, s_tmp, sk_enc, qrp_inst);

    // cout << "vk_debug6"<< endl;
    return vk;
}

void SavePM0(vector<R> &pm, string filePath){
    size_t pm_size = pm.size();
    saveSizet(pm_size, filePath, "pm_size.bin");

    for(size_t i=0;i<pm_size;i++){
        string istr = std::to_string(i);
        string save_path = filePath + "pmr" + istr + "/";
        pm[i].saveR(save_path);
    }
}

vector<R> LoadPM0(string filePath, SEALContext &context){
    size_t pm_size = loadSizet(filePath, "pm_size.bin");

    // cout << "pm0_debug1"<< endl;

    vector<R> pm;
    for(size_t i=0;i<pm_size;i++){
        string istr = std::to_string(i);
        string load_path = filePath + "pmr" + istr + "/";
        R rtmp;
        rtmp.loadR(load_path, context);
        pm.push_back(rtmp);
    }
    // cout << "pm0_debug2"<< endl;
    return pm;
}

void SaveOnePM(vector<R> &pm, size_t pvnum){
    std::string pvns = std::to_string(pvnum);
    std::string file_path0 = sl_path0 + "/pv" + pvns + "/pm/";
    SavePM0(pm, file_path0);
}

vector<R> LoadOnePM(size_t pvnum, SEALContext &context){
    std::string pvns = std::to_string(pvnum);
    std::string file_path0 = sl_path0 + "/pv" + pvns + "/pm/";
    vector<R> pm = LoadPM0(file_path0, context);
    return pm;
}

void SavePF0(ringsnark::rinocchio::proof<R, E> &pf, string filePath){
    E ea = pf.A;
    ea.saveElem(filePath + "ea/");
    E eb = pf.B;
    eb.saveElem(filePath + "eb/");
    E ec = pf.C;
    ec.saveElem(filePath + "ec/");
    E ed = pf.D;
    ed.saveElem(filePath + "ed/");
}

ringsnark::rinocchio::proof<R, E> LoadPF0(string filePath, SEALContext &context){
    // cout << "pf0_debug1"<< endl;
    E ea;
    ea.loadElem(filePath + "ea/", context);
    // cout << "pf0_debug2"<< endl;
    E eb;
    eb.loadElem(filePath + "eb/", context);
    E ec;
    ec.loadElem(filePath + "ec/", context);
    E ed;
    ed.loadElem(filePath + "ed/", context);
    // cout << "ea_size: "<<ea.get_cipher_size()<< endl;
    // cout << "eb_size: "<<eb.get_cipher_size()<< endl;
    // cout << "ec_size: "<<ec.get_cipher_size()<< endl;
    // cout << "ed_size: "<<ed.get_cipher_size()<< endl;

    ringsnark::rinocchio::proof<R, E> pf(ea, eb, ec, ed);
    // cout << "pf0_debug4"<< endl;
    return pf;
}

void SaveOnePF(ringsnark::rinocchio::proof<R, E> &pf, size_t pvnum){
    std::string pvns = std::to_string(pvnum);
    std::string file_path0 = sl_path0 + "/pv" + pvns + "/pf/";
    SavePF0(pf, file_path0);
}

ringsnark::rinocchio::proof<R, E> LoadOnePF(size_t pvnum, SEALContext &context){
    std::string pvns = std::to_string(pvnum);
    std::string file_path0 = sl_path0 + "/pv" + pvns + "/pf/";
    ringsnark::rinocchio::proof<R, E> pf = LoadPF0(file_path0, context);
    return pf;
}

void load_verify_only(string poly_type, string filenameA, string filenameB){
    double vfTime = 0;
    bool verif = false;

    SEALContext lct = creat_context(ModulusDegree);
    R::set_context(lct);
    E::set_context(ModulusDegree * 2);

    size_t lsa = loadSizet(sl_path0 + "/", "samp.bin");

    for(size_t j=0;j<lsa;j++){
        string istr = std::to_string(j);
        size_t k = loadSizet(sl_path0 + "/pv" + istr + "/", "sak.bin");
        double vfTtmp;
        ringsnark::rinocchio::verification_key<R, E> vkl0 = LoadOneVK(j, lct);
        ringsnark::r1cs_primary_input<R> pml0 = LoadOnePM(j, lct);
        ringsnark::rinocchio::proof<R, E> pfl0 = LoadOnePF(j, lct);

        verif = Verify(vkl0, pml0, pfl0, vfTtmp);
        vfTime += vfTtmp;
        cout << "verify"<<k<<" time:\t" << vfTtmp << "s" << endl;
        cout << "verify"<<k<<" passed:\t" << std::boolalpha << verif << endl;

        if(!verif){
            cout<<"-----------------------------------verify false: "<<k<<endl;
            // break;
        }
    }

    cout << "verify time is:\t" << vfTime <<"s"<< endl;
    cout << "Verification passed: " << std::boolalpha << verif << endl;


    std::ofstream outFile(filenameB, std::ios::app);
    if (!outFile) {
        std::cout << "无法打开文件"<<filenameB<<"进行写入。" << std::endl;
    }

    outFile<<"================================================="<<endl;
    outFile<< "Operation type:\t" << poly_type << endl;
    outFile<< "Calculate scale:\t" << retainNumbers(filenameA) << endl;
    outFile<< "scale=\t2^" << S_P << endl;

    outFile<< "verify time is:\t"<< vfTime <<"s"<<endl;
    outFile<< "Verification passed: " << std::boolalpha << verif << endl;
    outFile<<endl<<endl;
    
    outFile.close();

    cout << "The verification log has been stored in file: " << filenameB << endl;
}

int main(int argc,char** argv) {
    std::string poly_type = argv[1];
    std::string filenameA = argv[2];
    std::string filenameB = argv[3];

    double scale=pow(2.0, S_P);
    std::string add_sub = "-a";
    std::string mul_div = "-m";
    std::string natural_base = "-e";

    if(poly_type==natural_base){
        if(argc>4){
            std::string ag4 = argv[4];
            if(ag4=="clear_e"){
                clear_e_cache("e_test.txt");
            }
        }
        int res = e_steps(filenameA, filenameB);
        return res;
    }

    vector<vector<size_t>> coefficient;
    vector<vector<size_t>> exp;
    vector<vector<size_t>> aj;

    vector<unsigned long long> data = readCSV(filenameA);
    // cout<<"data_size: "<<(data.size()/Inner_N)<<endl;
    size_t n_comp = getNfromA(data.size(), poly_type);
    // cout<<"n_comp: "<<n_comp<<endl;

    if(poly_type == add_sub){
        coefficient = {{0}, {1}};
        exp = {{1}, {1}};
        sl_path0 = "vbuff/a" + retainNumbers(filenameA);
    }else if(poly_type == mul_div){
        coefficient = {{0, 1}};
        exp = {{1, 1}};
        sl_path0 = "vbuff/m" + retainNumbers(filenameA);
    }else{
        std::cout<<"Illegal input!"<<std::endl;
        return 1;
    }

    bool clearF = true;
    if(argc>4){
        std::string ag4 = argv[4];
        for (char &c : ag4) {
            c = std::tolower(static_cast<unsigned char>(c));
        }
        if(ag4=="usebuff"){
            clearF = false;
        }
    }
    if(clearF){
        std::filesystem::path buff_path = "vbuff";
        if(std::filesystem::exists(buff_path) && std::filesystem::is_directory(buff_path)){
            try {
                std::filesystem::remove_all(buff_path);
            } catch (const std::filesystem::filesystem_error& e) {
                std::cerr << "file is occupied, " << e.what() << std::endl;
            }
        }
    }

    std::filesystem::path dir_path = sl_path0;
    if(std::filesystem::exists(dir_path) && std::filesystem::is_directory(dir_path)){
        load_verify_only(poly_type, filenameA, filenameB);
        return 0;
    }

    size_t pfSize = 0;
    double pfTime = 0;
    double vfTime = 0;
    // bool verif = false;

    SetupOut output1 = Setup(ModulusDegree, scale, coefficient, exp, aj);
    
    size_t pkSize = output1.pk.size_in_bits();
    size_t vkSize = output1.vk.size_in_bits();

    // size_t samp = getSampNum(n_comp, retainNumbers(filenameA), poly_type);
    size_t samp = n_comp;

    saveSizet(samp, sl_path0 + "/", "samp.bin");

    cout<<"n_comp: "<<n_comp<<endl;

    // size_t samp = n_comp;
    // std::uniform_int_distribution<> dis(0, n_comp-1);

    // SEALContext lct = creat_context(4096);

    int afalse_fl = 0;

    bool verif = true;

    ringsnark::seal::RingElem tverif, lastV, l2V;
    array<ringsnark::seal::RingElem, 2> tvf;
    for(int i=0;i<samp;i++){
        // std::mt19937 gen(time(0));
        // size_t k = dis(gen);
        size_t k = i+1;
        // Circuit circuit = Comute(output1.context, output1.circuit, data, k, n_comp, poly_type);
        Circuit circuit = Comute(output1.context, output1.circuit, data, i, n_comp, poly_type);
    
        ProveOut proof1 = Prove(output1.pb, circuit, output1.pk);
        pfSize += proof1.proof.size_in_bits();
        pfTime += proof1.prove_time;
        cout << "proof"<<k<<" size:\t" << proof1.proof.size_in_bits() << " bits" << endl;
        cout << "proof"<<k<<" time:\t" << proof1.prove_time << "s" << endl;


        string istr = std::to_string(i);
        // saveSizet(k, sl_path0 + "/pv" + istr + "/", "sak.bin");

        // SaveOneVK(output1.vk, i);
        // SaveOnePM(proof1.pm, i);
        // SaveOnePF(proof1.proof, i);


        double vfTtmp;
        // ringsnark::rinocchio::verification_key<R, E> vkl0 = LoadOneVK(i, lct);
        // ringsnark::r1cs_primary_input<R> pml0 = LoadOnePM(i, lct);
        // ringsnark::rinocchio::proof<R, E> pfl0 = LoadOnePF(i, lct);

        tvf[0] = testVerify(output1.vk, proof1.pm, proof1.proof, vfTtmp);
        vfTime += vfTtmp;
        cout << "verify"<<k<<" time:\t" << vfTtmp << "s" << endl;

        tverif = tvf[0];
        if(i==0){
            lastV = tvf[0];
            tvf[1] = tvf[0];
        }

        bool t1 = false, t2 = false, t3 = false, t4 = false;
        if(tvf[0]==tvf[1]){
            t1 = true;
        }
        array<E, 2> t2e0 =  ringsnark::rinocchio::aggsingleproof(output1.vk, proof1.pm, proof1.proof);
        vector<E> t2e = {t2e0[0], t2e0[1]}; 
        t2e[0] += t2e[1];
        vector<R> t2r = ringsnark::rinocchio::decodeTest(output1.vk, t2e);
        
        if(tvf[0] == t2r[0]){
            t2 = true;
        }
        
        lastV = tvf[0];
        tvf[1] = tvf[0];
        
        cout << "is verify t== :"<<t1<<","<<t2<<","<<t3<<","<<t4<<endl;
    }

    if(afalse_fl>0){
        verif = false;
    }


    cout << "Size of proof:\t" << pfSize << " bits" << endl;
    cout << "prover time is:\t" << pfTime <<"s"<< endl;
    cout << "verify time is:\t" << vfTime <<"s"<< endl;
    cout << "Verification passed: " << std::boolalpha << verif << endl;


    std::ofstream outFile(filenameB, std::ios::app);
    if (!outFile) {
        std::cout << "无法打开文件"<<filenameB<<"进行写入。" << std::endl;
        return 1;
    }

    outFile<<"================================================="<<endl;
    outFile<< "Operation type:\t" << poly_type << endl;
    outFile<< "Calculate scale:\t" << retainNumbers(filenameA) << endl;
    outFile<< "scale=\t2^" << S_P << endl;
    outFile<< "Size of pk:\t" << pkSize<< " bits" << endl;
    outFile<< "Size of vk:\t" << vkSize << " bits" << endl;
    outFile<< "Size of proof:\t" << pfSize << " bits" << endl;

    outFile<< "setup time is:\t"<< output1.setup_time <<"s"<<endl;
    outFile<< "prove time is:\t"<< pfTime <<"s"<<endl;
    outFile<< "verify time is:\t"<< vfTime <<"s"<<endl;
    outFile<< "Verification passed: " << std::boolalpha << verif << endl;
    outFile<<endl<<endl;
    
    outFile.close();

    cout << "The calculation verification log has been stored in file: " << filenameB << endl;
    return 0;
}