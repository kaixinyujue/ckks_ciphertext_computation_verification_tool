#include <iostream>
#include <fstream>
#include <sstream>
#include <filesystem>
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <random>
#include <string>
#include <cstring>
#include <algorithm>
#include <cmath>
#include <boost/math/distributions/normal.hpp>
#include <ringsnark/gadgetlib/protoboard.hpp>
#include <ringsnark/seal/seal_ring.hpp>
#include <ringsnark/seal/seal_util.hpp>

#include "poly_arith.h"
#include "seal/seal.h"

using namespace std;
using namespace seal;
using namespace ringsnark;
typedef ringsnark::seal::RingElem R;
typedef ringsnark::seal::EncodingElem E;

#define N 4096
#define LEN 3
#define S_P 50
#define Inner_N 12288
#define UNSIZEMAX 32767
#define DEVICE_MEMORY_MAX 50000000



::polytools::SealPoly *relin_poly0 = nullptr;
::polytools::SealPoly *relin_poly1 = nullptr;


void simpleCopy0(unsigned long long a[], unsigned long long b[]){
    memcpy(a, b, Inner_N*sizeof(unsigned long long));
}

class doublePoly{
    public:
    unsigned long long a[Inner_N];
    unsigned long long b[Inner_N];
    int depth = 0;
    doublePoly(unsigned long long a0[],unsigned long long b0[]){
        simpleCopy0(a, a0);
        simpleCopy0(b, b0);
    }
    doublePoly(){
    }
    void set(unsigned long long a0[],unsigned long long b0[]){
        simpleCopy0(a, a0);
        simpleCopy0(b, b0);
    }
    void set(unsigned long long b0[]){
        simpleCopy0(b, b0);
    }
};

class myCipherText:public doublePoly{
    public:
    // 使用doublePoly的构造函数来初始化a和b
    myCipherText(unsigned long long a0[], unsigned long long b0[]) : doublePoly(a0, b0) {}
    myCipherText() : doublePoly() {}
};

class myCipher2 {
public:
    ::polytools::SealPoly a;
    ::polytools::SealPoly b;

    // 构造函数，利用SealPoly的拷贝构造函数来初始化a和b
    myCipher2(const ::polytools::SealPoly& a0, const ::polytools::SealPoly& b0)
        : a(a0),
          b(b0) {}
};

class myRelienKey:public doublePoly{
    public:
    // 使用doublePoly的构造函数来初始化a和b
    myRelienKey(unsigned long long a0[], unsigned long long b0[]) : doublePoly(a0, b0) {}
    myRelienKey() : doublePoly() {}
};

typedef struct ULLArray {
    unsigned long long data[Inner_N];
}ULLA;

ULLA copyA(unsigned long long a[]){
    ULLA arr;
    // for(int i=0;i<Inner_N;i++){
    //     arr.data[i] = a[i];
    // }
    simpleCopy0(arr.data, a);
    return arr;
}
void copyB(myCipherText &a, ULLA b){
    // unsigned long long *d_data0 = new unsigned long long[Inner_N];
    // unsigned long long *d_data1 = new unsigned long long[Inner_N];
    // for(int i=0;i<Inner_N;i++){
    //     d_data0[i] = b.data[i];
    //     d_data1[i] = b.data[i];
    // }
    a.set(b.data, b.data);
}
void copyC(myCipherText &a, myCipherText b){
    // unsigned long long *d_data0 = new unsigned long long[Inner_N];
    // unsigned long long *d_data1 = new unsigned long long[Inner_N];
    // for(int i=0;i<Inner_N;i++){
    //     d_data0[i] = b.a[i];
    //     d_data1[i] = b.b[i];
    // }
    a.set(b.a, b.b);
}
void copyR(myCipherText &a, myRelienKey b){
    // unsigned long long *d_data0 = new unsigned long long[Inner_N];
    // unsigned long long *d_data1 = new unsigned long long[Inner_N];
    // for(int i=0;i<Inner_N;i++){
    //     d_data0[i] = b.a[i];
    //     d_data1[i] = b.b[i];
    // }
    a.set(b.a, b.b);
}

myCipher2 copyMC(const myCipher2 &b0){
    ::polytools::SealPoly p0 = b0.a;
    ::polytools::SealPoly p1 = b0.b;
    myCipher2 mc = myCipher2(p0, p1);
    return mc;
}

void copyBmc(myCipher2 &a0, ::polytools::SealPoly b0){
    a0.a = b0;
    a0.b = b0;
}

std::vector<std::string> splitLineStream(std::stringstream& linestream, char delimiter) {
    std::vector<std::string> result;
    std::string item;

    while (std::getline(linestream, item, delimiter)) {
        result.push_back(item);
    }

    return result;
}

myCipher2 C_to_mC2(Ciphertext c0, SEALContext &context){
    ::polytools::SealPoly p0 = polytools::SealPoly(context, c0, 0);
    ::polytools::SealPoly p1 = polytools::SealPoly(context, c0, 1);
    myCipher2 mc2 = myCipher2(p0, p1);
    return mc2;
}

myCipherText getCfromA(int idx, std::vector<ULLA> &polys0){
    myCipherText c(polys0[idx].data, polys0[idx+1].data);
    // unsigned long long *d_data0 = new unsigned long long[Inner_N];
    // unsigned long long *d_data1 = new unsigned long long[Inner_N];
    // for(int i=0;i<Inner_N;i++){
    //     d_data0[i] = polys0[idx].data[i];
    //     d_data1[i] = polys0[idx+1].data[i];
    // }

    // // cudaMalloc((void**)&d_data0, Inner_N * sizeof(unsigned long long));
    // // cudaMalloc((void**)&d_data1, Inner_N * sizeof(unsigned long long));
    // // cudaMemcpy(d_data0, polys0[idx].data, Inner_N * sizeof(unsigned long long), cudaMemcpyHostToDevice);
    // // cudaMemcpy(d_data1, polys0[idx+1].data, Inner_N * sizeof(unsigned long long), cudaMemcpyHostToDevice);
    // c.set(d_data0, d_data1);
    return c;
}

myCipher2 getMC2fromA(int idx, std::vector<::polytools::SealPoly> &polys0){
    myCipher2 mc2 = myCipher2(polys0[idx], polys0[idx+1]);
    return mc2;
}

myCipher2 mulPlain_my(myCipher2 &a0, const ::polytools::SealPoly &b0, SEALContext &context){
    ::polytools::SealPoly poly0 =  polytools::SealPoly(context);
    ::polytools::SealPoly poly1 =  polytools::SealPoly(context);
    poly0 = a0.a;
    poly0.multiply_inplace(b0);
    poly1 = a0.b;
    poly1.multiply_inplace(b0);
    myCipher2 mc = myCipher2(poly0, poly1);
    if(poly0.get_coeff_modulus_count()!=LEN || poly1.get_coeff_modulus_count()!=LEN){
        cout<< "warring: mul LEN and coeff_modulus_count dont match!!" <<endl;
    }
    return mc;
}

void addPlain_my(myCipher2 &a0, const ::polytools::SealPoly &b0){
    a0.a.add_inplace(b0);
    a0.b.add_inplace(b0);
    if(a0.a.get_coeff_modulus_count()!=LEN || a0.b.get_coeff_modulus_count()!=LEN){
        cout<< "warring: add0 LEN and coeff_modulus_count dont match!!" <<endl;
    }
}

void addmc2(myCipher2 &a0, const myCipher2 &b0){
    a0.a.add_inplace(b0.a);
    a0.b.add_inplace(b0.b);
    if(a0.a.get_coeff_modulus_count()!=LEN || a0.b.get_coeff_modulus_count()!=LEN){
        cout<< "warring: add LEN and coeff_modulus_count dont match!!" <<endl;
    }
}

void swap_mc2(myCipher2 &a0){
    ::polytools::SealPoly poly0 = a0.a;
    a0.a = a0.b;
    a0.b = poly0;
}

SEALContext myInit0(int poly_modulus_degree){
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
    // auto coeff_modulus = context.get_context_data(context.first_parms_id())->parms().coeff_modulus();


    // for (size_t i = 0; i < coeff_modulus.size(); ++i) {
    //     cout << "Coeff Modulus00 " << i << ": " << coeff_modulus[i].value() << endl;
    // }

    return context;
}

int poly_mul_cipher(myCipher2 ciphertexta, myCipher2 ciphertextb, int &idx, std::vector<::polytools::SealPoly> &polys0, SEALContext &context, int outidx=UNSIZEMAX){
    int last_idx;
    // myCipherText c0, c1, a, b;
    myCipher2 a = copyMC(ciphertexta);
    myCipher2 b = copyMC(ciphertextb);
    // copyC(a, ciphertexta);
    // copyC(b, ciphertextb);
    // c0 = mulPlain_lazy(a, b.a);
    myCipher2 c0 = mulPlain_my(a, b.a, context);

    // copyC(a, ciphertexta);
    // copyC(b, ciphertextb);
    // c1 = mulPlain_lazy(a, b.b);
    myCipher2 c1 = mulPlain_my(ciphertexta, ciphertextb.b, context);

    // polys0[idx] = copyA(c0.a);
    // polys0[idx + 1] = copyA(c0.b);
    // polys0[idx + 2] = copyA(c1.a);
    // polys0[idx + 3] = copyA(c1.b);
    polys0[idx] = c0.a;
    polys0[idx + 1] = c0.b;
    polys0[idx + 2] = c1.a;
    polys0[idx + 3] = c1.b;

    // std::swap(c0.a,c0.b);
    swap_mc2(c0);

    // addPlain(c0,c1.a);
    // polys0[idx + 4] = copyA(c0.a);
    addPlain_my(c0, c1.a);
    polys0[idx + 4] = c0.a;
    
    // myCipherText tmprel;
    // copyR(tmprel, relkey);
    myCipher2 tmprel = myCipher2(*relin_poly0, *relin_poly1);

    // copyB(c1, polys0[idx + 3]);
    copyBmc(c1, polys0[idx + 3]);

    // c0 = mulPlain_lazy(tmprel, c1.b);
    c0 = mulPlain_my(tmprel, c1.b, context);
    
    // polys0[idx + 5] = copyA(c0.a);
    // polys0[idx + 6] = copyA(c0.b);
    polys0[idx + 5] = c0.a;
    polys0[idx + 6] = c0.b;


    if(outidx!=UNSIZEMAX){
        // copyB(c1, polys0[idx]);
        // addPlain(c1, c0.a);
        // polys0[outidx] = copyA(c1.a);
        copyBmc(c1, polys0[idx]);
        addPlain_my(c1, c0.a);
        polys0[outidx] = c1.a;


        // copyB(c1, polys0[idx + 4]);
        // addPlain(c1, c0.b);
        // polys0[outidx + 1] = copyA(c1.a);
        copyBmc(c1, polys0[idx + 4]);
        addPlain_my(c1, c0.b);
        polys0[outidx + 1] = c1.a;


        idx += 7;
        return outidx;
    }
    // copyB(c1, polys0[idx]);
    // addPlain(c1, c0.a);
    // polys0[idx + 7] = copyA(c1.a);
    copyBmc(c1, polys0[idx]);
    addPlain_my(c1, c0.a);
    polys0[idx + 7] = c1.a;

    // copyB(c1, polys0[idx + 4]);
    // addPlain(c1, c0.b);
    // polys0[idx + 8] = copyA(c1.a);
    copyBmc(c1, polys0[idx + 4]);
    addPlain_my(c1, c0.b);
    polys0[idx + 8] = c1.a;

    last_idx = idx + 7;
    idx += 9;
    return last_idx;
}

int poly_add_cipher(myCipher2 ciphertexta, myCipher2 ciphertextb, int &idx, std::vector<::polytools::SealPoly> &polys0, int outidx=UNSIZEMAX){
    int last_idx;

    // ULLA debug_p1 = copyA(ciphertexta.a);
    // std::cout<<"debug_p1.data[i]-------------------------"<<std::endl;
    // for(int i=0;i<10;i++){
    //     std::cout<<debug_p1.data[i]<<std::endl;
    // }
    

    // addcipher(ciphertexta, ciphertextb);
    addmc2(ciphertexta, ciphertextb);

    if(outidx!=UNSIZEMAX){
        // polys0[outidx] = copyA(ciphertexta.a);
        // polys0[outidx + 1] = copyA(ciphertexta.b);
        polys0[outidx] = ciphertexta.a;
        polys0[outidx + 1] = ciphertexta.b;

        // std::cout<<"debug_polys0[outidx].data[i]-------------------------"<<std::endl;
        // for(int i=0;i<10;i++){
        //     std::cout<< polys0[outidx].data[i] <<std::endl;
        // }
        return outidx;  
    }
    // polys0[idx] = copyA(ciphertexta.a);
    // polys0[idx + 1] = copyA(ciphertexta.b);
    polys0[idx] = ciphertexta.a;
    polys0[idx + 1] = ciphertexta.b;

    last_idx = idx;
    idx += 2;
    return last_idx;
}

std::vector<::polytools::SealPoly> my_poly_compute(std::vector<Ciphertext> input_ctxt, std::vector<std::vector<int>> coefficient, std::vector<std::vector<int>> exp, SEALContext &context){
    std::cout << "entering into:  poly_compute" << std::endl;
    std::vector<std::vector<myCipher2>> var_for_mul;
    std::vector<myCipher2> var_for_add;
    std::vector<myCipher2> temp_val;
    // std::vector<myCipherText> var_a;

    int input_number = 0;
    for(int i=0;i<coefficient.size();i++){
        for(int j=0;j<coefficient[i].size();j++){
            if(input_number < coefficient[i][j]){
                input_number = coefficient[i][j];
            }
        }
    }
    input_number++;

    int index_for_output = input_number*2;
    int num = 0;
    if(coefficient.size() != exp.size()) {
        std::cout << "error: the size of coefficient is not equal to exp" << std::endl;
        std::vector<::polytools::SealPoly> empty_ULLA;
        return empty_ULLA;
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
    if(coefficient.size()==1 && coefficient[0].size()==1 && exp[0][0]==1){
        num += 2;
    }

    //num包含输出
    // std::cout << "num: " << num <<std::endl;
    // std::cout << "index_for_output: " << index_for_output <<std::endl;
    int num_var = input_number*2 + num;
    // std::cout << "num_var: " << num_var <<std::endl;

    //用于存储输入输出以及中间变量的值
    // std::vector<ULLA> polys = std::vector<ULLA>(num_var);
    vector<::polytools::SealPoly> polys = vector<::polytools::SealPoly>(num_var, polytools::SealPoly(context));
    int index = 0;
    int last_idx = index;

    // std::cout<<"input_ctxt: "<<input_ctxt.size()<<std::endl;

    for(int i = 0; i < input_number; i++) {
        // polys[index] = copyA(input_ctxt[i].a);
        polys[index] = polytools::SealPoly(context, input_ctxt[i], 0);
        index++;
        // polys[index] = copyA(input_ctxt[i].b);
        polys[index] = polytools::SealPoly(context, input_ctxt[i], 1);
        index++;
    }
    index += 2;
    // std::cout << "index begin: " << index <<std::endl;

    //如果没有加法
    if(coefficient.size() == 1) {
        //如果没有乘法
        if(coefficient[0].size() == 1) {
            if(exp[0][0] == 1) {
                myCipher2 mc = C_to_mC2(input_ctxt[coefficient[0][0]], context);
                // polys[index] = copyA(input_ctxt[coefficient[0][0]].a);
                polys[index] = mc.a;
                index++;
                // polys[index] = copyA(input_ctxt[coefficient[0][0]].b);
                polys[index] = mc.b;
                index++;
                last_idx = index_for_output;
            }else if(exp[0][0] == 2) {
                myCipher2 mc0 = C_to_mC2(input_ctxt[coefficient[0][0]], context);
                myCipher2 mc1 = C_to_mC2(input_ctxt[coefficient[0][0]], context);
                last_idx = poly_mul_cipher(mc0, mc1, index, polys, context, index_for_output);
                // last_idx = poly_mul_cipher(input_ctxt[coefficient[0][0]], input_ctxt[coefficient[0][0]], index, polys, relkey, index_for_output);
            }else {
                for(int i = 2; i <= exp[0][0]; i++) {
                    if(i == 2) {
                        myCipher2 mc0 = C_to_mC2(input_ctxt[coefficient[0][0]], context);
                        myCipher2 mc1 = C_to_mC2(input_ctxt[coefficient[0][0]], context);
                        last_idx = poly_mul_cipher(mc0, mc1, index, polys, context);
                        // last_idx = poly_mul_cipher(input_ctxt[coefficient[0][0]], input_ctxt[coefficient[0][0]], index, polys, relkey);
                    }else if(i != exp[0][0]) {
                        myCipher2 lmc = getMC2fromA(last_idx, polys);
                        myCipher2 mc = C_to_mC2(input_ctxt[coefficient[0][0]], context);
                        last_idx = poly_mul_cipher(mc, lmc, index, polys, context);
                        // myCipherText last_c = getCfromA(last_idx, polys);
                        // last_idx = poly_mul_cipher(input_ctxt[coefficient[0][0]], last_c, index, polys, relkey);
                    }else {
                        myCipher2 lmc = getMC2fromA(last_idx, polys);
                        myCipher2 mc = C_to_mC2(input_ctxt[coefficient[0][0]], context);
                        last_idx = poly_mul_cipher(mc, lmc, index, polys, context, index_for_output);
                        // myCipherText last_c = getCfromA(last_idx, polys);
                        // last_idx = poly_mul_cipher(input_ctxt[coefficient[0][0]], last_c, index, polys, relkey, index_for_output);
                    }
                }
            }
        }
            //如果有乘法
        else {
            for(int i = 0; i < coefficient[0].size(); i++) {
                //进行幂运算
                if (exp[0][i] == 1) {
                    myCipher2 mc = C_to_mC2(input_ctxt[coefficient[0][i]], context);
                    temp_val.push_back(mc);
                    // temp_val.push_back(input_ctxt[coefficient[0][i]]);
                } else if (exp[0][i] == 2) {
                    myCipher2 mc0 = C_to_mC2(input_ctxt[coefficient[0][i]], context);
                    myCipher2 mc1 = C_to_mC2(input_ctxt[coefficient[0][i]], context);
                    last_idx = poly_mul_cipher(mc0, mc1, index, polys, context);
                    temp_val.push_back(getMC2fromA(last_idx, polys));
                    // last_idx = poly_mul_cipher(input_ctxt[coefficient[0][i]], input_ctxt[coefficient[0][i]], index, polys, relkey);
                    // temp_val.push_back(getCfromA(last_idx, polys));
                } else {
                    for (int j = 2; j <= exp[0][i]; j++) {
                        if (j == 2) {
                            myCipher2 mc0 = C_to_mC2(input_ctxt[coefficient[0][i]], context);
                            myCipher2 mc1 = C_to_mC2(input_ctxt[coefficient[0][i]], context);
                            last_idx = poly_mul_cipher(mc0, mc1, index, polys, context);
                            // last_idx = poly_mul_cipher(input_ctxt[coefficient[0][i]], input_ctxt[coefficient[0][i]], index, polys, relkey);
                        } else if (j != exp[0][i]) {
                            myCipher2 lmc = getMC2fromA(last_idx, polys);
                            myCipher2 mc = C_to_mC2(input_ctxt[coefficient[0][i]], context);
                            last_idx = poly_mul_cipher(mc, lmc, index, polys, context);
                            // myCipherText last_c = getCfromA(last_idx, polys);
                            // last_idx = poly_mul_cipher(input_ctxt[coefficient[0][i]], last_c, index, polys, relkey);
                        } else {
                            myCipher2 lmc = getMC2fromA(last_idx, polys);
                            myCipher2 mc = C_to_mC2(input_ctxt[coefficient[0][i]], context);
                            last_idx = poly_mul_cipher(mc, lmc, index, polys, context);
                            temp_val.push_back(getMC2fromA(last_idx, polys));
                            // myCipherText last_c = getCfromA(last_idx, polys);
                            // last_idx = poly_mul_cipher(input_ctxt[coefficient[0][i]], last_c, index, polys, relkey);
                            // temp_val.push_back(getCfromA(last_idx, polys));
                        }
                    }
                }
            }
            //进行乘法运算
            if(temp_val.size() == 2) {
                last_idx = poly_mul_cipher(temp_val[0], temp_val[1], index, polys, context, index_for_output);
            }else {
                for(int j = 1; j < temp_val.size(); j++) {
                    if(j == 1) {
                        last_idx = poly_mul_cipher(temp_val[j], temp_val[j-1], index, polys, context);
                    }else if(j != temp_val.size() - 1) {
                        myCipher2 lmc = getMC2fromA(last_idx, polys);
                        last_idx = poly_mul_cipher(temp_val[j], lmc, index, polys, context);
                        // myCipherText last_c = getCfromA(last_idx, polys);
                        // last_idx = poly_mul_cipher(temp_val[j], last_c, index, polys, relkey);
                    }else {
                        myCipher2 lmc = getMC2fromA(last_idx, polys);
                        last_idx = poly_mul_cipher(temp_val[j], lmc, index, polys, context, index_for_output);
                        // myCipherText last_c = getCfromA(last_idx, polys);
                        // last_idx = poly_mul_cipher(temp_val[j], last_c, index, polys, relkey, index_for_output);
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
                            myCipher2 mc0 = C_to_mC2(input_ctxt[coefficient[i][j]], context);
                            myCipher2 mc1 = C_to_mC2(input_ctxt[coefficient[i][j]], context);
                            last_idx = poly_mul_cipher(mc0, mc1, index, polys, context);
                            // last_idx = poly_mul_cipher(input_ctxt[coefficient[i][j]], input_ctxt[coefficient[i][j]], index, polys, relkey);
                            if(exp[i][j] == 2){
                                temp_val.push_back(getMC2fromA(last_idx, polys));
                                // temp_val.push_back(getCfromA(last_idx, polys));
                            }
                        }
                        else if(k != exp[i][j]){
                            myCipher2 lmc = getMC2fromA(last_idx, polys);
                            myCipher2 mc = C_to_mC2(input_ctxt[coefficient[i][j]], context);
                            last_idx = poly_mul_cipher(lmc, mc, index, polys, context);
                            // myCipherText last_c = getCfromA(last_idx, polys);
                            // last_idx = poly_mul_cipher(last_c, input_ctxt[coefficient[i][j]], index, polys, relkey);
                        }
                        else {
                            myCipher2 lmc = getMC2fromA(last_idx, polys);
                            myCipher2 mc = C_to_mC2(input_ctxt[coefficient[i][j]], context);
                            last_idx = poly_mul_cipher(lmc, mc, index, polys, context);
                            temp_val.push_back(getMC2fromA(last_idx, polys));
                            // myCipherText last_c = getCfromA(last_idx, polys);
                            // last_idx = poly_mul_cipher(last_c, input_ctxt[coefficient[i][j]], index, polys, relkey);
                            // temp_val.push_back(getCfromA(last_idx, polys));
                        }
                    }
                }
                else{
                    myCipher2 mc = C_to_mC2(input_ctxt[coefficient[i][j]], context);
                    temp_val.push_back(mc);
                    // temp_val.push_back(input_ctxt[coefficient[i][j]]);
                }
            }
            var_for_mul.push_back(temp_val);
        }

        for(int i = 0; i < coefficient.size(); i++) {

            if(var_for_mul[i].size() == 0) {
                std::cout << i << "var_for_mul is 0" << "\t";
                continue;
            }
            if(var_for_mul[i].size() == 1) {
                var_for_add.push_back(var_for_mul[i][0]);
                continue;
            }
            for(int j = 1; j < var_for_mul[i].size(); j++) {
                if(j == 1 && var_for_mul[i].size() == 2) {
                    last_idx = poly_mul_cipher(var_for_mul[i][j], var_for_mul[i][j - 1], index, polys, context);
                    var_for_add.push_back(getMC2fromA(last_idx, polys));
                    // last_idx = poly_mul_cipher(var_for_mul[i][j], var_for_mul[i][j - 1], index, polys, relkey);
                    // var_for_add.push_back(getCfromA(last_idx, polys));
                }else if(j == 1 && var_for_mul[i].size() > 2){
                    last_idx = poly_mul_cipher(var_for_mul[i][j], var_for_mul[i][j - 1], index, polys, context);
                    // last_idx = poly_mul_cipher(var_for_mul[i][j], var_for_mul[i][j - 1], index, polys, relkey);
                }else if(j != var_for_mul[i].size() - 1){
                    myCipher2 lmc = getMC2fromA(last_idx, polys);
                    last_idx = poly_mul_cipher(lmc, var_for_mul[i][j], index, polys, context);
                    // myCipherText last_c = getCfromA(last_idx, polys);
                    // last_idx = poly_mul_cipher(last_c, var_for_mul[i][j], index, polys, relkey);
                }
                else if(j == var_for_mul[i].size() - 1) {
                    myCipher2 lmc = getMC2fromA(last_idx, polys);
                    last_idx = poly_mul_cipher(lmc, var_for_mul[i][j], index, polys, context);
                    var_for_add.push_back(getMC2fromA(last_idx, polys));
                    // last_idx = cipherText_poly_mul(poly, index, last_idx, var_for_mul[i][j]);
                    // var_for_add.push_back(last_idx);
                }
            }
        }
        // std::cout << std::endl;

        // if(no_aj){
        //     var_a = var_for_add;
        // }
        // else{
        //     for(int i=0; i<num_avar;i++){
        //         last_idx = cipherText_poly_mul(poly, index, var_for_add[i], i, true);
        //         var_a.push_back(last_idx);
        //         // poly = polys[var_for_add[i]];
        //         // poly.multiply_inplace(poly_as[i]);
        //         // apoly[i] = poly;
        //     }
        // }
        
        if(var_for_add.size() == 0) {
            std::cout << "var_for_add.size = 0" << std::endl;
        }else if(var_for_add.size() == 1) {
            std::cout << "var_for_add.size = 1" << std::endl;
        }else {
            for(int i = 1; i < var_for_add.size(); i++) {
                if(i == 1 && var_for_add.size() == 2){
                    last_idx = poly_add_cipher(var_for_add[i], var_for_add[i-1], index, polys, index_for_output);
                    // last_idx = cipherText_poly_add(poly, index, var_a[i], var_a[i-1], index_for_output);
                }else if(i == 1 && var_for_add.size() > 2){
                    last_idx = poly_add_cipher(var_for_add[i], var_for_add[i-1], index, polys);
                    // last_idx = cipherText_poly_add(poly, index, var_a[i], var_a[i-1]);
                }else if(i != var_for_add.size() - 1){
                    myCipher2 lmc = getMC2fromA(last_idx, polys);
                    last_idx = poly_add_cipher(var_for_add[i], lmc, index, polys);
                    // myCipherText last_c = getCfromA(last_idx, polys);
                    // last_idx = poly_add_cipher(var_for_add[i], last_c, index, polys);
                }else {
                    myCipher2 lmc = getMC2fromA(last_idx, polys);
                    last_idx = poly_add_cipher(var_for_add[i], lmc, index, polys, index_for_output);
                    // myCipherText last_c = getCfromA(last_idx, polys);
                    // last_idx = poly_add_cipher(var_for_add[i], last_c, index, polys, index_for_output);
                }
            }
        }
    }

    // int final_var_num = last_idx;
    std::cout << "exit: poly_compute" << std::endl;
    return polys;
}


std::vector<Ciphertext> my_read_file(std::string file_path, int read_num, SEALContext &context){


    // auto context_data0 = context.get_context_data(context.first_parms_id());
    // auto coeff_modulus0 = context_data0->parms().coeff_modulus();

    // for (size_t i = 0; i < coeff_modulus0.size(); ++i) {
    //     cout << "Coeff Modulus " << i << ": " << coeff_modulus0[i].value() << endl;
    // }

    auto encoder = CKKSEncoder(context);
    KeyGenerator keygen(context);
    auto secret_key = keygen.secret_key();
    PublicKey public_key;
    keygen.create_public_key(public_key);
    // RelinKeys relin_keys;
    // keygen.create_relin_keys(relin_keys);
    Encryptor encryptor(context, public_key);

    // auto tables =context.get_context_data(context.first_parms_id())->small_ntt_tables();
    size_t slot_count = encoder.slot_count();
    // vector<double> vs(slot_count);
    Plaintext ptxt;
    Ciphertext ctxt;
// Inputs
    // cout<<"slot_count: "<<slot_count<<endl;

    if(slot_count != N/2){
        cout<<"slot_count error-------------------------------------"<<endl;
    }

    // for(int i=0;i<slot_count;i++)
    // {
    //     vs[i]=i;
    // }

    double scale=pow(2.0, S_P);

    // encoder.encode(vs,scale,ptxt);
    // encryptor.encrypt(ptxt,ctxt);
    // for(int i = 0; i < ring_input_size/2; i++) {
    //     cipherVec.push_back(ctxt);
    // }
    
    // Ciphertext relin_key_ctxt=relin_keys.data()[0][0].data();

    // cout << "debug3" << endl;
    // relin_poly0 = new ::polytools::SealPoly(context, relin_key_ctxt, 0);
    // relin_poly1 = new ::polytools::SealPoly(context, relin_key_ctxt, 1);

    // cout<<"poly_coeff_count0 = " << relin_poly0->get_coeff_count() <<endl;
    // cout<<"poly_coeff_modulus_count0 = " << relin_poly0->get_coeff_modulus_count() <<endl;
    // cout<<"poly_data_size0 = " << relin_poly0->get_data_size() <<endl;

    
    // auto m0 = relin_poly0->get_coeff_modulus();
    // cout<<"poly_modulus:";
    // for(int i=0;i<m0.size();i++){
    //     cout<<m0[i].data() <<"\t"; 
    // }
    // cout<<endl;


    // auto context_data = context.get_context_data(context.first_parms_id());
    // auto coeff_modulus = context_data->parms().coeff_modulus();

    // for (size_t i = 0; i < coeff_modulus.size(); ++i) {
    //     cout << "Coeff Modulus " << i << ": " << coeff_modulus[i].value() << endl;
    // }


    std::vector<Ciphertext> cipher_inputs;
    vector<double> a(N/2);
    vector<double> la(N/2);
    int cnt;
    std::string line;
    std::ifstream fileA(file_path);

    std::uniform_int_distribution<> dist(0, N/2-1);
    std::uniform_real_distribution<> doubleDist(0.0, 1.0);
    bool flag = true;
    std::getline(fileA, line);
    for(int i=0;i<read_num;i++){
        // 读取a的值
        cnt = 0;
        
        if(flag){
            while(std::getline(fileA, line) && cnt < (N/2)){
                std::stringstream linestream(line);
                std::vector<std::string> tokens = splitLineStream(linestream, ',');
                a[cnt] = std::stod(tokens[1]);
                cnt++;
            }
            if(cnt< N/2){
                flag = false;
            }
            if(flag){
                if(i==0){
                    for(int j=0;j<N/2;j++){
                        la[j] = a[j];
                    }
                }
                // 编码获取两个列向量的编码结果
                // auto encodeVeca = encode(a);
                encoder.encode(a, scale, ptxt);


                // if(i==0){
                //     ::polytools::SealPoly ppl = polytools::SealPoly(context, ptxt, &(context.first_parms_id()));
                //     cout<<"poly_coeff_count0p = " << ppl.get_coeff_count() <<endl;
                //     cout<<"poly_coeff_modulus_count0p = " << ppl.get_coeff_modulus_count() <<endl;
                //     cout<<"poly_data_size0p = " << ppl.get_data_size() <<endl;

                //     ::polytools::SealPoly ppl2 = polytools::SealPoly(context, ptxt);
                //     cout<<"poly_coeff_count0p2 = " << ppl2.get_coeff_count() <<endl;
                //     cout<<"poly_coeff_modulus_count0p2 = " << ppl2.get_coeff_modulus_count() <<endl;
                //     cout<<"poly_data_size0p2 = " << ppl2.get_data_size() <<endl;


                //     auto context_data = context.get_context_data(context.first_parms_id());
                //     auto coeff_modulus = context_data->parms().coeff_modulus();

                //     for (size_t i = 0; i < coeff_modulus.size(); ++i) {
                //         cout << "Coeff Modulus " << i << ": " << coeff_modulus[i].value() << endl;
                //     }
                // }


                // 对编码结果进行加密
                // myCipherText ciphertexta = encrypt(encodeVeca, getpub());
                encryptor.encrypt(ptxt, ctxt);
                cipher_inputs.push_back(ctxt);
            }
            else{
                std::mt19937 gen(time(0));
                int radi = dist(gen);
                double radd = doubleDist(gen);
                la[radi] = radd;
                // auto encodeVeca = encode(la);
                encoder.encode(la, scale, ptxt);
                // myCipherText ciphertexta = encrypt(encodeVeca, getpub());
                encryptor.encrypt(ptxt, ctxt);
                cipher_inputs.push_back(ctxt);
            }
        }
        else{
            std::mt19937 gen(time(0));
            int radi = dist(gen);
            double radd = doubleDist(gen);
            la[radi] = radd;
            // auto encodeVeca = encode(la);
            encoder.encode(la, scale, ptxt);
            // myCipherText ciphertexta = encrypt(encodeVeca, getpub());
            encryptor.encrypt(ptxt, ctxt);
            cipher_inputs.push_back(ctxt);
        }

        ::polytools::SealPoly pt0 = ::polytools::SealPoly(context, ctxt, 0);
        ::polytools::SealPoly pt1 = ::polytools::SealPoly(context, ctxt, 1);

        if(pt0.get_coeff_modulus_count()!=LEN || pt1.get_coeff_modulus_count()!=LEN){
            cout<< "warring: LEN and coeff_modulus_count dont match!!" <<endl;
        }

    }
    fileA.close();

    // ::polytools::SealPoly poly00 = polytools::SealPoly(context, cipher_inputs[0], 0);

    // cout<<"poly_coeff_count0 = " << poly00.get_coeff_count() <<endl;
    // cout<<"poly_coeff_modulus_count0 = " << poly00.get_coeff_modulus_count() <<endl;
    // cout<<"poly_data_size0 = " << poly00.get_data_size() <<endl;


    // auto m1 = poly00.get_coeff_modulus();
    // cout<<"poly00_modulus:";
    // for(int i=0;i<m1.size();i++){
    //     cout<<m1[i].data() <<"\t"; 
    // }
    // cout<<endl;

    relin_poly0 = new ::polytools::SealPoly(context, ctxt, 0);
    relin_poly1 = new ::polytools::SealPoly(context, ctxt, 1);

    return cipher_inputs;
}

// std::vector<myCipherText> read_file(std::string file_path, int read_num){
//     std::vector<myCipherText> cipher_inputs;
//     double a[N/2];
//     double la[N/2];
//     int cnt;
//     std::string line;
//     std::ifstream fileA(file_path);

//     std::uniform_int_distribution<> dist(0, N/2-1);
//     std::uniform_real_distribution<> doubleDist(0.0, 1.0);
//     bool flag = true;
//     std::getline(fileA, line);
//     for(int i=0;i<read_num;i++){
//         // 读取a的值
//         cnt = 0;
        
//         if(flag){
//             while(std::getline(fileA, line) && cnt < (N/2)){
//                 std::stringstream linestream(line);
//                 std::vector<std::string> tokens = splitLineStream(linestream, ',');
//                 a[cnt] = std::stod(tokens[1]);
//                 cnt++;
//             }
//             if(cnt< N/2){
//                 flag = false;
//             }
//             if(flag){
//                 if(i==0){
//                     for(int j=0;j<N/2;j++){
//                         la[j] = a[j];
//                     }
//                 }
//                 // 编码获取两个列向量的编码结果
//                 auto encodeVeca = encode(a);
//                 // 对编码结果进行加密
//                 myCipherText ciphertexta = encrypt(encodeVeca, getpub());
//                 cipher_inputs.push_back(ciphertexta);
//             }
//             else{
//                 std::mt19937 gen(time(0));
//                 int radi = dist(gen);
//                 double radd = doubleDist(gen);
//                 la[radi] = radd;
//                 auto encodeVeca = encode(la);
//                 myCipherText ciphertexta = encrypt(encodeVeca, getpub());
//                 cipher_inputs.push_back(ciphertexta);
//             }
//         }
//         else{
//             std::mt19937 gen(time(0));
//             int radi = dist(gen);
//             double radd = doubleDist(gen);
//             la[radi] = radd;
//             auto encodeVeca = encode(la);
//             myCipherText ciphertexta = encrypt(encodeVeca, getpub());
//             cipher_inputs.push_back(ciphertexta);
//         }
//     }
//     fileA.close();
//     return cipher_inputs;
// }


std::vector<ULLA> polys2ULLAs(std::vector<::polytools::SealPoly> &polys){
    uint64_t size_p = polys.size();
    std::vector<ULLA> ullas(size_p);

    // cout<<"poly_coeff_count = " << polys[0].get_coeff_count() <<endl;
    // cout<<"poly_coeff_modulus_count = " << polys[0].get_coeff_modulus_count() <<endl;
    // cout<<"poly_data_size = " << polys[0].get_data_size() <<endl;
    
    for(uint64_t i=0;i<size_p;i++){
        for(std::size_t j=0;j<Inner_N;j++){
            ullas[i].data[j] = polys[i].get_data_at_idx(j);
        }
    }
    // cout<<"poly_debug " <<endl;

    return ullas;
}

myRelienKey popRelienKey(){
    ULLA r0, r1;
    for(size_t i=0;i<Inner_N;i++){
        r0.data[i] = relin_poly0->get_data_at_idx(i);
        r1.data[i] = relin_poly1->get_data_at_idx(i);
    }
    myRelienKey myrel = myRelienKey(r0.data, r1.data);
    delete relin_poly0;
    delete relin_poly1;
    return myrel;
}

int getCipherNum(std::string comp, std::string cal_type){
    int cnu = std::stoi(comp) >> 13;
    std::string mul_div = "-m";
    int dmm = DEVICE_MEMORY_MAX >> 13;
    if(cal_type==mul_div && cnu > dmm){
        cnu = dmm;
    }
    if(cnu<2){
        cnu = 2;
    }
    return cnu;
}

void writeULLA(std::vector<ULLA> p, std::string save_path, myRelienKey rk){
    int plen = p.size();
    unsigned long long a_size = plen*Inner_N + 2*Inner_N;
    std::vector<unsigned long long> a(a_size);
    unsigned long long cnt = 0;

    // std::cout<<"plen: "<<plen<<std::endl;
    // std::cout<<"========================================================="<<std::endl;
    // for(int i=0;i<10;i++){
    //     std::cout<< p[3].data[Inner_N-10+i] <<std::endl;
    // }
    // for(int i=0;i<10;i++){
    //     std::cout<< p[4].data[i] <<std::endl;
    // }
    // std::cout<<"----------------------------------------------------------"<<std::endl;

    for(int i=0;i<plen;i++){
        for(int j=0;j<Inner_N;j++){
            a[cnt] = p[i].data[j];
            cnt++;
        }
    }
    // std::cout<<"cnt0:"<<cnt/Inner_N<<std::endl;
    ULLA rk0 = copyA(rk.a);
    for(int j=0;j<Inner_N;j++){
        a[cnt] = rk0.data[j];
        cnt++;
    }
    ULLA rk1 = copyA(rk.b);
    for(int j=0;j<Inner_N;j++){
        a[cnt] = rk1.data[j];
        cnt++;
    }
    // std::cout<<"cnt1:"<<cnt/Inner_N<<std::endl;

    
    // for(int i=0;i<20;i++){
    //     std::cout<< a[i-10 + Inner_N*(plen-2)] <<std::endl;
    // }
    // std::cout<<"----------------------------------------------------------"<<std::endl;

    std::ofstream outFile(save_path, std::ios::binary);
    if (!outFile) {
        std::cout << "无法打开文件!" << std::endl;
        return;
    }

    // 写入数据到文件
    outFile.write(reinterpret_cast<char*>(&a_size), sizeof(unsigned long long));
    outFile.write(reinterpret_cast<char*>(&a[0]), a_size * sizeof(unsigned long long));
    // 关闭文件
    outFile.close();
    std::cout << "The calculation result has been written into the binary file: "<< save_path << std::endl;
}

int main(int argc,char** argv){
    std::string poly_type = argv[1];
    std::string compute_num = argv[2];
    std::string filenameA = argv[3];
    std::string filenameB = argv[4];

    std::string add_sub = "-a";
    std::string mul_div = "-m";

    std::vector<std::vector<int>> coefficient, exp;

    // int Cipher_number = getCipherNum(compute_num, poly_type);
    int Cipher_number = 1 + std::stoi(compute_num);

    if(poly_type == add_sub){
        for(int i=0;i<Cipher_number;i++){
            coefficient.push_back({i});
            exp.push_back({1});
        }
    }else if(poly_type == mul_div){
        coefficient = {{0}};
        exp = {{Cipher_number}};
    }else{
        std::cout<<"Illegal input!"<<std::endl;
        return 1;
    }

    std::cout<<"init"<<std::endl;
    // 初始化（生成公钥私钥对,编码器加密器）
    SEALContext context = myInit0(N);

    std::cout<<"read begin"<<std::endl;
    std::vector<Ciphertext> inputs = my_read_file(filenameA , Cipher_number, context);
    std::cout<<"read finish"<<std::endl;

    // std::cout<<"poly_compute"<<std::endl;
    std::vector<::polytools::SealPoly> polys = my_poly_compute(inputs, coefficient, exp, context);

    std::vector<ULLA> ullas = polys2ULLAs(polys);

    myRelienKey relien_key = popRelienKey();
    std::cout<<"write begin"<<std::endl;
    writeULLA(ullas, filenameB, relien_key);
    // std::cout<<"writeULLA out"<<std::endl;

    return 0;
}