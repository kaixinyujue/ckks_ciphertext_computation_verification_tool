#include "library.cuh"
#include <cstdio>
#include <fstream>
#include <sstream>
#include <iostream>
#include <vector>
#include <random>
#include <string>
#include <algorithm>

#define N 4096
#define LEN 4
#define S_P 50
#define Inner_N 16384
#define UNSIZEMAX 32767
#define DEVICE_MEMORY_MAX 50000000


typedef struct ULLArray {
    unsigned long long data[Inner_N];
}ULLA;

ULLA copyA(unsigned long long *a){
    ULLA arr;
    unsigned long long ah[Inner_N];
    cudaMemcpy(ah, a, Inner_N * sizeof(unsigned long long), cudaMemcpyDeviceToHost);
    for(int i=0;i<Inner_N;i++){
        arr.data[i] = ah[i];
    }
    return arr;
}
void copyB(cipherText &a, ULLA b){
    unsigned long long *d_data0;
    unsigned long long *d_data1;
    cudaMalloc((void**)&d_data0, Inner_N * sizeof(unsigned long long));
    cudaMalloc((void**)&d_data1, Inner_N * sizeof(unsigned long long));
    cudaMemcpy(d_data0, b.data, Inner_N * sizeof(unsigned long long), cudaMemcpyHostToDevice);
    cudaMemcpy(d_data1, b.data, Inner_N * sizeof(unsigned long long), cudaMemcpyHostToDevice);
    a.set(d_data0, d_data1);
}
void copyC(cipherText &a, cipherText b){
    unsigned long long ah0[Inner_N];
    unsigned long long ah1[Inner_N];
    cudaMemcpy(ah0, b.a, Inner_N * sizeof(unsigned long long), cudaMemcpyDeviceToHost);
    cudaMemcpy(ah1, b.b, Inner_N * sizeof(unsigned long long), cudaMemcpyDeviceToHost);

    unsigned long long *d_data0;
    unsigned long long *d_data1;
    cudaMalloc((void**)&d_data0, Inner_N * sizeof(unsigned long long));
    cudaMalloc((void**)&d_data1, Inner_N * sizeof(unsigned long long));
    cudaMemcpy(d_data0, ah0, Inner_N * sizeof(unsigned long long), cudaMemcpyHostToDevice);
    cudaMemcpy(d_data1, ah1, Inner_N * sizeof(unsigned long long), cudaMemcpyHostToDevice);

    a.set(d_data0, d_data1);
}
void copyR(cipherText &a, relienKey b){
    unsigned long long ah0[Inner_N];
    unsigned long long ah1[Inner_N];
    cudaMemcpy(ah0, b.a, Inner_N * sizeof(unsigned long long), cudaMemcpyDeviceToHost);
    cudaMemcpy(ah1, b.b, Inner_N * sizeof(unsigned long long), cudaMemcpyDeviceToHost);

    unsigned long long *d_data0;
    unsigned long long *d_data1;
    cudaMalloc((void**)&d_data0, Inner_N * sizeof(unsigned long long));
    cudaMalloc((void**)&d_data1, Inner_N * sizeof(unsigned long long));
    cudaMemcpy(d_data0, ah0, Inner_N * sizeof(unsigned long long), cudaMemcpyHostToDevice);
    cudaMemcpy(d_data1, ah1, Inner_N * sizeof(unsigned long long), cudaMemcpyHostToDevice);

    a.set(d_data0, d_data1);
}

std::vector<std::string> splitLineStream(std::stringstream& linestream, char delimiter) {
    std::vector<std::string> result;
    std::string item;

    while (std::getline(linestream, item, delimiter)) {
        result.push_back(item);
    }

    return result;
}

cipherText getCfromA(int idx, std::vector<ULLA> &polys0){
    cipherText c;
    unsigned long long *d_data0;
    unsigned long long *d_data1;
    cudaMalloc((void**)&d_data0, Inner_N * sizeof(unsigned long long));
    cudaMalloc((void**)&d_data1, Inner_N * sizeof(unsigned long long));
    cudaMemcpy(d_data0, polys0[idx].data, Inner_N * sizeof(unsigned long long), cudaMemcpyHostToDevice);
    cudaMemcpy(d_data1, polys0[idx+1].data, Inner_N * sizeof(unsigned long long), cudaMemcpyHostToDevice);
    c.set(d_data0, d_data1);
    return c;
}

int poly_mul_cipher(cipherText ciphertexta, cipherText ciphertextb, int &idx, std::vector<ULLA> &polys0, relienKey relkey, int outidx=UNSIZEMAX){
    int last_idx;
    cipherText c0, c1, a, b;
    copyC(a, ciphertexta);
    copyC(b, ciphertextb);
    c0 = mulPlain_lazy(a, b.a);
    // mulPlain_new1_lazy(c0, a, b.a);
    copyC(a, ciphertexta);
    copyC(b, ciphertextb);
    c1 = mulPlain_lazy(a, b.b);
    // mulPlain_new1_lazy(c1, a, b.b);
    // auto c0 = mulPlain_lazy(ciphertexta,ciphertextb.a);
    // auto c1 = mulPlain_lazy(ciphertexta,ciphertextb.b);
    polys0[idx] = copyA(c0.a);
    polys0[idx + 1] = copyA(c0.b);
    polys0[idx + 2] = copyA(c1.a);
    polys0[idx + 3] = copyA(c1.b);

    std::swap(c0.a,c0.b);
    addPlain(c0,c1.a);
    polys0[idx + 4] = copyA(c0.a);
    
    cipherText tmprel;
    copyR(tmprel, relkey);

    copyB(c1, polys0[idx + 3]);

    c0 = mulPlain_lazy(tmprel, c1.b);
    // mulPlain_new1_lazy(c0, tmprel, c1.b);

    polys0[idx + 5] = copyA(c0.a);
    polys0[idx + 6] = copyA(c0.b);

    if(outidx!=UNSIZEMAX){
        copyB(c1, polys0[idx]);
        addPlain(c1, c0.a);
        polys0[outidx] = copyA(c1.a);

        copyB(c1, polys0[idx + 4]);
        addPlain(c1, c0.b);
        polys0[outidx + 1] = copyA(c1.a);

        idx += 7;
        return outidx;
    }
    copyB(c1, polys0[idx]);
    addPlain(c1, c0.a);
    polys0[idx + 7] = copyA(c1.a);

    copyB(c1, polys0[idx + 4]);
    addPlain(c1, c0.b);
    polys0[idx + 8] = copyA(c1.a);

    last_idx = idx + 7;
    idx += 9;
    return last_idx;
}

int poly_add_cipher(cipherText ciphertexta, cipherText ciphertextb, int &idx, std::vector<ULLA> &polys0, int outidx=UNSIZEMAX){
    int last_idx;


    // ULLA debug_p1 = copyA(ciphertexta.a);
    // std::cout<<"debug_p1.data[i]-------------------------"<<std::endl;
    // for(int i=0;i<10;i++){
    //     std::cout<<debug_p1.data[i]<<std::endl;
    // }
    

    addcipher(ciphertexta, ciphertextb);
    if(outidx!=UNSIZEMAX){
        polys0[outidx] = copyA(ciphertexta.a);
        polys0[outidx + 1] = copyA(ciphertexta.b);
        // std::cout<<"debug_polys0[outidx].data[i]-------------------------"<<std::endl;
        // for(int i=0;i<10;i++){
        //     std::cout<< polys0[outidx].data[i] <<std::endl;
        // }
        return outidx;  
    }
    polys0[idx] = copyA(ciphertexta.a);
    polys0[idx + 1] = copyA(ciphertexta.b);

    last_idx = idx;
    idx += 2;
    return last_idx;
}

std::vector<ULLA> poly_compute(std::vector<cipherText> input_ctxt, relienKey relkey,std::vector<std::vector<int>> coefficient, std::vector<std::vector<int>> exp){
    std::cout << "entering into:  poly_compute" << std::endl;
    std::vector<std::vector<cipherText>> var_for_mul;
    std::vector<cipherText> var_for_add;
    std::vector<cipherText> temp_val;
    // std::vector<cipherText> var_a;

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
        std::vector<ULLA> empty_ULLA;
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
    std::vector<ULLA> polys = std::vector<ULLA>(num_var);
    int index = 0;
    int last_idx = index;

    // std::cout<<"input_ctxt: "<<input_ctxt.size()<<std::endl;

    for(int i = 0; i < input_number; i++) {
        polys[index] = copyA(input_ctxt[i].a);
        index++;
        polys[index] = copyA(input_ctxt[i].b);
        index++;
    }
    index += 2;
    // std::cout << "index begin: " << index <<std::endl;

    //如果没有加法
    if(coefficient.size() == 1) {
        //如果没有乘法
        if(coefficient[0].size() == 1) {
            if(exp[0][0] == 1) {
                polys[index] = copyA(input_ctxt[coefficient[0][0]].a);
                index++;
                polys[index] = copyA(input_ctxt[coefficient[0][0]].b);
                index++;
                last_idx = index_for_output;
            }else if(exp[0][0] == 2) {
                last_idx = poly_mul_cipher(input_ctxt[coefficient[0][0]], input_ctxt[coefficient[0][0]], index, polys, relkey, index_for_output);
                // last_idx = cipherText_poly_mul(poly, index, coefficient[0][0]*2, coefficient[0][0]*2, false, index_for_output);
            }else {
                for(int i = 2; i <= exp[0][0]; i++) {
                    if(i == 2) {
                        last_idx = poly_mul_cipher(input_ctxt[coefficient[0][0]], input_ctxt[coefficient[0][0]], index, polys, relkey);
                        // last_idx = cipherText_poly_mul(poly, index, coefficient[0][0]*2, coefficient[0][0]*2);
                    }else if(i != exp[0][0]) {
                        cipherText last_c = getCfromA(last_idx, polys);
                        last_idx = poly_mul_cipher(input_ctxt[coefficient[0][0]], last_c, index, polys, relkey);
                        // last_idx = cipherText_poly_mul(poly, index, coefficient[0][0]*2, last_idx);
                    }else {
                        cipherText last_c = getCfromA(last_idx, polys);
                        last_idx = poly_mul_cipher(input_ctxt[coefficient[0][0]], last_c, index, polys, relkey, index_for_output);
                        // last_idx = cipherText_poly_mul(poly, index, coefficient[0][0]*2, last_idx, false, index_for_output);
                    }
                }
            }
        }
            //如果有乘法
        else {
            for(int i = 0; i < coefficient[0].size(); i++) {
                //进行幂运算
                if (exp[0][i] == 1) {
                    temp_val.push_back(input_ctxt[coefficient[0][i]]);
                } else if (exp[0][i] == 2) {
                    last_idx = poly_mul_cipher(input_ctxt[coefficient[0][i]], input_ctxt[coefficient[0][i]], index, polys, relkey);
                    temp_val.push_back(getCfromA(last_idx, polys));
                    // last_idx = cipherText_poly_mul(poly, index, coefficient[0][i]*2, coefficient[0][i]*2);
                    // temp_val.push_back(last_idx);
                } else {
                    for (int j = 2; j <= exp[0][i]; j++) {
                        if (j == 2) {
                            last_idx = poly_mul_cipher(input_ctxt[coefficient[0][i]], input_ctxt[coefficient[0][i]], index, polys, relkey);
                            // last_idx = cipherText_poly_mul(poly, index, coefficient[0][i]*2, coefficient[0][i]*2);
                        } else if (j != exp[0][i]) {
                            cipherText last_c = getCfromA(last_idx, polys);
                            last_idx = poly_mul_cipher(input_ctxt[coefficient[0][i]], last_c, index, polys, relkey);
                            // last_idx = cipherText_poly_mul(poly, index, coefficient[0][i]*2, last_idx);
                        } else {
                            cipherText last_c = getCfromA(last_idx, polys);
                            last_idx = poly_mul_cipher(input_ctxt[coefficient[0][i]], last_c, index, polys, relkey);
                            temp_val.push_back(getCfromA(last_idx, polys));
                            // last_idx = cipherText_poly_mul(poly, index, coefficient[0][i]*2, last_idx);
                            // temp_val.push_back(last_idx);
                        }
                    }
                }
            }
            //进行乘法运算
            if(temp_val.size() == 2) {
                last_idx = poly_mul_cipher(temp_val[0], temp_val[1], index, polys, relkey, index_for_output);
                // last_idx = cipherText_poly_mul(poly, index, temp_val[0], temp_val[1], false, index_for_output);
            }else {
                for(int j = 1; j < temp_val.size(); j++) {
                    if(j == 1) {
                        last_idx = poly_mul_cipher(temp_val[j], temp_val[j-1], index, polys, relkey);
                        // last_idx = cipherText_poly_mul(poly, index, temp_val[j], temp_val[j-1]);
                    }else if(j != temp_val.size() - 1) {
                        cipherText last_c = getCfromA(last_idx, polys);
                        last_idx = poly_mul_cipher(temp_val[j], last_c, index, polys, relkey);
                        // last_idx = cipherText_poly_mul(poly, index, temp_val[j], last_idx);
                    }else {
                        cipherText last_c = getCfromA(last_idx, polys);
                        last_idx = poly_mul_cipher(temp_val[j], last_c, index, polys, relkey, index_for_output);
                        // last_idx = cipherText_poly_mul(poly, index, temp_val[j], last_idx, false, index_for_output);
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
                            last_idx = poly_mul_cipher(input_ctxt[coefficient[i][j]], input_ctxt[coefficient[i][j]], index, polys, relkey);
                            // last_idx = cipherText_poly_mul(poly, index, coefficient[i][j]*2, coefficient[i][j]*2);
                            if(exp[i][j] == 2){
                                temp_val.push_back(getCfromA(last_idx, polys));
                                // temp_val.push_back(last_idx);
                            }
                        }
                        else if(k != exp[i][j]){
                            cipherText last_c = getCfromA(last_idx, polys);
                            last_idx = poly_mul_cipher(last_c, input_ctxt[coefficient[i][j]], index, polys, relkey);
                            // last_idx = cipherText_poly_mul(poly, index, last_idx, coefficient[i][j]*2);
                        }
                        else {
                            cipherText last_c = getCfromA(last_idx, polys);
                            last_idx = poly_mul_cipher(last_c, input_ctxt[coefficient[i][j]], index, polys, relkey);
                            temp_val.push_back(getCfromA(last_idx, polys));
                            // last_idx = cipherText_poly_mul(poly, index, last_idx, coefficient[i][j]*2);
                            // temp_val.push_back(last_idx);
                        }
                    }
                }
                else{
                    temp_val.push_back(input_ctxt[coefficient[i][j]]);
                    // temp_val.push_back(coefficient[i][j]*2);
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
                    last_idx = poly_mul_cipher(var_for_mul[i][j], var_for_mul[i][j - 1], index, polys, relkey);
                    var_for_add.push_back(getCfromA(last_idx, polys));
                    // last_idx = cipherText_poly_mul(poly, index, var_for_mul[i][j], var_for_mul[i][j - 1]);
                    // var_for_add.push_back(last_idx);
                }else if(j == 1 && var_for_mul[i].size() > 2){
                    last_idx = poly_mul_cipher(var_for_mul[i][j], var_for_mul[i][j - 1], index, polys, relkey);
                    // last_idx = cipherText_poly_mul(poly, index, var_for_mul[i][j], var_for_mul[i][j - 1]);
                }else if(j != var_for_mul[i].size() - 1){
                    cipherText last_c = getCfromA(last_idx, polys);
                    last_idx = poly_mul_cipher(last_c, var_for_mul[i][j], index, polys, relkey);
                    // last_idx = cipherText_poly_mul(poly, index, last_idx, var_for_mul[i][j]);
                }
                else if(j == var_for_mul[i].size() - 1) {
                    cipherText last_c = getCfromA(last_idx, polys);
                    last_idx = poly_mul_cipher(last_c, var_for_mul[i][j], index, polys, relkey);
                    var_for_add.push_back(getCfromA(last_idx, polys));
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
                    cipherText last_c = getCfromA(last_idx, polys);
                    last_idx = poly_add_cipher(var_for_add[i], last_c, index, polys);
                    // last_idx = cipherText_poly_add(poly, index, var_a[i], last_idx);
                }else {
                    cipherText last_c = getCfromA(last_idx, polys);
                    last_idx = poly_add_cipher(var_for_add[i], last_c, index, polys, index_for_output);
                    // last_idx = cipherText_poly_add(poly, index, var_a[i], last_idx, index_for_output);
                }
            }
        }
    }

    // int final_var_num = last_idx;
    std::cout << "exit: poly_compute" << std::endl;
    return polys;
}

std::vector<cipherText> read_file(std::string file_path, int read_num){
    std::vector<cipherText> cipher_inputs;
    double a[N/2];
    double la[N/2];
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
                auto encodeVeca = encode(a);
                // 对编码结果进行加密
                cipherText ciphertexta = encrypt(encodeVeca, getpub());
                cipher_inputs.push_back(ciphertexta);
            }
            else{
                std::mt19937 gen(time(0));
                int radi = dist(gen);
                double radd = doubleDist(gen);
                la[radi] = radd;
                auto encodeVeca = encode(la);
                cipherText ciphertexta = encrypt(encodeVeca, getpub());
                cipher_inputs.push_back(ciphertexta);
            }
        }
        else{
            std::mt19937 gen(time(0));
            int radi = dist(gen);
            double radd = doubleDist(gen);
            la[radi] = radd;
            auto encodeVeca = encode(la);
            cipherText ciphertexta = encrypt(encodeVeca, getpub());
            cipher_inputs.push_back(ciphertexta);
        }
    }
    fileA.close();
    return cipher_inputs;
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

void writeULLA(std::vector<ULLA> p, std::string save_path, relienKey rk){
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

    int Cipher_number = getCipherNum(compute_num, poly_type);

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
    double scale = 1llu << S_P;
    // 初始化（生成公钥私钥对,编码器加密器）
    init(N/2,scale,LEN); 

    std::cout<<"read begin"<<std::endl;
    std::vector<cipherText> inputs = read_file(filenameA , Cipher_number);
    std::cout<<"read finish"<<std::endl;

    
    relienKey relien_key = getrelien_simple();
    // std::cout<<"poly_compute"<<std::endl;
    std::vector<ULLA> polys = poly_compute(inputs, relien_key, coefficient, exp);

    std::cout<<"write begin"<<std::endl;
    writeULLA(polys, filenameB, relien_key);
    // std::cout<<"writeULLA out"<<std::endl;

    return 0;
}