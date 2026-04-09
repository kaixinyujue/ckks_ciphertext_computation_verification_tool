//
// test on 2025/02/15.
//
#include <iostream>
#include <fstream>
#include <filesystem>
#include <vector>
#include <random>
#include <string>


#define Inner_N 12288

using namespace std;

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

void delcrash(string filename){
    std::string sl_path0 = "vbuff/a" + retainNumbers(filename);
    std::string sl_path1 = "vbuff/m" + retainNumbers(filename);
    std::filesystem::path dir_path0 = sl_path0;
    std::filesystem::path dir_path1 = sl_path1;
    if(std::filesystem::exists(dir_path0) && std::filesystem::is_directory(dir_path0)){
        try {
            std::filesystem::remove_all(dir_path0);
        } catch (const std::filesystem::filesystem_error& e) {
            std::cerr << "file is occupied, " << e.what() << std::endl;
        }
    }
    if(std::filesystem::exists(dir_path1) && std::filesystem::is_directory(dir_path1)){
        try {
            std::filesystem::remove_all(dir_path1);
        } catch (const std::filesystem::filesystem_error& e) {
            std::cerr << "file is occupied, " << e.what() << std::endl;
        }
    }
}

void destroy_csv(vector<unsigned long long> &data0){
    size_t data_size = data0.size();
    size_t slnum = data_size/Inner_N;
    // size_t d = Inner_N/2;

    // // size_t rim = slnum/64;

    // std::random_device rd; // 随机设备，用于生成种子
    // std::mt19937 gen(rd());

    // // std::uniform_int_distribution<size_t> dist1(0, slnum - 1);

    // // vector<size_t> rinms;
    // // for(size_t i=0;i<rim;i++){
    // //     size_t rdmn = dist1(gen);
    // //     rinms.push_back(rdmn);
    // // }

    // std::uniform_int_distribution<size_t> dist2(0, d-1);
    // size_t desid = dist2(gen);
    // std::uniform_int_distribution<unsigned long long> dist3(0, 4294967295);
    // unsigned long long desda = dist3(gen);

    // for(size_t i=0;i<slnum;i++){
    //     if((i+1)%64==0){
    //         continue;
    //     }
    //     data0[i*Inner_N + desid] = desda;
    //     desid = (desid*7 + 1123) % d;
    //     desda = (desda*89 + 101399) % 4294967296;

    //     data0[i*Inner_N + d + desid] = desda;
    //     desid = (desid*11 + 1327) % d;
    //     desda = (desda*97 + 100511) % 4294967296;
    // }

    vector<unsigned long long> tmp(Inner_N);
    // for(int i=0;i<Inner_N;i++){
    //     tmp[i] = data0[i];
    // }
    // data0.erase(data0.begin(), data0.begin()+Inner_N);

    // for(int i=0;i<Inner_N;i++){
    //     data0.push_back(tmp[i]);
    // }

    size_t i = 1, j = slnum - 2;
    while (i<j){
        std::copy(data0.begin()+i*Inner_N, data0.begin()+(i+1)*Inner_N, tmp.begin());
        std::copy(data0.begin()+j*Inner_N, data0.begin()+(j+1)*Inner_N, data0.begin()+i*Inner_N);
        std::copy(tmp.begin(), tmp.begin()+Inner_N, data0.begin()+j*Inner_N);
        i++;
        j--;
    }

    if(slnum==3){
        std::copy(data0.begin()+Inner_N, data0.begin()+2*Inner_N, tmp.begin());
        std::copy(data0.begin()+2*Inner_N, data0.begin()+3*Inner_N, data0.begin()+Inner_N);
        std::copy(tmp.begin(), tmp.begin()+Inner_N, data0.begin()+2*Inner_N);
    }
    else if(slnum<3){
        cout<<"data_size is too little!"<<endl;
    }

}

void dese(){
    std::string filename = "e_test.txt";
    std::ofstream outFile(filename);
    if (!outFile.is_open()) {
        std::cerr << "无法打开文件 " << filename << std::endl;
        return;
    }
    outFile << "e_test" << std::endl;
    outFile.close();
}

void save_csv(vector<unsigned long long> &data1, string save_path){
    std::ofstream outFile(save_path, std::ios::binary);
    if (!outFile) {
        std::cout << "无法打开文件!" << std::endl;
        return;
    }
    unsigned long long a_size = data1.size();
    // 写入数据到文件
    outFile.write(reinterpret_cast<char*>(&a_size), sizeof(unsigned long long));
    outFile.write(reinterpret_cast<char*>(&data1[0]), a_size * sizeof(unsigned long long));
    // 关闭文件
    outFile.close();
}

int main(int argc,char** argv) {
    std::string filenameA;
    std::string filenameB;
    if(argc==2){
        filenameA = argv[1];
        filenameB = argv[1];
    }else if(argc==3){
        filenameA = argv[1];
        filenameB = argv[2];
    }else{
        cout << "arg error!"<<endl;
        return 1;
    }

    if(filenameA=="-e"){
        dese();
        cout << "Tampering completed."<< endl;
        return 0;
    }

    delcrash(filenameA);

    vector<unsigned long long> data = readCSV(filenameA);

    destroy_csv(data);

    save_csv(data, filenameB);
    
    if((data.size()/Inner_N)>=3){
        cout << "The data file: " << filenameA << " has been tampered."<< endl;
    }
    return 0;
}