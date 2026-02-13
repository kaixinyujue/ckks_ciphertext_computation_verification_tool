#include <iostream>
#include <fstream>
#include <random>
#include <string>

int main(int argc, char* argv[]) {
    // 检查命令行参数的数量
    if (argc != 3) {
        std::cerr << "使用方法: " << argv[0] << " <数量> <文件路径>" << std::endl;
        return 1;
    }

    // 从命令行读取数量和文件路径
    int count = std::stoi(argv[1]);
    std::string filePath = argv[2];

    // 创建一个随机数引擎
    std::random_device rd;
    std::mt19937 gen(rd());
    
    // 创建一个均匀分布，生成0到1之间的随机浮点数
    std::uniform_real_distribution<> dis(0.0, 1.0);
    
    // 打开指定的文件用于写入
    std::ofstream file(filePath);
    
    if (!file.is_open()) {
        std::cerr << "无法打开文件：" << filePath << std::endl;
        return 1;
    }
    
    // 生成并写入指定数量的随机浮点数
    for (int i = 1; i <= count; ++i) {
        double random_number = dis(gen);
        file << i << "," << random_number << std::endl;
    }
    
    // 关闭文件
    file.close();
    
    std::cout << count << " random numbers have been written to the file: " << filePath << std::endl;
    
    return 0;
}