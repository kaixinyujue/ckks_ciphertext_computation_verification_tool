# A verification scheme for the correctness of ckks homomorphic encryption computation based on SNARK
 To address trustworthiness requirements in such outsourcing scenarios, SNARK (Succinct Non-interactive Argument of Knowledge) technology in verifiable computing enables verification of computation correctness while preserving user privacy.
This scheme splits the input encrypted computation function into atomic operations, allowing the R1CS constraint circuit generated during a single trusted setup to be reused across multiple computations.This significantly reduces the overall size of the constraint circuit and lowers the time overhead of the Prove step compared to traditional SNARK schemes.


## Comming Soon

## Build
```
git clone https://github.com/kaixinyujue/ckks_ciphertext_computation_verification_tool.git
cd ckks_ciphertext_computation_verification_tool
mkdir build
cd build
cmake ..
make
```


---


# 基于SNARK的ckks同态加密计算正确性验证方案
针对外包场景下的可信性需求，可验证计算中的 SNARK 技术能够在保护用户隐私的同时验证计算结果的正确性。
本方案采用新颖的计算函数拆分与约束电路复用技术，将输入的密文计算函数拆分为原子运算，使一次初始化生成的R1CS约束电路可以重复使用，减小了总约束电路的规模，降低了传统SNARK方案中Prove步骤的时间开销。

## 敬请期待

## 编译
```
git clone https://github.com/kaixinyujue/ckks_ciphertext_computation_verification_tool.git
cd ckks_ciphertext_computation_verification_tool
mkdir build
cd build
cmake ..
make
```