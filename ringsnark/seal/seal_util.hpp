#ifndef RINGSNARK_SEAL_UTIL_HPP
#define RINGSNARK_SEAL_UTIL_HPP

#include <iostream>

#include "seal/seal.h"

using namespace std;
using namespace seal;
/***
 *
 * @param poly_modulus_degree           degree of the outer FHE scheme
 * @param inner_poly_modulus_degree     degree of the inner FHE schemes, used
 * inside the ZKP
 * @return a `vector<Modulus>' that has the same bit size as
 * `CoeffModulus::BFVDefault(poly_modulus_degree)', but such that each for each
 * sub-modulus q_i, q_i = 1 mod 2*inner_poly_modulus_degree. This guarantees
 * that the batching optimization can be used for the ZKP scheme.
 */
vector<seal::Modulus> default_double_batching_modulus(
    const size_t poly_modulus_degree, const size_t inner_poly_modulus_degree) {
  assert(inner_poly_modulus_degree >= poly_modulus_degree);
  auto default_modulus = CoeffModulus::BFVDefault(poly_modulus_degree);
  vector<int> bit_sizes(default_modulus.size());
  for (size_t i = 0; i < default_modulus.size(); i++) {
    bit_sizes[i] = default_modulus[i].bit_count();
  }

  vector<Modulus> coeff_modulus = CoeffModulus::Create(
      inner_poly_modulus_degree,
      bit_sizes);  // Will be batching-friendly for inner scheme

  return coeff_modulus;
}
vector<int> enc_modulus (vector<seal::Modulus> encode_mod, const size_t enc_degree,const size_t encode_degree) {
    int max_count_enc=CoeffModulus::MaxBitCount(enc_degree);
    int max_count_encode=CoeffModulus::MaxBitCount(encode_degree);
    // cout<<"max_count_enc"<<max_count_enc<<endl;
    // cout<<"max_count_encode"<<max_count_encode<<endl;
    int count_encode=encode_mod.size();
    vector<int> encode_bits(count_encode);
    vector<int> enc_bits;
    //编码位数
    int bits_count_enc=0;
    // cout<<"count_encode "<<count_encode<<endl;
    for(int i=0;i<count_encode;i++){
        encode_bits[i]=int(log2(encode_mod[i].value())+1);
        // cout<<"encode_bits"<<i<<": "<<encode_bits[i]<<endl;
        enc_bits.push_back(encode_bits[i]);
        enc_bits.push_back(encode_bits[i]);
        bits_count_enc+=encode_bits[i];
    }
    enc_bits.push_back(max_count_encode-bits_count_enc);
    enc_bits.push_back(max_count_encode-bits_count_enc);
//    int rest_bits=max_count_enc-max_count_encode;
//    int bit=encode_bits[count_encode-1]+5;
//    while(bit>=60){
//        bit=bit-1;
//    }
//    int rest_count=rest_bits/(bit);
//    //
//    int count=0;
//    for(int i=0;i<=rest_count-1;i++){
//        enc_bits.push_back(bit);
//        cout<<"rest_bits"<<i<<": "<<bit<<endl;
//        count++;
//    }
//    enc_bits.push_back(rest_bits-bit*count);
    return enc_bits;
}
void print_params(const EncryptionParameters parms,
                  bool throw_on_invalid = true) {
  const SEALContext context(parms);
  cout << "[PARAM] Parameter validation (" << context.parameter_error_name()
       << "): " << context.parameter_error_message() << endl;
  auto qualifiers = context.first_context_data()->qualifiers();
  cout << "[PARAM] Batching enabled: " << boolalpha << qualifiers.using_batching
       << endl;
  cout << "[PARAM] poly_modulus_degree N=" << parms.poly_modulus_degree()
       << endl;
  cout << "[PARAM] plain_modulus log(t)=" << parms.plain_modulus().bit_count()
       << " bits" << endl;
  size_t coeff_modulus_bit_count = 0;
  cout << "[PARAM] coeff_modulus log(q)=";
  for (auto q_i : parms.coeff_modulus()) {
    coeff_modulus_bit_count += q_i.bit_count();
    if (q_i != parms.coeff_modulus()[0]) {
      cout << " + ";
    }
    cout << q_i.bit_count();
  }
  cout << " = " << coeff_modulus_bit_count << " bits" << endl;
  cout << "[PARAM] coeff_modulus.size=" << parms.coeff_modulus().size() << endl;

  cout << "[PARAM] plain_modulus t=" << parms.plain_modulus().value() << endl;
  cout << "[PARAM] coeff_modulus q=";
  for (auto q_i : parms.coeff_modulus()) {
    if (q_i != parms.coeff_modulus()[0]) {
      cout << " * ";
    }
    cout << q_i.value();
  }
  cout << endl;

  if (throw_on_invalid &&
      context.first_context_data()->qualifiers().parameter_error !=
          seal::EncryptionParameterQualifiers::error_type::success) {
    throw invalid_argument(string(context.parameter_error_name()) + ": " +
                           string(context.parameter_error_message()));
  }
}

#endif  // RINGSNARK_SEAL_UTIL_HPP
