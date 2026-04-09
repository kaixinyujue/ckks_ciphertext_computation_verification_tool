
#include <ringsnark/reductions/r1cs_to_qrp/r1cs_to_qrp.hpp>
#include <stdio.h>
#include <iostream>
using namespace std;
namespace ringsnark::rinocchio {
template <typename RingT, typename EncT>
keypair<RingT, EncT> generator(const r1cs_constraint_system<RingT> &cs) {
  // cout<<"generator debug1"<<endl;
  const auto domain = get_evaluation_domain<RingT>(cs.num_constraints());
  // cout<<"generator debug2"<<endl;
  const RingT s = RingT::random_exceptional_element(domain);
  // cout<<"generator debug3"<<endl;
  const qrp_instance_evaluation<RingT> qrp_inst =
      r1cs_to_qrp_instance_map_with_evaluation(cs, s);
    // cout<<"generator debug4"<<endl;
  const auto [pk_enc, sk_enc] = EncT::keygen();
//12-9
//  const RingT alpha = RingT::random_invertible_element(),
//              r_v = RingT::random_invertible_element(),
//              r_w = RingT::random_invertible_element(), r_y = r_v * r_w,
//              beta = RingT::random_nonzero_element();

  // ({E(s^i)}_{i=0}^{num_mid}}, {E(alpha * s^i)}_{i=0}^{num_mid}},
  // {beta_prod}_{i=0}^{num_mid}, pk) Ht holds the monomials {s^i}_{i=0}^m

  vector<RingT> s_pows_ring(qrp_inst.Ht.begin(),
                            qrp_inst.Ht.begin() + cs.num_constraints() + 1);
  //12-9
//  vector<RingT> alpha_s_pows_ring(s_pows_ring);
//  for (auto &s_i : alpha_s_pows_ring) {
//    s_i *= alpha;
//  }
//12-9
//  vector<RingT> linchecks, rv_vs, rw_ws, ry_ys;
//  linchecks.reserve(cs.auxiliary_input_size);
//  rv_vs.reserve(cs.auxiliary_input_size);
//  rw_ws.reserve(cs.auxiliary_input_size);
//  ry_ys.reserve(cs.auxiliary_input_size);
//  for (size_t i = 0; i < cs.auxiliary_input_size; i++) {
//    size_t idx = i + cs.primary_input_size + 1;
//    rv_vs.push_back(r_v * qrp_inst.At[idx]);
//    rw_ws.push_back(r_w * qrp_inst.Bt[idx]);
//    ry_ys.push_back(r_y * qrp_inst.Ct[idx]);
//    RingT lincheck(rv_vs[i]);
//    lincheck += rw_ws[i];
//    lincheck += ry_ys[i];
//    lincheck *= beta;
//    linchecks.push_back(lincheck);
//  }

  const vector<EncT> s_pows = EncT::encode(sk_enc, s_pows_ring);
  //12-9
//                     alpha_s_pows = EncT::encode(sk_enc, alpha_s_pows_ring),
//                     beta_prods = EncT::encode(sk_enc, linchecks);

//  const RingT beta_Zt = beta * qrp_inst.Zt;
//  const EncT beta_rv_ts = EncT::encode(sk_enc, {beta_Zt * r_v})[0];
//  const EncT beta_rw_ts = EncT::encode(sk_enc, {beta_Zt * r_w})[0];
//  const EncT beta_ry_ts = EncT::encode(sk_enc, {beta_Zt * r_y})[0];
//
//  const RingT alpha_Zt = alpha * qrp_inst.Zt;
//  const EncT alpha_rv_ts = EncT::encode(sk_enc, {alpha_Zt * r_v})[0];
//  const EncT alpha_rw_ts = EncT::encode(sk_enc, {alpha_Zt * r_w})[0];
//  const EncT alpha_ry_ts = EncT::encode(sk_enc, {alpha_Zt * r_y})[0];

  // pk = ({E(s^i)}_{i=0}^{num_mid}}, {E(alpha * s^i)}_{i=0}^{num_mid}},
  // {beta_prod}_{i=0}^{num_mid}, pk_enc)
//  auto pk = new proving_key<RingT, EncT>(
//      cs, s_pows, alpha_s_pows, beta_prods, beta_rv_ts, beta_rw_ts, beta_ry_ts,
//      alpha_rv_ts, alpha_rw_ts, alpha_ry_ts, EncT::encode(sk_enc, rv_vs),
//      EncT::encode(sk_enc, rw_ws), EncT::encode(sk_enc, ry_ys), pk_enc);
    auto pk = new proving_key<RingT, EncT>(cs, s_pows, pk_enc);
//12-9
  // vk = (pk, s, alpha, beta, r_v, r_w, r_y, sk_enc)
//  auto vk = new verification_key<RingT, EncT>(*pk, s, alpha, beta, r_v, r_w,
//                                              r_y, sk_enc);
    auto vk = new verification_key<RingT, EncT>(*pk, s, sk_enc, qrp_inst);

  return ::ringsnark::rinocchio::keypair<RingT, EncT>(*pk, *vk);
}



template <typename RingT, typename EncT>
proof<RingT, EncT> prover(const proving_key<RingT, EncT> &pk,
                          const r1cs_primary_input<RingT> &primary_input,
                          const r1cs_auxiliary_input<RingT> &auxiliary_input) {
#ifdef DEBUG
  assert(pk.constraint_system.is_satisfied(primary_input, auxiliary_input));
#endif
  const bool use_zk = !auxiliary_input.empty();
  if (!use_zk) {
    cout << "[Prover] "
         << "using non-zero-knowledge SNARK, since no auxiliary inputs are "
            "defined"
         << endl;
  }
  // cout<<"prover debug1"<<endl;
  const RingT d1 = use_zk ? RingT::random_invertible_element() : RingT::zero();
  const RingT d2 = use_zk ? RingT::random_invertible_element() : RingT::zero();
  const RingT d3 = use_zk ? RingT::random_invertible_element() : RingT::zero();
  clock_t qrp_wit_start = clock();
  const qrp_witness<RingT> qrp_wit = r1cs_to_qrp_witness_map(
      pk.constraint_system, primary_input, auxiliary_input, d1, d2, d3);
  clock_t qrp_wit_end = clock();
  cout << "prover qrp_wit time is: " << ((double)qrp_wit_end - qrp_wit_start) / CLOCKS_PER_SEC << endl;
  // cout<<" prover debug2"<<endl;
  // s_pows, alpha_s_pows have length d+1, where d = cs.num_constraints() is the
  // size of the QRP
  const auto a_mid = qrp_wit.coefficients_for_A_mid;
  const auto b_mid = qrp_wit.coefficients_for_B_mid;
  const auto c_mid = qrp_wit.coefficients_for_C_mid;
  const auto z = qrp_wit.coefficients_for_Z;
  const auto h = qrp_wit.coefficients_for_H;

  EncT a_enc, alpha_a_enc, b_enc, alpha_b_enc, c_enc, alpha_c_enc, d_enc,
            alpha_d_enc, z_enc, alpha_z_enc;
    clock_t abc_start = clock();
#pragma omp parallel sections default(none) shared(                            \
        pk, a_mid, b_mid, c_mid, z, h, a_enc, alpha_a_enc, b_enc, alpha_b_enc, \
            c_enc, alpha_c_enc, d_enc, alpha_d_enc, z_enc, alpha_z_enc)
  {

#pragma omp section
    {
      a_enc = EncT::inner_product(pk.s_pows.begin(), pk.s_pows.end() - 1,
                                  a_mid.begin(), a_mid.end());

    }
    //12-9
//#pragma omp section
//    {
//      alpha_a_enc = EncT::inner_product(pk.alpha_s_pows.begin(),
//                                        pk.alpha_s_pows.end() - 1,
//                                        a_mid.begin(), a_mid.end());
//    }
#pragma omp section
    {
      b_enc = EncT::inner_product(pk.s_pows.begin(), pk.s_pows.end() - 1,
                                  b_mid.begin(), b_mid.end());
    }
//#pragma omp section
//    {
//      alpha_b_enc = EncT::inner_product(pk.alpha_s_pows.begin(),
//                                        pk.alpha_s_pows.end() - 1,
//                                        b_mid.begin(), b_mid.end());
//    }
#pragma omp section
    {
      c_enc = EncT::inner_product(pk.s_pows.begin(), pk.s_pows.end() - 1,
                                  c_mid.begin(), c_mid.end());
    }
//#pragma omp section
//    {
//      alpha_c_enc = EncT::inner_product(pk.alpha_s_pows.begin(),
//                                        pk.alpha_s_pows.end() - 1,
//                                        c_mid.begin(), c_mid.end());
//    }
#pragma omp section
    {
      d_enc = EncT::inner_product(pk.s_pows.begin(), pk.s_pows.end(), h.begin(),
                                  h.end());
    }
//#pragma omp section
//    {
//      alpha_d_enc = EncT::inner_product(
//          pk.alpha_s_pows.begin(), pk.alpha_s_pows.end(), h.begin(), h.end());
//    }
#pragma omp section
    {
      z_enc = EncT::inner_product(pk.s_pows.begin(), pk.s_pows.end(), z.begin(),
                                  z.end());
    }
//#pragma omp section
//    {
//      alpha_z_enc = EncT::inner_product(
//          pk.alpha_s_pows.begin(), pk.alpha_s_pows.end(), z.begin(), z.end());
//    }
  }
  // Add shift terms
  // TODO: add terms to coefficients_for_{A, B, C} directly, similarly to H
  if (use_zk) {
    a_enc += d1 * z_enc;
//    alpha_a_enc += d1 * alpha_z_enc;
    b_enc += d2 * z_enc;
//    alpha_b_enc += d2 * alpha_z_enc;
    c_enc += d3 * z_enc;
//    alpha_c_enc += d3 * alpha_z_enc;
  }
    clock_t abc_end = clock();
  cout << "prover abc time is: " << ((double)abc_end - abc_start) / CLOCKS_PER_SEC << endl;
  // cout<<"prover debug4"<<endl;
  //12-9
//  EncT f_enc;
//  if (!auxiliary_input.empty()) {
//    f_enc = EncT::inner_product(pk.beta_prods.begin(), pk.beta_prods.end(),
//                                auxiliary_input.begin(), auxiliary_input.end());
//    if (use_zk) {
//      f_enc += d1 * pk.beta_rv_ts;
//      f_enc += d2 * pk.beta_rw_ts;
//      f_enc += d3 * pk.beta_ry_ts;
//    }
//  }
  // cout<<" prover debug5"<<endl;
//  return ringsnark::rinocchio::proof<RingT, EncT>(
//      a_enc, alpha_a_enc, b_enc, alpha_b_enc, c_enc, alpha_c_enc, d_enc,
//      alpha_d_enc, f_enc);
    return ringsnark::rinocchio::proof<RingT, EncT>(
            a_enc, b_enc, c_enc, d_enc);
}

template <typename RingT, typename EncT>
bool verifier(const verification_key<RingT, EncT> &vk,
              const r1cs_primary_input<RingT> &primary_input,
              const proof<RingT, EncT> &proof) {
    //12-9
//  const array<EncT, 9> encs = {proof.A,       proof.A_prime, proof.B,
//                               proof.B_prime, proof.C,       proof.C_prime,
//                               proof.D,       proof.D_prime, proof.F};
    const array<EncT, 4> encs = {proof.A, proof.B,proof.C,proof.D};
  bool auxiliary_inputs_present = true;
//  if (proof.F == EncT()) {
//    cout << "[Verifier] last proof element is empty, i.e., no auxiliary inputs "
//            "are present"
//         << endl;
//    auxiliary_inputs_present = false;
//  }
//  size_t num_proof_elems = auxiliary_inputs_present ? 9 : 8;
    size_t num_proof_elems = 4;
//  array<RingT, 9> decs;
    array<RingT, 4> decs;
  const auto sk_enc = vk.sk_enc;
//  cout<<"verifier debug1"<<endl;
    clock_t verifier_decode_start = clock();
#pragma omp parallel for default(none) \
    shared(sk_enc, decs, encs, num_proof_elems)
  for (size_t i = 0; i < num_proof_elems; i++) {
    decs[i] = EncT::decode(sk_enc, encs[i]);
  }
    clock_t verifier_decode_end = clock();
    cout << "verifier_decode time is: " << ((double)verifier_decode_end - verifier_decode_start) / CLOCKS_PER_SEC << endl;
//  auto [V_mid, V_mid_prime, W_mid, W_mid_prime, Y_mid, Y_mid_prime, H, H_prime,L_beta] = decs;
    auto [V_mid, W_mid, Y_mid, H] = decs;

    // cout<<"verifier debug2"<<endl;
  const auto cs = vk.pk.constraint_system;
    clock_t verifier_qrp_start = clock();
    //2024/3/14
//  qrp_instance_evaluation<RingT> qrp_inst_eval =
//      r1cs_to_qrp_instance_map_with_evaluation(cs, vk.s);

    qrp_instance_evaluation<RingT> qrp_inst_eval = vk.qrp_inst;
    clock_t verifier_qrp_end = clock();
    cout << "verifier_qrp time is: " << ((double)verifier_qrp_end - verifier_qrp_start) / CLOCKS_PER_SEC << endl;
    // cout<<"verifier debug3"<<endl;
  // L = beta * ((vk.r_v * V_mid) + (vk.r_w * W_mid) + (vk.r_y * Y_mid))
  //12-9
//  RingT L = V_mid * vk.r_v;
//  L += W_mid * vk.r_w;
//  L += Y_mid * vk.r_y;
//  L *= vk.beta;
//
  // TODO: make this more efficient, and skip all zero-mults
  vector<RingT> padded_primary_assignment(primary_input);
  vector<RingT> zeros(vk.pk.constraint_system.auxiliary_input_size,
                      RingT::zero());
  padded_primary_assignment.insert(padded_primary_assignment.end(),
                                   zeros.begin(), zeros.end());
  // TODO: or use the {At, Bt, Ct} members from qrp_inst_eval?
//  clock_t verifier_ios_start = clock();
//  vector<RingT> v_io(cs.num_constraints()), w_io(cs.num_constraints()),
//      y_io(cs.num_constraints());
//    clock_t verifier_io_start = clock();
//  for (size_t i = 0; i < cs.num_constraints(); ++i) {
//    v_io[i] = cs.constraints[i].a.evaluate(padded_primary_assignment);
//    w_io[i] = cs.constraints[i].b.evaluate(padded_primary_assignment);
//    y_io[i] = cs.constraints[i].c.evaluate(padded_primary_assignment);
//  }
//  auto domain = get_evaluation_domain<RingT>(cs.num_constraints());
//  vector<RingT> xs(domain->m);
//  for (size_t i = 0; i < domain->m; i++) {
//    xs[i] = domain->get_domain_element(i);
//  }
//  v_io = interpolate(xs, v_io);
//  w_io = interpolate(xs, w_io);
//  y_io = interpolate(xs, y_io);
//    clock_t verifier_io_end = clock();
//    cout << "verifier_io_x time is: " << ((double)verifier_io_end - verifier_io_start) / CLOCKS_PER_SEC << endl;
//    cout<<"verifier debug4"<<endl;
    clock_t verifier_ios_start = clock();
//    RingT v_io_s= RingT::zero(),w_io_s=RingT::zero(),y_io_s=RingT::zero();
    RingT v_io_s= qrp_inst_eval.At[0],w_io_s=qrp_inst_eval.Bt[0],y_io_s=qrp_inst_eval.Ct[0];
    for(size_t i = 0; i<cs.primary_input_size;i++)
    {
        v_io_s +=qrp_inst_eval.At[i+1]*primary_input[i];
        w_io_s +=qrp_inst_eval.Bt[i+1]*primary_input[i];
        y_io_s +=qrp_inst_eval.Ct[i+1]*primary_input[i];
    }
//    auto v_io_s = eval(v_io, vk.s);
//    auto w_io_s = eval(w_io, vk.s);
//    auto y_io_s = eval(y_io, vk.s);
    clock_t verifier_ios_end = clock();
    cout << "verifier_io_s time is: " << ((double)verifier_ios_end - verifier_ios_start) / CLOCKS_PER_SEC << endl;
    // cout<<"verifier debug5"<<endl;

  // P = (v_io(s) + V_mid) * (w_io(s) + W_mid) - (y_io(s) + Y_mid)
  RingT P = V_mid + v_io_s;
  P *= W_mid + w_io_s;
  P -= Y_mid + y_io_s;

  RingT tmp;
  //12-9
//  // CHECK: V'_mid = alpha * V_mid
//  tmp = V_mid * vk.alpha;
  bool res = true;
//  if (V_mid_prime != tmp) {
//    res = false;
//  }
//  // CHECK: W'_mid = alpha * W_mid
//  tmp = W_mid * vk.alpha;
//  if (W_mid_prime != tmp) {
//    res = false;
//  }
//  // CHECK: Y'_mid = alpha * Y_mid
//  tmp = Y_mid * vk.alpha;
//  if (Y_mid_prime != tmp) {
//    res = false;
//  }
//  // CHECK: H' = alpha * H
//  tmp = H * vk.alpha;
//  if (H_prime != tmp) {
//    res = false;
//  }
//  if (auxiliary_inputs_present) {
//    // CHECK: L_beta = L
//    if (L != L_beta) {
//      res = false;
//    }
//  }
  // CHECK: P = H * Z(t)
  clock_t verifier_check_start = clock();
  tmp = H * qrp_inst_eval.Zt;
  if (P != tmp) {
    res = false;
  }
    clock_t verifier_check_end = clock();
    cout << "verifier_check time is: " << ((double)verifier_check_end - verifier_check_start) / CLOCKS_PER_SEC << endl;
    // cout<<"verifier debug6"<<endl;
  return res;
}
}  // namespace ringsnark::rinocchio