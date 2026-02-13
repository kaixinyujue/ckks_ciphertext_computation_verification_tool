#define CURVE_BN128
#include <ringsnark/reductions/r1cs_to_qrp/r1cs_to_qrp.hpp>
#include <ringsnark/reductions/r1cs_to_qap/r1cs_to_qap.hpp>
#include <stdio.h>
#include <iostream>
#include <libff/algebra/curves/public_params.hpp>
#include <libff/common/default_types/ec_pp.hpp>
#include <libff/algebra/scalar_multiplication/multiexp.hpp>

namespace ringsnark::rinocchio {
    using G1 = typename libff::default_ec_pp::G1_type;
    using G2 = typename libff::default_ec_pp::G2_type;
    using GT = typename libff::default_ec_pp::GT_type;
    using Fr = typename libff::default_ec_pp::Fp_type;
    template <typename RingT>
    //参数d:degree of polynomial
    keypair<RingT> generator(const r1cs_constraint_system<RingT> &cs,int d) {
        const auto domain = get_evaluation_domain<RingT>(cs.num_constraints());
        Fr s=Fr::random_element();
        Fr t=Fr::random_element();
        const qrp_instance_evaluation<RingT> qap_inst = r1cs_to_qap_instance_map_with_evaluation(cs, s);
//        vector<RingT> s_pows_ring(qrp_inst.Ht.begin(),qrp_inst.Ht.begin() + cs.num_constraints() + 1);
        std::vector<G1> tv_pk,tw_pk,ty_pk,tv_vk,tw_vk,ty_vk;
        tv_pk.reserve(cs.auxiliary_input_size);
        tw_pk.reserve(cs.auxiliary_input_size);
        ty_pk.reserve(cs.auxiliary_input_size);
        tv_vk.reserve(cs.primary_input_size);
        tw_vk.reserve(cs.primary_input_size);
        ty_vk.reserve(cs.primary_input_size);
        G1 g1 = G1::one();
        Fr t_i=t;
        Fr tv_exp,tw_exp,ty_exp;
        for(size_t i = 1; i <= d; i++){
            for(size_t k =0; k < cs.auxiliary_input_size; k++){
                size_t idx = i + cs.primary_input_size + 1;
                tv_exp = t_i * qap_inst.At[idx];
                tw_exp = t_i * qap_inst.Bt[idx];
                ty_exp = t_i * qap_inst.Ct[idx];
                tv_pk.push_back(g1 * tv_exp);
                tw_pk.push_back(g1 * tw_exp);
                ty_pk.push_back(g1 * ty_exp);
            }
            for(size_t j =0; j < cs.primary_input_size; j++){
                tv_exp = t_i * qap_inst.At[j];
                tw_exp = t_i * qap_inst.Bt[j];
                ty_exp = t_i * qap_inst.Ct[j];
                tv_vk.push_back(g1 * tv_exp);
                tw_vk.push_back(g1 * tw_exp);
                ty_vk.push_back(g1 * ty_exp);
            }
            t_i = t_i * t;
        }
        const vector<EncT> s_pows = EncT::encode(s_pows_ring);

        auto pk = new proving_key<RingT, EncT>(cs, s_pows);
        auto vk = new verification_key<RingT, EncT>(*pk, s, t)
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
#pragma omp section
            {
                b_enc = EncT::inner_product(pk.s_pows.begin(), pk.s_pows.end() - 1,
                                            b_mid.begin(), b_mid.end());
            }
#pragma omp section
            {
                c_enc = EncT::inner_product(pk.s_pows.begin(), pk.s_pows.end() - 1,
                                            c_mid.begin(), c_mid.end());
            }
#pragma omp section
            {
                d_enc = EncT::inner_product(pk.s_pows.begin(), pk.s_pows.end(), h.begin(),
                                            h.end());
            }
#pragma omp section
            {
                z_enc = EncT::inner_product(pk.s_pows.begin(), pk.s_pows.end(), z.begin(),
                                            z.end());
            }
        }
        // Add shift terms
        // TODO: add terms to coefficients_for_{A, B, C} directly, similarly to H
        if (use_zk) {
            a_enc += d1 * z_enc;
            b_enc += d2 * z_enc;
            c_enc += d3 * z_enc;
        }
        clock_t abc_end = clock();
        cout << "prover abc time is: " << ((double)abc_end - abc_start) / CLOCKS_PER_SEC << endl;
        // cout<<"prover debug4"<<endl;
        // cout<<" prover debug5"<<endl;
        return ringsnark::rinocchio::proof<RingT, EncT>(
                a_enc, b_enc, c_enc, d_enc);
    }

    template <typename RingT, typename EncT>
    bool verifier(const verification_key<RingT, EncT> &vk,
                  const r1cs_primary_input<RingT> &primary_input,
                  const proof<RingT, EncT> &proof) {
        const array<EncT, 4> encs = {proof.A, proof.B,proof.C,proof.D};
        bool auxiliary_inputs_present = true;
        size_t num_proof_elems = 4;
        array<RingT, 4> decs;
        const auto sk_enc = vk.sk_enc;
        // cout<<"verifier debug1"<<endl;
        clock_t verifier_decode_start = clock();
#pragma omp parallel for default(none) \
    shared(sk_enc, decs, encs, num_proof_elems)
        for (size_t i = 0; i < num_proof_elems; i++) {
            decs[i] = EncT::decode(sk_enc, encs[i]);
        }
        clock_t verifier_decode_end = clock();
        cout << "verifier_decode time is: " << ((double)verifier_decode_end - verifier_decode_start) / CLOCKS_PER_SEC << endl;
        auto [V_mid, W_mid, Y_mid, H] = decs;

        // cout<<"verifier debug2"<<endl;
        const auto cs = vk.pk.constraint_system;
        clock_t verifier_qrp_start = clock();
        qrp_instance_evaluation<RingT> qrp_inst_eval =
                r1cs_to_qrp_instance_map_with_evaluation(cs, vk.s);
        clock_t verifier_qrp_end = clock();
        cout << "verifier_qrp time is: " << ((double)verifier_qrp_end - verifier_qrp_start) / CLOCKS_PER_SEC << endl;
        // cout<<"verifier debug3"<<endl;
        // TODO: make this more efficient, and skip all zero-mults
        vector<RingT> padded_primary_assignment(primary_input);
        vector<RingT> zeros(vk.pk.constraint_system.auxiliary_input_size,
                            RingT::zero());
        padded_primary_assignment.insert(padded_primary_assignment.end(),
                                         zeros.begin(), zeros.end());
        // TODO: or use the {At, Bt, Ct} members from qrp_inst_eval?
        vector<RingT> v_io(cs.num_constraints()), w_io(cs.num_constraints()),
                y_io(cs.num_constraints());
        clock_t verifier_io_start = clock();
        for (size_t i = 0; i < cs.num_constraints(); ++i) {
            v_io[i] = cs.constraints[i].a.evaluate(padded_primary_assignment);
            w_io[i] = cs.constraints[i].b.evaluate(padded_primary_assignment);
            y_io[i] = cs.constraints[i].c.evaluate(padded_primary_assignment);
        }
        auto domain = get_evaluation_domain<RingT>(cs.num_constraints());
        vector<RingT> xs(domain->m);
        for (size_t i = 0; i < domain->m; i++) {
            xs[i] = domain->get_domain_element(i);
        }
        v_io = interpolate(xs, v_io);
        w_io = interpolate(xs, w_io);
        y_io = interpolate(xs, y_io);
        clock_t verifier_io_end = clock();
        cout << "verifier_io_x time is: " << ((double)verifier_io_end - verifier_io_start) / CLOCKS_PER_SEC << endl;
        // cout<<"verifier debug4"<<endl;
        clock_t verifier_ios_start = clock();
        auto v_io_s = eval(v_io, vk.s);
        auto w_io_s = eval(w_io, vk.s);
        auto y_io_s = eval(y_io, vk.s);
        clock_t verifier_ios_end = clock();
        cout << "verifier_io_s time is: " << ((double)verifier_ios_end - verifier_ios_start) / CLOCKS_PER_SEC << endl;
        // cout<<"verifier debug5"<<endl;
        RingT P = V_mid + v_io_s;
        P *= W_mid + w_io_s;
        P -= Y_mid + y_io_s;

        RingT tmp;
        bool res = true;
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