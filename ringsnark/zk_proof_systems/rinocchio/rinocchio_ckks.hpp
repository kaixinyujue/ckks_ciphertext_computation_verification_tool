//
// Created by andy on 2023/12/20.
//

#ifndef RINOCCHIO_CKKS_HPP
#define RINOCCHIO_CKKS_HPP
#define CURVE_BN128
#include <ringsnark/zk_proof_systems/r1cs_ppzksnark.hpp>
#include <libff/algebra/curves/public_params.hpp>
#include <libff/common/default_types/ec_pp.hpp>
#include <libff/algebra/scalar_multiplication/multiexp.hpp>
using std::vector;

namespace ringsnark::rinocchio {
    using G1 = typename libff::default_ec_pp::G1_type;
    using G2 = typename libff::default_ec_pp::G2_type;
    using GT = typename libff::default_ec_pp::GT_type;
    using Fr = typename libff::default_ec_pp::Fp_type;
    template <typename RingT>
    class proving_key : public ringsnark::proving_key<RingT> {
    public:
        const r1cs_constraint_system<RingT> constraint_system;
        const vector<G1> tw;
        const vector<G1> tv;
        const vector<G1> ty;
        const vector<G1> st;

        proving_key(const ringsnark::r1cs_constraint_system<RingT> &constraint_system,
                    const vector<G1> &tw,const vector<G1> &tv,const vector<G1> &ty, const vector<G1> st)
                : constraint_system(constraint_system),
                  tw(tw),
                  tv(tv),
                  ty(ty),
                  st(st){
//            assert(s_pows.size() == constraint_system.num_constraints() + 1);
        }

        [[nodiscard]] size_t size_in_bits() const override {
            return tw.size() * tw[0].size_in_bits() + tv.size() * tv[0].size_in_bits()+ty.size() * ty[0].size_in_bits()+st.size() * st[0].size_in_bits();
        }
    };

    template <typename RingT>
    class verification_key : public ringsnark::verification_key<RingT> {
    public:
        const G1 g;
        const G1 gts;
        const vector<G1> tw;
        const vector<G1> tv;
        const vector<G1> ty;
        verification_key() = default;
        verification_key(const G1 g,const G1 gts,const vector<G1> &tw,const vector<G1> &tv,const vector<G1> &ty )
                : g(g),gts(gts),tw(tw),tv(tv),ty(ty) {
        }

        [[nodiscard]] size_t size_in_bits() const override {
            return g.size_in_bits() +gts.size_in_bits()+tw.size() * tw[0].size_in_bits() + tv.size() * tv[0].size_in_bits()+ty.size() * ty[0].size_in_bits();
        }
    };

    template <typename RingT>
    class keypair {
    public:
        const proving_key<RingT> &pk;
        const verification_key<RingT> &vk;

        keypair(const keypair<RingT> &other) = default;

        keypair(keypair<RingT> &&other) noexcept = default;

        keypair(proving_key<RingT> &pk, const verification_key<RingT> &vk)
                : pk(pk), vk(vk) {}

        keypair(proving_key<RingT> &&pk, verification_key<RingT> &&vk)
                : pk(std::move(pk)), vk(std::move(vk)) {}
    };

    template <typename RingT>
    class proof : public ringsnark::proof<RingT> {
    public:
        const G1 A;
        const G1 B;
        const G1 C;
        const G1 D;

        proof(G1 a, G1 b,  G1 c,  G1 d)
                : A(a),

                  B(b),

                  C(c),

                  D(d)
        {}

        [[nodiscard]] size_t size_in_bits() const override {
            return A.size_in_bits()  + B.size_in_bits() + C.size_in_bits()+ D.size_in_bits();
        }
    };

}  // namespace ringsnark::rinocchio

#include "rinocchio_ckks.tcc"
#endif
