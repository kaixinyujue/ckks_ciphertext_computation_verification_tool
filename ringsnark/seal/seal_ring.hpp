#ifndef RINGSNARK_SEAL_RING_HPP
#define RINGSNARK_SEAL_RING_HPP
#define CURVE_BN128
#include <iostream>
#include <fstream>
#include <filesystem>
#include <string>
#include <memory>
#include <utility>
#include <variant>
#include <vector>
#include <libff/algebra/curves/public_params.hpp>
#include <libff/common/default_types/ec_pp.hpp>
#include <libff/algebra/scalar_multiplication/multiexp.hpp>

#include "poly_arith.h"
#include "../util/evaluation_domain.hpp"
#include "seal/seal.h"
#include "seal/util/rlwe.h"



using std::vector;

namespace ringsnark::seal {
    class RingElem {
    protected:
        using Scalar = uint64_t;
        using Poly = polytools::SealPoly;

        // TODO: try and turn this into a template parameter (which would probably
        // require building a constexpr SEALContext)
        inline static ::seal::SEALContext *context = nullptr;
        std::variant<Poly, Scalar> value = (uint64_t)0;
        inline static std::shared_ptr<::seal::UniformRandomGenerator> prng = nullptr;

        [[nodiscard]] Scalar &get_scalar();

    public:
        /*
         * Constructors
         */
        RingElem();

        RingElem(const RingElem &other) = default;

        RingElem(RingElem &&other) = default;

        RingElem &operator=(const RingElem &other) = default;

        virtual ~RingElem() = default;

        RingElem(uint64_t value);

        explicit RingElem(const polytools::SealPoly &poly);

        bool saveR(std::string filePath){
            std::string dir = filePath;
            if (!dir.empty() && dir.back() == '/') {
                dir.erase(dir.size() - 1);  // 去除最后一个字符
            }
            std::filesystem::create_directories(dir);

            size_t isP;
            if(this->is_poly()){
                isP = 1;
            }
            else{
                isP = 0;
            }
            std::string ringelemtype_bin = filePath + "ringelemtype.bin";
            std::ofstream ofs(ringelemtype_bin, std::ios::binary); // 以二进制方式打开文件
            if (!ofs) {
                std::cerr << "Error opening file for writing: " << ringelemtype_bin << std::endl;
                return false;
            }
            ofs.write(reinterpret_cast<const char*>(&isP), sizeof(size_t));
            ofs.close();

            if(isP==1){
                std::string ringelem_bin = filePath + "ringelem.json";
                std::ofstream ofs1(ringelem_bin);
                if (!ofs1) {
                    std::cerr << "Error opening file for writing: " << ringelem_bin << std::endl;
                    return false;
                }
                polytools::SealPoly polyv = this->get_poly();
                polyv.save(ofs1);
                ofs1.close();
            }
            else{
                std::string ringelem_bin = filePath + "ringelem.bin";
                std::ofstream ofs1(ringelem_bin, std::ios::binary);
                if (!ofs1) {
                    std::cerr << "Error opening file for writing: " << ringelem_bin << std::endl;
                    return false;
                }
                uint64_t i64tmp = this->get_scalar();
                ofs1.write(reinterpret_cast<const char*>(&i64tmp), sizeof(uint64_t));
                ofs1.close();
            }
            return true;
        };

        bool loadR(std::string filePath, ::seal::SEALContext &context){
            size_t isP;
            std::string ringelemtype_bin = filePath + "ringelemtype.bin";
            std::ifstream ifs(ringelemtype_bin, std::ios::binary); // 以二进制方式打开文件
            if (!ifs) {
                std::cerr << "Error opening file for reading: " << ringelemtype_bin << std::endl;
                return false;
            }
            ifs.read(reinterpret_cast<char*>(&isP), sizeof(size_t));
            ifs.close();

            if(isP==1){
                std::string ringelem_bin = filePath + "ringelem.json";
                std::ifstream ifs1(ringelem_bin);
                if (!ifs1) {
                    std::cerr << "Error opening file for reading: " << ringelem_bin << std::endl;
                    return false;
                }
                polytools::SealPoly polyv(context);
                polyv.load(ifs1);
                ifs1.close();
                this->value = polyv;
            }
            else{
                std::string ringelem_bin = filePath + "ringelem.bin";
                std::ifstream ifs1(ringelem_bin, std::ios::binary);
                if (!ifs1) {
                    std::cerr << "Error opening file for reading: " << ringelem_bin << std::endl;
                    return false;
                }
                uint64_t i64tmp;
                ifs1.read(reinterpret_cast<char*>(&i64tmp), sizeof(uint64_t));
                ifs1.close();
                this->value = i64tmp;
            }
            return true;
        };


        /*
         * Static
         */
        static void set_context(::seal::SEALContext &context_) {
            if (context == nullptr) {
                context = new ::seal::SEALContext(context_);
            } else {
                throw std::invalid_argument("cannot re-set context once set");
            }
        }

        static ::seal::SEALContext &get_context() {
            if (context == nullptr) {
                throw std::invalid_argument("context not set");
            } else {
                return *context;
            }
        }
        //12-26 ringelem: vector modulus_size*coeff_degree(4*8192)
        //
        uint64_t evalring(uint64_t t){
//            Poly r_poly=r.get_poly();
            int modulus_length=get_poly().get_coeff_modulus().size();
            auto q0=get_poly().get_coeff_modulus()[0].value();
            cout<<"q0: "<<q0<<endl;
//            vector<uint64_t> result(modulus_length);
            uint64_t result=1;
            for(int k=0;k<modulus_length;k++)
            {
                uint64_t tmp=t;
                uint64_t resultk;
                auto q=get_poly().get_coeff_modulus()[k].value();
                vector<uint64_t> r_coeff=get_poly().get_limb(k);
                resultk=r_coeff[0];
                for(int i=1;i<r_coeff.size();i++)
                {
                    resultk += (tmp * r_coeff[i])%q;
                    tmp = tmp * t;
                }
                result = result * resultk;
                cout<<"result "<<result<<endl;
                result = result % q0;
            }
            return result;
        }
        static RingElem one() { return RingElem(1); }

        static RingElem zero() { return RingElem(0); }

        static RingElem random_exceptional_element(
                const shared_ptr<evaluation_domain<RingElem>> domain = nullptr) {
            // TODO: throw error if number of exceptional elements is less than required

            // cout<<"get_evaluation_domain debug1"<<endl;
            auto parms =
                    get_context().get_context_data(get_context().first_parms_id())->parms();
            uint64_t q1 = parms.coeff_modulus()[0].value();
            uint64_t bit_width = 1ULL + (uint64_t)std::floor(std::log2l(q1));
            // uint64_t mask = (1 << (bit_width + 1)) - 1;
            uint64_t mask = 137438953471;

            // cout<<"get_evaluation_domain debug2"<<endl;
            // Rejection sampling with masking
            uint64_t rand = ::seal::random_uint64() & mask;
            while (rand >= q1 || (domain && rand <= domain->m)) {
                rand = ::seal::random_uint64() & mask;
            }
            // cout<<"get_evaluation_domain debug3"<<endl;

            return RingElem(rand);
        }

        inline static RingElem random_element() {
            if (prng == nullptr) {
                prng = ::seal::UniformRandomGeneratorFactory::DefaultFactory()->create();
            }

            auto parms =
                    get_context().get_context_data(get_context().first_parms_id())->parms();
            vector<uint64_t> coeffs(parms.poly_modulus_degree() *
                                    parms.coeff_modulus().size());
            ::seal::util::sample_poly_uniform(prng, parms, coeffs.data());
            return RingElem(polytools::SealPoly(get_context(), coeffs,
                                                &get_context().first_parms_id()));
        }

        static RingElem random_invertible_element() {
            RingElem res;
            do {
                res = random_element();
            } while (!res.is_invertible());
            return res;
        }

        static RingElem random_nonzero_element() {
            RingElem res;
            do {
                res = random_element();
            } while (res.is_zero());
            return res;
        }

        /*
         * Functions
         */
        [[nodiscard]] size_t size_in_bits() const;

        [[nodiscard]] bool is_zero() const;

        [[nodiscard]] bool fast_is_zero() const;

        [[nodiscard]] bool is_poly() const;

        [[nodiscard]] bool is_scalar() const;

        void negate_inplace();

        inline RingElem operator-() const {
            RingElem res(*this);
            res.negate_inplace();
            return res;
        }

        [[nodiscard]] bool is_invertible() const noexcept;

        void invert_inplace();

        [[nodiscard]] inline RingElem inverse() const {
            RingElem res(*this);
            res.invert_inplace();
            return res;
        }

        RingElem &operator+=(const RingElem &other);

        RingElem &operator-=(const RingElem &other);

        RingElem &operator*=(const RingElem &other);

        RingElem &operator/=(const RingElem &other) {
            *this *= other.inverse();
            return *this;
        }

        RingElem &to_poly_inplace();

        [[nodiscard]] RingElem &to_poly() const {
            auto *res = new RingElem(*this);
            res->to_poly_inplace();
            return *res;
        }

        [[nodiscard]] size_t hash() const;

        class invalid_ring_elem_types : std::invalid_argument {
        public:
            explicit invalid_ring_elem_types() : invalid_argument("invalid types") {}
        };

        [[nodiscard]] Scalar get_scalar() const;

        [[nodiscard]] Poly get_poly() const;

        [[nodiscard]] Poly &get_poly();
    
    };

    inline RingElem operator+(const RingElem &lhs, const RingElem &rhs) {
        RingElem res(lhs);
        res += rhs;
        return res;
    }

    inline RingElem operator-(const RingElem &lhs, const RingElem &rhs) {
        RingElem res(lhs);
        res -= rhs;
        return res;
    }

    inline RingElem operator*(const RingElem &lhs, const RingElem &rhs) {
        RingElem res(lhs);
        res *= rhs;
        return res;
    }

    inline RingElem operator/(const RingElem &lhs, const RingElem &rhs) {
        RingElem res(lhs);
        res /= rhs;
        return res;
    }

    bool operator==(const RingElem &lhs, const RingElem &rhs);

    inline bool operator!=(const RingElem &lhs, const RingElem &rhs) {
        return !operator==(lhs, rhs);
    }

    std::ostream &operator<<(std::ostream &out, const RingElem &elem);

    class EncodingElem {
    protected:
        inline static std::vector<::seal::SEALContext> contexts;
        // Use pointers instead of values as an ugly hack.
        // std::vectors requires a copy-constructor to be available, whereas SEAL
        // deletes them for BatchEncoder and Evaluator
        inline static std::vector<::seal::BatchEncoder *> encoders;
        inline static std::vector<::seal::Evaluator *> evaluators;

        std::vector<::seal::Ciphertext> ciphertexts;

        //        EncodingElem() = delete;

    public:
        using PublicKey = nullptr_t;  // No keying material needed to evaluate affine
        // combinations of ciphertexts
        using SecretKey = vector<::seal::SecretKey>;
        class decoding_error : std::invalid_argument {
        public:
            explicit decoding_error() : invalid_argument("decoding error") {}
            explicit decoding_error(const string &msg)
                    : invalid_argument("decoding error: " + msg) {}
        };

        /*
         * Constructor
         */
        EncodingElem() = default;

        EncodingElem(const EncodingElem &other) : ciphertexts(other.ciphertexts) {
            assert(!other.ciphertexts.empty());
        }

        [[nodiscard]] bool is_empty() const { return this->ciphertexts.empty(); }

        size_t get_cipher_size() const {
            return this->ciphertexts.size();
        }

        /*
         * Static
         */
        static std::tuple<PublicKey, SecretKey> keygen() {
            SecretKey sk;
            sk.reserve(get_contexts().size());
            for (const auto &context : get_contexts()) {
                ::seal::KeyGenerator keygen(context);
                sk.push_back(keygen.secret_key());
            }
            PublicKey pk = nullptr;

            return {nullptr, sk};
        }

        static void set_context(size_t N = 0) {
            // TODO: find (joint) primes Q_1, ..., Q_L for encoding schemes s.t.
            // Q_1 > q_l, and Q, resp. L are just barely big enough to allow for a
            // linear homomorphism
            const ::seal::SEALContext &ring_context = RingElem::get_context();
            auto ring_params = ring_context.first_context_data()->parms();
            vector<::seal::SEALContext> enc_contexts;
            enc_contexts.reserve(ring_params.coeff_modulus().size());

            auto poly_modulus_degree = (N > 0) ? N : ring_params.poly_modulus_degree();
            auto coeff_modulus = ::seal::CoeffModulus::BFVDefault(poly_modulus_degree);

            for (size_t i = 0; i < ring_params.coeff_modulus().size(); i++) {
                ::seal::EncryptionParameters enc_params(::seal::scheme_type::bgv);
                enc_params.set_poly_modulus_degree(poly_modulus_degree);
                enc_params.set_plain_modulus(ring_params.coeff_modulus()[i].value());
                enc_params.set_coeff_modulus(coeff_modulus);
                ::seal::SEALContext context(enc_params);

                if (context.first_context_data()->qualifiers().parameter_error !=
                    ::seal::EncryptionParameterQualifiers::error_type::success) {
                    std::cerr
                            << context.first_context_data()->qualifiers().parameter_error_name()
                            << std::endl;
                    std::cerr << context.first_context_data()
                            ->qualifiers()
                            .parameter_error_message()
                              << std::endl;
                    throw std::invalid_argument("");
                }

                assert(context.first_context_data()->qualifiers().using_batching == true);

                //                assert(context.using_keyswitching() == false); //TODO:
                //                can we always force this to be false while having enough
                //                noise budget for (potentially) many additions?

                enc_contexts.push_back(context);
            }
            set_contexts(enc_contexts);
        }

        static void set_contexts(const vector<::seal::SEALContext> &contexts_) {
            if (contexts.empty()) {
                contexts = vector<::seal::SEALContext>(contexts_);
                encoders = vector<::seal::BatchEncoder *>();
                evaluators = vector<::seal::Evaluator *>();
                for (const ::seal::SEALContext &c : contexts) {
                    encoders.push_back(new ::seal::BatchEncoder(c));
                    evaluators.push_back(new ::seal::Evaluator(c));
                }
            } else {
                throw std::invalid_argument("cannot re-set contexts once set");
            }
        }

        static std::vector<::seal::SEALContext> &get_contexts() {
            if (contexts.empty()) {
                throw std::invalid_argument("context not set");
            } else {
                return contexts;
            }
        }

        // Encode all elements in rs using the same BatchEncoder and Encryptor objects
        // for efficiency
        static std::vector<EncodingElem> encode(const SecretKey &keygen,
                                                const std::vector<RingElem> &rs);

        static EncodingElem inner_product(
                vector<EncodingElem>::const_iterator a_start,
                vector<EncodingElem>::const_iterator a_end,
                vector<RingElem>::const_iterator b_start,
                vector<RingElem>::const_iterator b_end);

        static RingElem decode(const SecretKey &sk, const EncodingElem &e);

        /*
         * Members
         */
        [[nodiscard]] size_t size_in_bits() const;

        [[nodiscard]] static size_t size_in_bits_pk(const PublicKey &pk) { return 0; }

        [[nodiscard]] static size_t size_in_bits_sk(const SecretKey &sk) {
            size_t size = 0;
            for (size_t i = 0; i < sk.size(); i++) {
                auto context = get_contexts()[i];
                for (const auto &q_i :
                        context.first_context_data()->parms().coeff_modulus()) {
                    size += q_i.bit_count() *
                            context.first_context_data()->parms().poly_modulus_degree();
                }
            }
            return size;
        }

        bool saveElem(std::string filePath){
            std::string dir = filePath;
            if (!dir.empty() && dir.back() == '/') {
                dir.erase(dir.size() - 1);  // 去除最后一个字符
            }
            std::filesystem::create_directories(dir);

            size_t ciphernum = ciphertexts.size();
            std::string ciphernum_bin = filePath + "ciphernum.bin";
            std::ofstream ofs(ciphernum_bin, std::ios::binary); // 以二进制方式打开文件
            if (!ofs) {
                std::cerr << "Error opening file for writing: " << ciphernum_bin << std::endl;
                return false;
            }
            ofs.write(reinterpret_cast<const char*>(&ciphernum), sizeof(size_t));
            ofs.close();



            for(size_t i=0;i<ciphernum;i++){
                std::string istr = std::to_string(i);
                std::string savepath = filePath + "cipher" + istr + "/";
                // std::string savepath = filePath + "cipher" + istr + ".bin";
                // std::ofstream ofs1(savepath, std::ios::binary); // 以二进制方式打开文件
                // if (!ofs1) {
                //     std::cerr << "Error opening file for writing: " << savepath << std::endl;
                //     return false;
                // }
                // ciphertexts[i].save(ofs1);
                // ofs1.close();
                ciphertexts[i].my_save(savepath);
            }

            return true;
        }

        bool loadElem(std::string filePath, const ::seal::SEALContext &context){
            size_t ciphernum;
            std::string ciphernum_bin = filePath + "ciphernum.bin";
            std::ifstream ifs(ciphernum_bin, std::ios::binary); // 以二进制方式打开文件
            if (!ifs) {
                std::cerr << "Error opening file for reading:" << ciphernum_bin << std::endl;
                return false;
            }
            ifs.read(reinterpret_cast<char*>(&ciphernum), sizeof(size_t));
            ifs.close();
            
            this->ciphertexts.resize(ciphernum);
            // ciphertexts.clear();
            for(size_t i=0;i<ciphernum;i++){
                std::string istr = std::to_string(i);
                std::string loadpath = filePath + "cipher" + istr + "/";
                // std::string loadpath = filePath + "cipher" + istr + ".bin";
                // std::ifstream ifs1(loadpath, std::ios::binary); // 以二进制方式打开文件
                // if (!ifs1) {
                //     std::cerr << "Error opening file for reading: " << loadpath << std::endl;
                //     return false;
                // }
                // std::cout<<"cipherload debug1"<<std::endl;
                // ::seal::Ciphertext ctmp;
                // std::cout<<"cipherload debug2"<<std::endl;
                // ctmp.load(context, ifs1);
                // ifs1.close();
                // std::cout<<"cipherload debug3"<<std::endl;
                // // ciphertexts[i] = ctmp;
                // ciphertexts.push_back(ctmp);
                // std::cout<<"cipherload debug4"<<std::endl;
                // ::seal::Ciphertext ctmp;
                // ctmp.my_load(loadpath);
                // ciphertexts.push_back(ctmp);
                this->ciphertexts[i].my_load(loadpath);
            }

            // std::cout<<"cipher_nums: "<<this->ciphertexts.size()<<std::endl;

            return true;
        }


        EncodingElem &operator+=(const EncodingElem &other);

        EncodingElem &operator*=(const RingElem &other);

        explicit EncodingElem(std::vector<::seal::Ciphertext> ciphertexts)
                : ciphertexts(std::move(ciphertexts)) {}

        EncodingElem &modswitch_inplace();

        friend bool operator==(const EncodingElem &lhs, const EncodingElem &rhs);
    };

    inline EncodingElem operator+(const EncodingElem &lhs,
                                  const EncodingElem &rhs) {
        EncodingElem res(lhs);
        res += rhs;
        return res;
    }

    inline EncodingElem operator*(const EncodingElem &lhs, const RingElem &rhs) {
        EncodingElem res(lhs);
        res *= rhs;
        return res;
    }

    inline EncodingElem operator*(const RingElem &lhs, const EncodingElem &rhs) {
        EncodingElem res(rhs);
        res *= lhs;
        return res;
    }

    inline bool operator==(const EncodingElem &lhs, const EncodingElem &rhs) {
        if (lhs.ciphertexts.size() != rhs.ciphertexts.size()) {
            return false;
        }
        for (size_t i = 0; i < lhs.ciphertexts.size(); i++) {
            assert(lhs.ciphertexts[i].size() == rhs.ciphertexts[i].size());
            for (size_t j = 0; j < lhs.ciphertexts[i].size(); j++) {
                ::polytools::SealPoly l(RingElem::get_context(), lhs.ciphertexts[i], j);
                ::polytools::SealPoly r(RingElem::get_context(), rhs.ciphertexts[i], j);
                if (!l.is_equal(r)) {
                    return false;
                }
            }
        }
        return true;
    }

//    class EncodingElem_BP{
//    public:
//    private:
//        vector<G1> s;
//        vector<G1> st;
//        G1 g1 = G1::one();
//        Fr t = Fr::one();
//        g1 = t * g1;
//    };

}  // namespace ringsnark::seal

namespace std {
    template <>
    struct hash<ringsnark::seal::RingElem> {
        size_t operator()(const ringsnark::seal::RingElem &r) const {
            return r.hash();
        }
    };
}  // namespace std
template <typename T>
inline void print_vector(std::vector<T> vec, std::size_t print_size = 4, int prec = 3)
{
    /*
    Save the formatting information for std::cout.
    */
    std::ios old_fmt(nullptr);
    old_fmt.copyfmt(std::cout);

    std::size_t slot_count = vec.size();

    std::cout << std::fixed << std::setprecision(prec);
    std::cout << std::endl;
    if (slot_count <= 2 * print_size)
    {
        std::cout << "    [";
        for (std::size_t i = 0; i < slot_count; i++)
        {
            std::cout << " " << vec[i] << ((i != slot_count - 1) ? "," : " ]\n");
        }
    }
    else
    {
        vec.resize(std::max(vec.size(), 2 * print_size));
        std::cout << "    [";
        for (std::size_t i = 0; i < print_size; i++)
        {
            std::cout << " " << vec[i] << ",";
        }
        if (vec.size() > 2 * print_size)
        {
            std::cout << " ...,";
        }
        for (std::size_t i = slot_count - print_size; i < slot_count; i++)
        {
            std::cout << " " << vec[i] << ((i != slot_count - 1) ? "," : " ]\n");
        }
    }
    std::cout << std::endl;

    /*
    Restore the old std::cout formatting.
    */
    std::cout.copyfmt(old_fmt);
}

/*
Helper function: Prints a matrix of values.
*/
template <typename T>
inline void print_matrix(std::vector<T> matrix, std::size_t row_size)
{
    /*
    We're not going to print every column of the matrix (there are 2048). Instead
    print this many slots from beginning and end of the matrix.
    */
    std::size_t print_size = 5;

    std::cout << std::endl;
    std::cout << "    [";
    for (std::size_t i = 0; i < print_size; i++)
    {
        std::cout << std::setw(3) << std::right << matrix[i] << ",";
    }
    std::cout << std::setw(3) << " ...,";
    for (std::size_t i = row_size - print_size; i < row_size; i++)
    {
        std::cout << std::setw(3) << matrix[i] << ((i != row_size - 1) ? "," : " ]\n");
    }
    std::cout << "    [";
    for (std::size_t i = row_size; i < row_size + print_size; i++)
    {
        std::cout << std::setw(3) << matrix[i] << ",";
    }
    std::cout << std::setw(3) << " ...,";
    for (std::size_t i = 2 * row_size - print_size; i < 2 * row_size; i++)
    {
        std::cout << std::setw(3) << matrix[i] << ((i != 2 * row_size - 1) ? "," : " ]\n");
    }
    std::cout << std::endl;
}

/*
Helper function: Print line number.
*/
inline void print_line(int line_number)
{
    std::cout << "Line " << std::setw(3) << line_number << " --> ";
}

#include "seal_ring.tcc"

#endif