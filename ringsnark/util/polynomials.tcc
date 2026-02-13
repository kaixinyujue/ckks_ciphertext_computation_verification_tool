#include <algorithm>
#include <boost/math/tools/polynomial.hpp>
#include <cstdint>

using size_t = std::size_t;
template <typename RingT>
using polynomial = boost::math::tools::polynomial<RingT>;
// 二分构建多项式
using namespace std;
//2024-4-24 分治计算分母的（x-xi）的联乘的系数，复杂度为n2logn.
template <typename RingT>
void binary_subpoly(const std::vector<RingT>& x, std::vector<std::vector<RingT>>& poly_divisor, int l, int r, int idx) {
    if (l == r - 1) {  // 基础情况
        poly_divisor[idx].push_back(-x[l]);  // xi
        poly_divisor[idx].push_back(RingT(1));  // 常数项
    } else {
        int mid = (l + r) / 2;
        int lidx = (idx << 1) + 1;  // 左子树
        int ridx = lidx+1;
        binary_subpoly(x,poly_divisor, l, mid, lidx);
        binary_subpoly(x,poly_divisor,mid, r, ridx);

        std::vector<RingT> left_poly = poly_divisor[lidx];
        std::vector<RingT> right_poly = poly_divisor[ridx];

        poly_divisor[idx] = poly_multiply(left_poly, right_poly);  // 左右多项式相乘
    }
}
template <typename RingT>
vector<RingT> bin_interpolate(const vector<RingT> &x, const vector<RingT> &y) {
    assert(x.size() == y.size());
    int n = x.size();
    int k, j, i;
    RingT phi, ff, b;
    std::cout<<"polynomials.tcc 11111"<<std::endl;
    vector<RingT> coeffs(n, RingT::zero());
    int p_length=int(pow(2,n));
    vector<vector<RingT>> poly_divisor(p_length-1);
    binary_subpoly(x,poly_divisor,0,n,0);
    auto s=poly_divisor[0];
    for (j = 0; j < n; j++) {
        phi = RingT(n);
        for (k = n - 1; k > 0; k--) {
            // phi = RingT(k) * s[k] + x[j] * phi;
            phi *= x[j];
            phi += s[k] * RingT(k);
        }
        ff = y[j] / phi;
        b = RingT::one();
        for (k = n - 1; k >= 0; k--) {
            // b = s[k] + x[j] * b;
            coeffs[k] += b * ff;
            b *= x[j];
            b += s[k];
        }
    }
    return coeffs;
}

template <typename RingT>
vector<RingT> interpolate(const vector<RingT> &x, const vector<RingT> &y) {
  assert(x.size() == y.size());
  int n = x.size();
  int k, j, i;
  RingT phi, ff, b;
//  std::cout<<"polynomials.tcc 11111"<<std::endl;
//  for(auto xi:y){
//      std::cout<<"xi:"<<xi<<endl;
//  }
  vector<RingT> coeffs(n, RingT::zero());
  vector<RingT> s(n, RingT::zero());
  s[n - 1] = -x[0];

  for (i = 1; i < n; i++) {
    for (j = n - i - 1; j < n - 1; j++) {
      s[j] -= x[i] * s[j + 1];
    }
    s[n - 1] -= x[i];
  }
//  int p_length=int(pow(2,n));
//  vector<vector<RingT>> poly_divisor(p_length-1);
//  cout<<poly_divisor.size()<<endl;
//  binary_subpoly(x,poly_divisor,0,n,0);
//  auto s=poly_divisor[0];
//  cout<<s.size()<<endl;
  for (j = 0; j < n; j++) {
    phi = RingT(n);
    for (k = n - 1; k > 0; k--) {
      // phi = RingT(k) * s[k] + x[j] * phi;
      phi *= x[j];
      phi += s[k] * RingT(k);
    }
    ff = y[j] / phi;
    b = RingT::one();
    for (k = n - 1; k >= 0; k--) {
      // b = s[k] + x[j] * b;
      coeffs[k] += b * ff;
      b *= x[j];
      b += s[k];
    }
  }
  return coeffs;
}
template <typename RingT>
RingT eval(const vector<RingT> &coeffs, const RingT &x) {
  RingT res(coeffs[coeffs.size() - 1]);
  for (int i = coeffs.size() - 2; i >= 0; i--) {
    res *= x;
    res += coeffs[i];
  }
  return res;
}

template <typename RingT>
inline bool is_zero(const vector<RingT> &coeffs) {
  return std::all_of(coeffs.begin(), coeffs.end(),
                     [](const RingT &c) { return c.is_zero(); });
}

template <typename RingT>
vector<RingT> multiply(const vector<RingT> &x, const vector<RingT> &y) {
  polynomial<RingT> x_poly(x), y_poly(y);
  x_poly *= y_poly;
  return x_poly.data();
}

template <typename RingT>
vector<RingT> add(const vector<RingT> &x, const vector<RingT> &y) {
  polynomial<RingT> x_poly(x), y_poly(y);
  x_poly += y_poly;
  return x_poly.data();
}

template <typename RingT>
vector<RingT> divide(const vector<RingT> &numerator,
                     const vector<RingT> &denominator) {
  polynomial<RingT> x_poly(numerator), y_poly(denominator);
  x_poly /= y_poly;
  return x_poly.data();
}