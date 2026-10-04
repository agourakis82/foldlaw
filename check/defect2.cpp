// Structure test for quaternionic pairs of the sedenions S = O ⊕ Oℓ, x=(a,b), y=(c,d).
//
// Lemma A (containment): every quaternionic pair lies in E = Q ⊕ Qℓ for a quaternion
//   subalgebra Q ⊂ O (the imaginary parts of a,b,c,d span ≤ 3 dims closed under product).
// Lemma C (block formulas on E' = Q⊥ ⊕ Q⊥ℓ, coordinates (u',v') ∈ Q×Q via O = Q ⊕ Q e):
//   W'(u',v') = ( r v', -r u' ),              r  = [c,b] + [a,d]
//   A'(u',v') = ( k1 u' + m1 v', m2 u' + k2 v' ),
//     k1 = [a,c] + 2 Im(conj(d) b),  m1 = {conj(d),a} - {conj(b),c},
//     m2 = {a,d} - {b,c},            k2 = [a,c] + 2 Im(d conj(b)).
//   Prediction: dim Ass' = 4 + 8[r=0];  dim Ass = 4 + dim ker A'  (A' left-mult on Q², so ∈{0,4,8}).
//
// Test 1: all 7413 weight-2 quaternionic pairs: containment, and predicted vs direct (N,A).
// Test 2: random integer pairs inside E with Q = H(1,2): predicted vs direct, value census.
#include <array>
#include <cstdio>
#include <cstdlib>
#include <map>
#include <numeric>
#include <set>
#include <tuple>
#include <vector>
using std::array; using std::vector;
static constexpr int D = 16;
struct V { array<long long, D> c{}; };
static V basis(int i) { V v; v.c[i] = 1; return v; }
static V add(V x, const V& y) { for (int i = 0; i < D; i++) x.c[i] += y.c[i]; return x; }
static V sub(V x, const V& y) { for (int i = 0; i < D; i++) x.c[i] -= y.c[i]; return x; }
static V sc(V x, long long s) { for (int i = 0; i < D; i++) x.c[i] *= s; return x; }
static V cj(V x) { for (int i = 1; i < D; i++) x.c[i] = -x.c[i]; return x; }
static bool is0(const V& a) { for (int i = 0; i < D; i++) if (a.c[i]) return false; return true; }
static bool eq(const V& a, const V& b) { return is0(sub(a, b)); }
static long long dot(const V& a, const V& b) { long long s = 0; for (int i = 0; i < D; i++) s += a.c[i] * b.c[i]; return s; }
static void mul_rec(const long long* x, const long long* y, long long* r, int n) {
  if (n == 1) { r[0] = x[0] * y[0]; return; }
  int h = n / 2;
  long long xa[D], xb[D], ya[D], yb[D], t1[D], t2[D], cx[D], cy[D];
  for (int i = 0; i < h; i++) { xa[i] = x[i]; xb[i] = x[h + i]; ya[i] = y[i]; yb[i] = y[h + i]; }
  for (int i = 0; i < h; i++) { cx[i] = i ? -xb[i] : xb[i]; cy[i] = i ? -xa[i] : xa[i]; }
  mul_rec(xa, ya, t1, h); mul_rec(yb, cx, t2, h);
  for (int i = 0; i < h; i++) r[i] = t1[i] - t2[i];
  mul_rec(cy, yb, t1, h); mul_rec(ya, xb, t2, h);
  for (int i = 0; i < h; i++) r[h + i] = t1[i] + t2[i];
}
static V mul(const V& x, const V& y) { V r; mul_rec(x.c.data(), y.c.data(), r.c.data(), D); return r; }
static long long mpow(long long a, long long e, long long p) {
  long long r = 1; a %= p; if (a < 0) a += p;
  while (e) { if (e & 1) r = r * a % p; a = a * a % p; e >>= 1; } return r;
}
static int rank_p(vector<vector<long long>> M, long long p) {
  int n = (int)M.size(); if (!n) return 0; int m = (int)M[0].size(), r = 0;
  for (int col = 0; col < m && r < n; col++) {
    int piv = -1;
    for (int i = r; i < n; i++) { long long v = M[i][col] % p; if (v < 0) v += p; if (v) { piv = i; break; } }
    if (piv < 0) continue;
    std::swap(M[r], M[piv]);
    long long inv = mpow(M[r][col], p - 2, p);
    for (int j = 0; j < m; j++) { long long v = M[r][j] % p; if (v < 0) v += p; M[r][j] = v * inv % p; }
    for (int i = 0; i < n; i++) if (i != r) {
      long long f = M[i][col] % p; if (f < 0) f += p; if (!f) continue;
      for (int j = 0; j < m; j++) { long long v = (M[i][j] - f * M[r][j]) % p; if (v < 0) v += p; M[i][j] = v; }
    }
    r++;
  }
  return r;
}
static int rank2(const vector<vector<long long>>& M) {
  int r1 = rank_p(M, 1000003), r2 = rank_p(M, 1048573);
  if (r1 != r2) { std::fprintf(stderr, "rank mismatch\n"); std::exit(2); }
  return r1;
}
static int kerdim(const V& x, const V& y, int s) {
  vector<vector<long long>> M(D, vector<long long>(D));
  for (int k = 0; k < D; k++) {
    V e = basis(k);
    V w = s < 0 ? sub(mul(mul(x, e), y), mul(x, mul(e, y))) : add(mul(mul(x, e), y), mul(x, mul(e, y)));
    for (int i = 0; i < D; i++) M[i][k] = w.c[i];
  }
  return D - rank2(M);
}
static int rank_rows(const vector<V>& rows) {
  vector<vector<long long>> M;
  for (auto& v : rows) M.push_back(vector<long long>(v.c.begin(), v.c.end()));
  return rank2(M);
}
static bool quaternionic(const V& x, const V& y) {
  if (x.c[0] || y.c[0] || is0(x) || is0(y)) return false;
  if (dot(x, y)) return false;
  // [x,x,y] = 0 and [y,y,x] = 0
  if (!eq(mul(mul(x, x), y), mul(x, mul(x, y)))) return false;
  if (!eq(mul(mul(y, y), x), mul(y, mul(y, x)))) return false;
  return true;
}
// octonion components: lo(x) = (a,0), hi(x) = (b,0) as elements of O ⊂ S (coords 0..7)
static V lo(const V& x) { V r; for (int i = 0; i < 8; i++) r.c[i] = x.c[i]; return r; }
static V hi(const V& x) { V r; for (int i = 0; i < 8; i++) r.c[i] = x.c[8 + i]; return r; }
static V im(V x) { x.c[0] = 0; return x; }
static V comm(const V& p, const V& q) { return sub(mul(p, q), mul(q, p)); }
static V acomm(const V& p, const V& q) { return add(mul(p, q), mul(q, p)); }

// containment: imaginary parts of a,b,c,d span a subspace closed under product, dim ≤ 3
static bool contained_in_Q(const V& a, const V& b, const V& c, const V& d) {
  vector<V> gens = {im(a), im(b), im(c), im(d)};
  vector<V> span; for (auto& g : gens) if (!is0(g)) span.push_back(g);
  if (rank_rows(span) > 3) return false;
  for (auto& p : gens) for (auto& q : gens) {
    vector<V> t = span; t.push_back(im(mul(p, q)));
    if (rank_rows(t) > 3) return false;
  }
  return true;
}
// dim ker of (u,v) ↦ (k1 u + m1 v, m2 u + k2 v), u,v ∈ Q, with Q = span of a basis (4 vectors in O)
static int ker_quatmat(const V& k1, const V& m1, const V& m2, const V& k2, const vector<V>& Qb) {
  // columns: images of (q_j, 0) and (0, q_j); rows: coordinates in O ⊕ O (16 numbers)
  vector<vector<long long>> M(16, vector<long long>(8));
  for (int j = 0; j < 4; j++) {
    V u = Qb[j];
    V f1 = mul(k1, u), f2 = mul(m2, u);
    for (int i = 0; i < 8; i++) { M[i][j] = f1.c[i]; M[8 + i][j] = f2.c[i]; }
    V g1 = mul(m1, u), g2 = mul(k2, u);
    for (int i = 0; i < 8; i++) { M[i][4 + j] = g1.c[i]; M[8 + i][4 + j] = g2.c[i]; }
  }
  return 8 - rank2(M);
}
// a basis of Q ⊃ Im parts of a,b,c,d (fill up with products / fallback units)
static vector<V> Q_basis(const V& a, const V& b, const V& c, const V& d) {
  // two independent imaginary generators g1, g2 from the components; Q = span{1, g1, g2, g1 g2}
  vector<V> gens = {im(a), im(b), im(c), im(d)};
  V g1, g2; bool h1 = false, h2 = false;
  for (auto& g : gens) {
    if (is0(g)) continue;
    if (!h1) { g1 = g; h1 = true; continue; }
    if (!h2 && rank_rows({g1, g}) == 2) { g2 = g; h2 = true; break; }
  }
  if (!h1) g1 = basis(1), h1 = true;
  if (!h2) {
    // complete with an imaginary unit direction orthogonal to g1: Im(g1 e_i) for some i
    for (int i = 1; i < 8 && !h2; i++) {
      V h = im(mul(g1, basis(i)));
      if (!is0(h) && dot(h, g1) == 0 && rank_rows({g1, h}) == 2) { g2 = h; h2 = true; }
    }
  }
  // orthogonalise g2 against g1 is unnecessary: span{1,g1,g2,g1g2} is the quaternion
  // subalgebra generated whenever g1, g2 are independent imaginary octonions
  V g12 = im(mul(g1, g2));
  vector<V> Qb = {basis(0), g1, g2, g12};
  if (rank_rows(Qb) != 4) { std::fprintf(stderr, "Q basis degenerate\n"); std::exit(3); }
  return Qb;
}
struct Pred { int N, A, kerA; bool r0; V r, k1, m1, m2, k2; };
static Pred predict(const V& x, const V& y) {
  V a = lo(x), b = hi(x), c = lo(y), d = hi(y);
  Pred P;
  P.r = add(comm(c, b), comm(a, d));
  P.r0 = is0(P.r);
  P.k1 = add(comm(a, c), sc(im(mul(cj(d), b)), 2));
  P.m1 = sub(acomm(cj(d), a), acomm(cj(b), c));
  P.m2 = sub(acomm(a, d), acomm(b, c));
  P.k2 = add(comm(a, c), sc(im(mul(d, cj(b))), 2));
  vector<V> Qb = Q_basis(a, b, c, d);
  P.kerA = Qb.size() == 4 ? ker_quatmat(P.k1, P.m1, P.m2, P.k2, Qb) : -1;
  P.N = 4 + (P.r0 ? 8 : 0);
  P.A = 4 + P.kerA;
  return P;
}
static void show(const V& v) {
  std::printf("[");
  for (int i = 0; i < D; i++) if (v.c[i]) std::printf(" %+lld e%d", v.c[i], i);
  std::printf(" ]");
}
int main() {
  std::setvbuf(stdout, nullptr, _IONBF, 0);
  // ---- Test 1: weight-2 census ----
  {
    vector<V> vs;
    for (int i = 1; i <= 15; i++) for (int j = i + 1; j <= 15; j++) for (int s = -1; s <= 1; s += 2)
      vs.push_back(add(basis(i), sc(basis(j), s)));
    int pairs = 0, contained = 0, okN = 0, okA = 0, shownBad = 0;
    std::map<std::tuple<int,int>, int> byNA;
    std::map<std::tuple<bool,int>, int> byRK;   // (r==0, kerA')
    for (size_t p = 0; p < vs.size(); p++) for (size_t q = p + 1; q < vs.size(); q++) {
      const V& x = vs[p]; const V& y = vs[q];
      if (!quaternionic(x, y)) continue;
      pairs++;
      V a = lo(x), b = hi(x), c = lo(y), d = hi(y);
      bool cont = contained_in_Q(a, b, c, d);
      contained += cont;
      int N = kerdim(x, y, +1), A = kerdim(x, y, -1);
      Pred P = predict(x, y);
      okN += (P.N == N); okA += (P.A == A);
      byNA[{N, A}]++; byRK[{P.r0, P.kerA}]++;
      if ((P.N != N || P.A != A || !cont) && shownBad < 5) {
        shownBad++;
        std::printf("  MISMATCH contained=%d direct (N,A)=(%d,%d) predicted (%d,%d) kerA'=%d  x=", (int)cont, N, A, P.N, P.A, P.kerA);
        show(x); std::printf(" y="); show(y); std::printf("\n");
      }
    }
    std::printf("Test 1 (weight-2): quaternionic pairs=%d  contained in some Q⊕Qℓ: %d  N ok: %d  A ok: %d\n",
                pairs, contained, okN, okA);
    std::printf("  (N,A):"); for (auto& kv : byNA) std::printf("  (%d,%d)x%d", std::get<0>(kv.first), std::get<1>(kv.first), kv.second); std::printf("\n");
    std::printf("  (r=0, ker A'):"); for (auto& kv : byRK) std::printf("  (%d,%d)x%d", (int)std::get<0>(kv.first), std::get<1>(kv.first), kv.second); std::printf("\n");
  }
  // ---- Test 2: random integer pairs inside E = Q ⊕ Qℓ, Q = H(1,2) = span{e0,e1,e2,e3} ----
  {
    unsigned long long seed = 20261003ULL;
    auto rnd = [&]() { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; return seed; };
    auto ri = [&](int R) { return (long long)(rnd() % (2 * R + 1)) - R; };
    int pairs = 0, okN = 0, okA = 0, shownBad = 0;
    std::map<std::tuple<int,int>, int> byNA;
    std::map<std::tuple<bool,int>, int> byRK;
    std::map<std::tuple<int,int>, std::pair<V,V>> wit;
    for (int trial = 0; trial < 200000 && pairs < 20000; trial++) {
      V x, y;
      int R = 1 + (trial % 3);
      // x = (a,b): a ∈ span{e1,e2,e3}, b ∈ span{e0..e3} -> coords 1..3 and 8..11
      for (int i = 1; i <= 3; i++) x.c[i] = ri(R);
      for (int i = 8; i <= 11; i++) x.c[i] = ri(R);
      for (int i = 1; i <= 3; i++) y.c[i] = ri(R);
      for (int i = 8; i <= 11; i++) y.c[i] = ri(R);
      // force orthogonality by solving for one coordinate when possible
      long long s = dot(x, y);
      if (s) {
        // adjust y.c[k] for a k with x.c[k] = ±1
        int k = -1; for (int i : {1,2,3,8,9,10,11}) if (x.c[i] == 1 || x.c[i] == -1) { k = i; break; }
        if (k < 0) continue;
        y.c[k] -= s * x.c[k];
      }
      if (!quaternionic(x, y)) continue;   // should hold for all orthogonal imaginary pairs in E
      pairs++;
      int N = kerdim(x, y, +1), A = kerdim(x, y, -1);
      Pred P = predict(x, y);
      okN += (P.N == N); okA += (P.A == A);
      byNA[{N, A}]++; byRK[{P.r0, P.kerA}]++;
      if (!wit.count({N, A})) wit[{N, A}] = {x, y};
      if ((P.N != N || P.A != A) && shownBad < 5) {
        shownBad++;
        std::printf("  MISMATCH direct (N,A)=(%d,%d) predicted (%d,%d) kerA'=%d  x=", N, A, P.N, P.A, P.kerA);
        show(x); std::printf(" y="); show(y); std::printf("\n");
      }
    }
    std::printf("Test 2 (random in E, Q=H(1,2)): pairs=%d  N ok: %d  A ok: %d\n", pairs, okN, okA);
    std::printf("  (N,A):"); for (auto& kv : byNA) std::printf("  (%d,%d)x%d", std::get<0>(kv.first), std::get<1>(kv.first), kv.second); std::printf("\n");
    std::printf("  (r=0, ker A'):"); for (auto& kv : byRK) std::printf("  (%d,%d)x%d", (int)std::get<0>(kv.first), std::get<1>(kv.first), kv.second); std::printf("\n");
    for (auto& kv : wit) {
      std::printf("  witness (%d,%d): x=", std::get<0>(kv.first), std::get<1>(kv.first)); show(kv.second.first);
      std::printf(" y="); show(kv.second.second); std::printf("\n");
    }
  }
  // ---- Test 3: strata of ker A' by the zero pattern of (p, q, w, t), pairs in E ----
  {
    unsigned long long seed = 777ULL;
    auto rnd = [&]() { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; return seed; };
    auto ri = [&](int R) { return (long long)(rnd() % (2 * R + 1)) - R; };
    // (p=0, q=0, w=0, t=0, r=0) -> multiset of kerA'
    std::map<std::array<int,5>, std::map<int,int>> strata;
    int pairs = 0;
    for (int trial = 0; trial < 400000 && pairs < 60000; trial++) {
      V x, y; int R = 1 + (trial % 2);
      for (int i = 1; i <= 3; i++) x.c[i] = ri(R);
      for (int i = 8; i <= 11; i++) x.c[i] = ri(R);
      for (int i = 1; i <= 3; i++) y.c[i] = ri(R);
      for (int i = 8; i <= 11; i++) y.c[i] = ri(R);
      // sparsify sometimes to hit special strata
      if (trial % 3 == 0) for (int i : {1,2,3,8,9,10,11}) { if (rnd() % 2) x.c[i] = 0; if (rnd() % 2) y.c[i] = 0; }
      long long s = dot(x, y);
      if (s) { int k = -1; for (int i : {1,2,3,8,9,10,11}) if (x.c[i] == 1 || x.c[i] == -1) { k = i; break; } if (k < 0) continue; y.c[k] -= s * x.c[k]; }
      if (!quaternionic(x, y)) continue;
      pairs++;
      V a = lo(x), b = hi(x), c = lo(y), d = hi(y);
      V bv = im(b), dv = im(d); long long b0 = b.c[0], d0 = d.c[0];
      V p = add(im(mul(a, c)), im(mul(bv, dv)));                 // a×c + b⃗×d⃗
      V q = sub(sc(bv, d0), sc(dv, b0));                          // d0 b⃗ − b0 d⃗
      V w = sub(sc(a, d0), sc(c, b0));                            // d0 a − b0 c
      long long t = dot(a, dv) - dot(bv, c);                      // ⟨a,d⃗⟩ − ⟨b⃗,c⟩
      Pred P = predict(x, y);
      int A = kerdim(x, y, -1);
      if (P.A != A) { std::printf("  Test 3 mismatch\n"); }
      strata[{is0(p), is0(q), is0(w), t == 0, P.r0}][P.kerA]++;
    }
    std::printf("Test 3 (strata, %d pairs in E): columns p=0 q=0 w=0 t=0 r=0 -> kerA' counts\n", pairs);
    for (auto& kv : strata) {
      std::printf("   %d %d %d %d %d ->", kv.first[0], kv.first[1], kv.first[2], kv.first[3], kv.first[4]);
      for (auto& c : kv.second) std::printf("  ker=%d x%d", c.first, c.second);
      std::printf("\n");
    }
  }
  // ---- Test 4: octonion fact used in Lemma A: dim{w ∈ O : (a,w,b) = 0} = 4 when Im a, Im b independent ----
  {
    unsigned long long seed = 99ULL;
    auto rnd = [&]() { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; return seed; };
    int tested = 0, ok = 0;
    for (int trial = 0; trial < 3000; trial++) {
      V a, b;
      for (int i = 0; i < 8; i++) { a.c[i] = (long long)(rnd() % 5) - 2; b.c[i] = (long long)(rnd() % 5) - 2; }
      if (rank_rows({im(a), im(b)}) != 2) continue;
      tested++;
      vector<vector<long long>> M(8, vector<long long>(8));
      for (int k = 0; k < 8; k++) {
        V e = basis(k); V as = sub(mul(mul(a, e), b), mul(a, mul(e, b)));
        for (int i = 0; i < 8; i++) M[i][k] = as.c[i];
      }
      ok += (8 - rank2(M) == 4);
    }
    std::printf("Test 4 (octonion associator kernel of a generic pair = 4): %d/%d\n", ok, tested);
  }
  // ---- Test 5: Moreno's criterion in our convention: x=(a,b) ∈ Im S alternative iff [a,b]=0 ----
  {
    unsigned long long seed = 5ULL;
    auto rnd = [&]() { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; return seed; };
    int tested = 0, agree = 0, alt = 0;
    for (int trial = 0; trial < 4000; trial++) {
      V x;
      for (int i = 1; i < 16; i++) x.c[i] = (long long)(rnd() % 3) - 1;
      if (trial % 2) { // make [a,b]=0 often: b = s + t a
        V a = lo(x); long long s = (long long)(rnd() % 3) - 1, t = (long long)(rnd() % 3) - 1;
        for (int i = 0; i < 8; i++) x.c[8 + i] = (i == 0 ? s : 0) + t * a.c[i];
      }
      if (is0(x)) continue;
      tested++;
      bool isalt = true;
      for (int k = 0; k < 16 && isalt; k++) { V e = basis(k); if (!eq(mul(mul(x, x), e), mul(x, mul(x, e)))) isalt = false; }
      bool nu0 = is0(comm(lo(x), hi(x)));
      agree += (isalt == nu0); alt += isalt;
    }
    std::printf("Test 5 (alternative iff [a,b]=0): agree %d/%d, alternative elements seen %d\n", agree, tested, alt);
  }
  return 0;
}
