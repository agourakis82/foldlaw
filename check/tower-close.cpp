// Tower blocks for quaternionic pairs of alternative elements, levels 5..7, standard Q = H(e1,e2).
// Complement of E_m: the units whose index has bit 2 set. Everything exact (integers, ranks mod two primes).
#include <array>
#include <cstdio>
#include <cstdlib>
#include <map>
#include <vector>
using std::vector;
static constexpr int DMAX = 128;
struct V { int n; std::array<long long, DMAX> c{}; };
static V zero(int n) { V v; v.n = n; return v; }
static V add(V x, const V& y) { for (int i = 0; i < x.n; i++) x.c[i] += y.c[i]; return x; }
static V sub(V x, const V& y) { for (int i = 0; i < x.n; i++) x.c[i] -= y.c[i]; return x; }
static bool is0(const V& a) { for (int i = 0; i < a.n; i++) if (a.c[i]) return false; return true; }
static long long dot(const V& a, const V& b) { long long s = 0; for (int i = 0; i < a.n; i++) s += a.c[i]*b.c[i]; return s; }
static void mul_rec(const long long* x, const long long* y, long long* r, int n) {
  if (n == 1) { r[0] = x[0]*y[0]; return; }
  int h = n/2; long long xa[DMAX], xb[DMAX], ya[DMAX], yb[DMAX], t1[DMAX], t2[DMAX], cx[DMAX], cy[DMAX];
  for (int i = 0; i < h; i++) { xa[i]=x[i]; xb[i]=x[h+i]; ya[i]=y[i]; yb[i]=y[h+i]; }
  for (int i = 0; i < h; i++) { cx[i]= i ? -xb[i] : xb[i]; cy[i]= i ? -xa[i] : xa[i]; }
  mul_rec(xa, ya, t1, h); mul_rec(yb, cx, t2, h);
  for (int i = 0; i < h; i++) r[i] = t1[i] - t2[i];
  mul_rec(cy, yb, t1, h); mul_rec(ya, xb, t2, h);
  for (int i = 0; i < h; i++) r[h+i] = t1[i] + t2[i];
}
static V mul(const V& x, const V& y) { V r = zero(x.n); mul_rec(x.c.data(), y.c.data(), r.c.data(), x.n); return r; }
static V W(const V& x, const V& y, const V& z) { return add(mul(mul(x, z), y), mul(x, mul(z, y))); }
static V As(const V& x, const V& y, const V& z) { return sub(mul(mul(x, z), y), mul(x, mul(z, y))); }
static V unit(int n, int i) { V v = zero(n); v.c[i] = 1; return v; }
static long long mpow(long long a, long long e, long long p) { long long r = 1; a %= p; if (a < 0) a += p; while (e) { if (e & 1) r = r*a%p; a = a*a%p; e >>= 1; } return r; }
static int rank_p(vector<vector<long long>> M, long long p) {
  int n = (int)M.size(); if (!n) return 0; int m = (int)M[0].size(), r = 0;
  for (int col = 0; col < m && r < n; col++) {
    int piv = -1; for (int i = r; i < n; i++) { long long v = M[i][col]%p; if (v < 0) v += p; if (v) { piv = i; break; } }
    if (piv < 0) continue; std::swap(M[r], M[piv]);
    long long inv = mpow(M[r][col], p-2, p);
    for (int j = 0; j < m; j++) { long long v = M[r][j]%p; if (v < 0) v += p; M[r][j] = v*inv%p; }
    for (int i = 0; i < n; i++) if (i != r) { long long f = M[i][col]%p; if (f < 0) f += p; if (!f) continue;
      for (int j = 0; j < m; j++) { long long v = (M[i][j] - f*M[r][j])%p; if (v < 0) v += p; M[i][j] = v; } }
    r++;
  }
  return r;
}
static int rank2(const vector<vector<long long>>& M) { int a = rank_p(M, 1000003), b = rank_p(M, 1048573); if (a != b) { std::printf("RANK MISMATCH\n"); std::exit(2); } return a; }
// Moreno's parametrisation, recursive. Pure alternative element of A_m, m >= 3, with octonion seed in span{e1,e2,e3}.
struct Rng { unsigned long long s; long long operator()(int R) { s ^= s<<13; s ^= s>>7; s ^= s<<17; return (long long)(s % (2*R+1)) - R; } };
static V altpure(int m, Rng& g, int R, bool sparse) {
  if (m == 3) { V a = zero(8); for (int i = 1; i <= 3; i++) a.c[i] = g(R); if (sparse) for (int i = 1; i <= 3; i++) if (g(1) == 0) a.c[i] = 0; return a; }
  V a = altpure(m-1, g, R, sparse);
  long long s = g(R), t = g(R);
  if (sparse) { if (g(1) == 0) s = 0; if (g(1) == 0) t = 0; }
  int h = 1 << (m-1);
  V x = zero(2*h);
  for (int i = 0; i < h; i++) { x.c[i] = a.c[i]; x.c[h+i] = t*a.c[i]; }
  x.c[h] += s;
  return x;
}
static bool isAlt(const V& x) {
  int n = x.n; V xx = mul(x, x);
  for (int k = 0; k < n; k++) { V e = unit(n, k); if (!is0(sub(mul(xx, e), mul(x, mul(xx.n ? x : x, e))))) return false; }
  return true;
}
// nullity of an operator restricted to a list of basis indices (operator maps the span into itself; we check that)
static int nullityOn(const V& x, const V& y, const vector<int>& idx, bool anti, bool* invariant) {
  int n = x.n; int k = (int)idx.size();
  vector<vector<long long>> M(n, vector<long long>(k));
  vector<char> inset(n, 0); for (int i : idx) inset[i] = 1;
  bool inv = true;
  for (int j = 0; j < k; j++) {
    V w = anti ? W(x, y, unit(n, idx[j])) : As(x, y, unit(n, idx[j]));
    for (int i = 0; i < n; i++) { M[i][j] = w.c[i]; if (!inset[i] && w.c[i]) inv = false; }
  }
  if (invariant) *invariant = inv;
  return k - rank2(M);
}
struct Rec { int N, A, NE, AE, beta, alpha; bool inv; };
static Rec analyse(const V& x, const V& y) {
  int n = x.n;
  vector<int> all, E, F;
  for (int i = 0; i < n; i++) { all.push_back(i); if (i & 4) F.push_back(i); else E.push_back(i); }
  Rec r; bool i1, i2, i3, i4;
  r.N = nullityOn(x, y, all, true, nullptr);
  r.A = nullityOn(x, y, all, false, nullptr);
  r.NE = nullityOn(x, y, E, true, &i1);
  r.AE = nullityOn(x, y, E, false, &i2);
  r.beta = nullityOn(x, y, F, true, &i3);
  r.alpha = nullityOn(x, y, F, false, &i4);
  r.inv = i1 && i2 && i3 && i4;
  return r;
}
// Block form on the top complement F = F_lo + F_hi: W(u,v) = (Au+Bv, -Bu+Av)?  And As(u,v) = (A'u+B'v, B'u-A'v)?
static void blockForm(const V& x, const V& y, int& wform, int& aform) {
  int n = x.n, h = n/2;
  vector<int> Flo; for (int i = 0; i < h; i++) if (i & 4) Flo.push_back(i);
  wform = 1; aform = 1;
  for (int j : Flo) {
    V w0 = W(x, y, unit(n, j)), w1 = W(x, y, unit(n, h+j));
    V a0 = As(x, y, unit(n, j)), a1 = As(x, y, unit(n, h+j));
    for (int i : Flo) {
      if (w0.c[h+i] != -w1.c[i] || w1.c[h+i] != w0.c[i]) wform = 0;
      // associator: test both candidate shapes, record which
      if (a0.c[h+i] != a1.c[i] || a1.c[h+i] != -a0.c[i]) aform = 0;
    }
  }
}
int main(int argc, char** argv) {
  int m = argc > 1 ? std::atoi(argv[1]) : 5;
  int want = argc > 2 ? std::atoi(argv[2]) : 2000;
  int target = argc > 3 ? std::atoi(argv[3]) : -1; // hunt for a specific total N
  int n = 1 << m;
  Rng g{ (unsigned long long)(12345 + 7*m) };
  std::map<std::pair<int,int>, int> histNA, histBlocks;
  std::map<int,int> histBeta, histAlpha;
  int pairs = 0, inv = 0, addN = 0, addA = 0, wf = 0, af = 0, altok = 0;
  for (int trial = 0; trial < 50*want && pairs < want; trial++) {
    bool sparse = trial % 2;
    V x = altpure(m, g, 2, sparse), y = altpure(m, g, 2, sparse);
    if (is0(x) || is0(y) || dot(x, y)) continue;
    pairs++;
    if (pairs <= 200 || (pairs % 50 == 0)) { if (isAlt(x) && isAlt(y)) altok++; else { std::printf("NOT ALTERNATIVE\n"); std::exit(3); } }
    Rec r = analyse(x, y);
    inv += r.inv; addN += (r.N == r.NE + r.beta); addA += (r.A == r.AE + r.alpha);
    int w, a; blockForm(x, y, w, a); wf += w; af += a;
    histNA[{r.N, r.A}]++; histBeta[r.beta]++; histAlpha[r.alpha]++; histBlocks[{r.NE, r.beta}]++;
    if (target >= 0 && r.N == target) {
      std::printf("TARGET N=%d: A=%d NE=%d beta=%d\n x:", r.N, r.A, r.NE, r.beta);
      for (int i = 0; i < n; i++) if (x.c[i]) std::printf(" %+lld e%d", x.c[i], i);
      std::printf("\n y:");
      for (int i = 0; i < n; i++) if (y.c[i]) std::printf(" %+lld e%d", y.c[i], i);
      std::printf("\n");
      target = -2;
    }
  }
  std::printf("level %d: pairs %d (alternativity spot-checked %d), invariance %d, additivity N %d A %d, W form %d, As form %d\n",
              m, pairs, altok, inv, addN, addA, wf, af);
  std::printf("beta_%d:", m); for (auto& kv : histBeta) std::printf(" %d->%d", kv.first, kv.second); std::printf("\n");
  std::printf("alpha_%d:", m); for (auto& kv : histAlpha) std::printf(" %d->%d", kv.first, kv.second); std::printf("\n");
  std::printf("(N,A):"); for (auto& kv : histNA) std::printf(" (%d,%d)x%d", kv.first.first, kv.first.second, kv.second); std::printf("\n");
  std::printf("(N_E,beta):"); for (auto& kv : histBlocks) std::printf(" (%d,%d)x%d", kv.first.first, kv.first.second, kv.second); std::printf("\n");
}
