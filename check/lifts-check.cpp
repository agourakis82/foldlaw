// Peer-review check of Corollary 4: four lifts of a quaternionic pair of A_4 to A_5.
// Same-side lifts (x,0),(y,0) and (0,x),(0,y): expect (2N+4, 2A-4). Cross lifts: (2A-4, 2N+4).
#include <array>
#include <cstdio>
#include <vector>
#include <random>
#include <map>
#include <cstdlib>
using std::vector;
static constexpr int D = 32;
struct V { std::array<long long, D> c{}; };
static V add(V x, const V& y) { for (int i = 0; i < D; i++) x.c[i] += y.c[i]; return x; }
static V sub(V x, const V& y) { for (int i = 0; i < D; i++) x.c[i] -= y.c[i]; return x; }
static bool is0(const V& a) { for (int i = 0; i < D; i++) if (a.c[i]) return false; return true; }
static long long dot(const V& a, const V& b) { long long s = 0; for (int i = 0; i < D; i++) s += a.c[i]*b.c[i]; return s; }
static void mul_rec(const long long* x, const long long* y, long long* r, int n) {
  if (n == 1) { r[0] = x[0]*y[0]; return; }
  int h = n/2; long long xa[D], xb[D], ya[D], yb[D], t1[D], t2[D], cx[D], cy[D];
  for (int i = 0; i < h; i++) { xa[i]=x[i]; xb[i]=x[h+i]; ya[i]=y[i]; yb[i]=y[h+i]; }
  for (int i = 0; i < h; i++) { cx[i]= i ? -xb[i] : xb[i]; cy[i]= i ? -xa[i] : xa[i]; }
  mul_rec(xa, ya, t1, h); mul_rec(yb, cx, t2, h);
  for (int i = 0; i < h; i++) r[i] = t1[i] - t2[i];
  mul_rec(cy, yb, t1, h); mul_rec(ya, xb, t2, h);
  for (int i = 0; i < h; i++) r[h+i] = t1[i] + t2[i];
}
static V mul(const V& x, const V& y) { V r; mul_rec(x.c.data(), y.c.data(), r.c.data(), D); return r; }
static V W(const V& x, const V& y, const V& z) { return add(mul(mul(x, z), y), mul(x, mul(z, y))); }
static V As(const V& x, const V& y, const V& z) { return sub(mul(mul(x, z), y), mul(x, mul(z, y))); }
static V unit(int i) { V v; v.c[i] = 1; return v; }
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
// kernel dims of W and associator on the first n coordinates (n = 16 or 32)
static std::pair<int,int> dims(const V& x, const V& y, int n) {
  vector<vector<long long>> KW(n, vector<long long>(n)), KA(n, vector<long long>(n));
  for (int j = 0; j < n; j++) { V w = W(x, y, unit(j)), a = As(x, y, unit(j)); for (int i = 0; i < n; i++) { KW[i][j] = w.c[i]; KA[i][j] = a.c[i]; } }
  return {n - rank2(KW), n - rank2(KA)};
}
static bool quatPair(const V& x, const V& y, int n) {
  if (x.c[0] || y.c[0] || dot(x, y) != 0 || is0(x) || is0(y)) return false;
  if (!is0(sub(mul(mul(x,x),y), mul(x,mul(x,y))))) return false; if (!is0(sub(mul(mul(y,y),x), mul(y,mul(y,x))))) return false;
  return true;
}
static V shift(const V& x) { V r; for (int i = 0; i < 16; i++) r.c[16+i] = x.c[i]; return r; }
int main() {
  std::mt19937 g(11); std::uniform_int_distribution<int> d(-2, 2);
  static const int Eidx[8] = {0,1,2,3,8,9,10,11};
  int tot = 0, okSame = 0, okCross = 0, qp = 0;
  std::map<std::pair<int,int>,int> seen;
  for (int it = 0; it < 4000 && tot < 400; it++) {
    V x, y; for (int k = 1; k < 8; k++) { x.c[Eidx[k]] = d(g); y.c[Eidx[k]] = d(g); } x.c[1] = 1; y.c[1] = 0; y.c[1] = -dot(x, y);
    if (!quatPair(x, y, 16)) continue;
    tot++;
    auto [N, A] = dims(x, y, 16);
    seen[{N,A}]++;
    auto s1 = dims(x, y, 32), s2 = dims(shift(x), shift(y), 32);
    auto c1 = dims(x, shift(y), 32), c2 = dims(shift(x), y, 32);
    qp += quatPair(x, shift(y), 32) && quatPair(shift(x), y, 32) && quatPair(shift(x), shift(y), 32);
    bool same = s1 == std::make_pair(2*N+4, 2*A-4) && s2 == std::make_pair(2*N+4, 2*A-4);
    bool cross = c1 == std::make_pair(2*A-4, 2*N+4) && c2 == std::make_pair(2*A-4, 2*N+4);
    okSame += same; okCross += cross;
    if (!(same && cross) && tot < 40) std::printf("base (%d,%d): same (%d,%d),(%d,%d) cross (%d,%d),(%d,%d)\n", N, A, s1.first, s1.second, s2.first, s2.second, c1.first, c1.second, c2.first, c2.second);
  }
  { // the six witnesses of the note
    struct Wt { std::vector<std::pair<int,int>> x, y; };
    std::vector<Wt> ws = {
      {{{1,1},{2,-1}}, {{3,1},{9,-1}}}, {{{2,-1},{3,1},{9,-1},{10,1}}, {{1,-1},{3,-1},{9,-1},{11,-1}}},
      {{{1,1}}, {{10,1}}}, {{{1,1}}, {{2,1}}}, {{{1,1},{8,-1}}, {{2,1},{9,-1}}}, {{{1,1},{10,-1}}, {{1,1},{10,1}}} };
    for (auto& w : ws) { V x, y; for (auto& p : w.x) x.c[p.first] = p.second; for (auto& p : w.y) y.c[p.first] = p.second;
      auto [N, A] = dims(x, y, 16); auto s1 = dims(x, y, 32), s2 = dims(shift(x), shift(y), 32), c1 = dims(x, shift(y), 32), c2 = dims(shift(x), y, 32);
      std::printf("witness qp=%d (%d,%d) -> same (%d,%d),(%d,%d) cross (%d,%d),(%d,%d) expect (%d,%d)/(%d,%d)\n", quatPair(x,y,16), N, A, s1.first, s1.second, s2.first, s2.second, c1.first, c1.second, c2.first, c2.second, 2*N+4, 2*A-4, 2*A-4, 2*N+4); }
  }
  std::printf("level-4 quaternionic pairs %d (lifts all quaternionic: %d): same-side rule %d, cross rule %d\n", tot, qp, okSame, okCross);
  for (auto& kv : seen) std::printf(" (%d,%d)x%d", kv.first.first, kv.first.second, kv.second); std::printf("\n");
}
