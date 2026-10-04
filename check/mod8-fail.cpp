// Counterexample to beta_5 in 8Z.
// x = e3 - e16 - 2 e19,  y = e2 - e3 - 2 e10 + 2 e11 - e16
// Both alternative, orthogonal, anticommuting. dim Ass' = 8, dim Ass = 4, top block = 4.
#include <array>
#include <cstdio>
#include <vector>
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
static long long mpow(long long a, long long e, long long p) {
  long long r = 1; a %= p; if (a < 0) a += p;
  while (e) { if (e & 1) r = r*a%p; a = a*a%p; e >>= 1; }
  return r;
}
static int rank_p(vector<vector<long long>> M, long long p) {
  int n = (int)M.size(); if (!n) return 0;
  int m = (int)M[0].size(), r = 0;
  for (int col = 0; col < m && r < n; col++) {
    int piv = -1;
    for (int i = r; i < n; i++) { long long v = M[i][col]%p; if (v < 0) v += p; if (v) { piv = i; break; } }
    if (piv < 0) continue;
    std::swap(M[r], M[piv]);
    long long inv = mpow(M[r][col], p-2, p);
    for (int j = 0; j < m; j++) { long long v = M[r][j]%p; if (v < 0) v += p; M[r][j] = v*inv%p; }
    for (int i = 0; i < n; i++) if (i != r) {
      long long f = M[i][col]%p; if (f < 0) f += p; if (!f) continue;
      for (int j = 0; j < m; j++) { long long v = (M[i][j] - f*M[r][j])%p; if (v < 0) v += p; M[i][j] = v; }
    }
    r++;
  }
  return r;
}
static int rank2(const vector<vector<long long>>& M) {
  int a = rank_p(M, 1000003), b = rank_p(M, 1048573);
  if (a != b) { std::printf("rank mismatch %d %d\n", a, b); return -1; }
  return a;
}
int main() {
  V x, y;
  x.c[3] = 1; x.c[16] = -1; x.c[19] = -2;
  y.c[2] = 1; y.c[3] = -1; y.c[10] = -2; y.c[11] = 2; y.c[16] = -1;
  bool art = true;
  for (int k = 0; k < D; k++) {
    if (!is0(sub(mul(mul(x, x), unit(k)), mul(x, mul(x, unit(k)))))) art = false;
    if (!is0(sub(mul(mul(y, y), unit(k)), mul(y, mul(y, unit(k)))))) art = false;
  }
  vector<vector<long long>> KW(D, vector<long long>(D)), KA(D, vector<long long>(D));
  for (int j = 0; j < D; j++) {
    V w = W(x, y, unit(j)), a = As(x, y, unit(j));
    for (int i = 0; i < D; i++) { KW[i][j] = w.c[i]; KA[i][j] = a.c[i]; }
  }
  static const int Fb[8] = {4, 5, 6, 7, 12, 13, 14, 15};
  vector<vector<long long>> KF(D, vector<long long>(16));
  for (int j = 0; j < 8; j++) {
    V w0 = W(x, y, unit(Fb[j])), w1 = W(x, y, unit(16+Fb[j]));
    for (int i = 0; i < D; i++) { KF[i][j] = w0.c[i]; KF[i][8+j] = w1.c[i]; }
  }
  int rW = rank2(KW), rA = rank2(KA), rF = rank2(KF);
  std::printf("art=%d orth=%lld anticomm=%d Ass'=%d Ass=%d beta5=%d\n",
              art, dot(x, y), is0(add(mul(x, y), mul(y, x))), D-rW, D-rA, 16-rF);
  long long A[8][8] = {}, B[8][8] = {};
  for (int j = 0; j < 8; j++) {
    V w0 = W(x, y, unit(Fb[j])), w1 = W(x, y, unit(16+Fb[j]));
    for (int i = 0; i < 8; i++) { A[i][j] = w0.c[Fb[i]]; B[i][j] = w1.c[Fb[i]]; }
  }
  std::printf("p from A col4:"); for (int i = 0; i < 4; i++) std::printf(" %lld", A[i][4]);
  std::printf("\na from B col0:"); for (int i = 0; i < 4; i++) std::printf(" %lld", B[i][0]);
  std::printf("\nb from B col4:"); for (int i = 0; i < 4; i++) std::printf(" %lld", B[i][4]);
  std::printf("\nc from B col4 bot:"); for (int i = 0; i < 4; i++) std::printf(" %lld", B[4+i][4]);
  std::printf("\nshape:");
  bool shape = true;
  for (int i = 0; i < 4; i++) {
    if (A[i][0] || A[4+i][4]) shape = false;
    if (A[4+i][0] != -A[i][4]) shape = false;
    if (B[4+i][0] != -B[i][4]) shape = false; // bottom-left = -b, and b is real so -conj(b)=-b
    if (B[i][0] != B[4+i][4]) shape = false;
  }
  std::printf(" %d", shape);
  long long drift = 0;
  for (int i = 0; i < 8; i++) for (int j = 0; j < 8; j++) {
    long long ab = 0, ba = 0;
    for (int k = 0; k < 8; k++) { ab += A[i][k]*B[k][j]; ba += B[i][k]*A[k][j]; }
    drift += ab - ba;
  }
  std::printf(" commute=%d\n", drift == 0);
  return (art && dot(x, y)==0 && D-rW==8 && D-rA==4 && 16-rF==4) ? 0 : 1;
}
