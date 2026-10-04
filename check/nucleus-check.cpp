// Lemma test: for nonzero pure a in A_n, is {b : [a,u,b] = 0 for all u} = span{1, a}?
// Also: Moreno necessity at level n+1 via (I) [a,u,b]=0 and (II) [a,a,u]+[b,b,u]=0.
#include <array>
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <random>
#include <map>
using std::vector;
static constexpr int D = 64;
struct V { std::array<long long, D> c{}; };
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
static int N;
static V mul(const V& x, const V& y) { V r; mul_rec(x.c.data(), y.c.data(), r.c.data(), N); return r; }
static V sub(V x, const V& y) { for (int i = 0; i < N; i++) x.c[i] -= y.c[i]; return x; }
static V As(const V& x, const V& y, const V& z) { return sub(mul(mul(x, y), z), mul(x, mul(y, z))); }
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
// dim { b : [a,u,b] = 0 for all u }  (linear in b; rows (u,i), cols j)
static int nucleusDim(const V& a) {
  vector<vector<long long>> M(N*N, vector<long long>(N));
  for (int j = 0; j < N; j++) for (int u = 0; u < N; u++) { V r = As(a, unit(u), unit(j)); for (int i = 0; i < N; i++) M[u*N+i][j] = r.c[i]; }
  return N - rank2(M);
}
int main(int argc, char** argv) {
  int n = argc > 1 ? std::atoi(argv[1]) : 4; int want = argc > 2 ? std::atoi(argv[2]) : 200; int R = argc > 3 ? std::atoi(argv[3]) : 2;
  N = 1 << n;
  std::mt19937 g(5); std::uniform_int_distribution<int> d(-R, R);
  std::map<int,int> hist; std::map<int,int> histSparse;
  for (int it = 0; it < want; it++) {
    V a; for (int i = 1; i < N; i++) a.c[i] = d(g);
    bool z = true; for (int i = 1; i < N; i++) if (a.c[i]) z = false; if (z) continue;
    hist[nucleusDim(a)]++;
  }
  // sparse / structured a: single units, sums of two units (zero divisors), sums of three
  for (int i = 1; i < N; i++) { V a; a.c[i] = 1; histSparse[nucleusDim(a)]++; }
  for (int it = 0; it < want; it++) {
    V a; int k = 2 + (it % 3); for (int s = 0; s < k; s++) { int i = 1 + g() % (N-1); a.c[i] += (g() & 1) ? 1 : -1; }
    bool z = true; for (int i = 1; i < N; i++) if (a.c[i]) z = false; if (z) continue;
    histSparse[nucleusDim(a)]++;
  }
  // (I)&(II) versus alternativity of x = (a,b) in A_{n+1}, on three families
  {
    int M2 = 2*N; int keepN = N; N = M2;
    auto embed = [&](const V& a, const V& b) { V x; for (int i = 0; i < keepN; i++) { x.c[i] = a.c[i]; x.c[keepN+i] = b.c[i]; } return x; };
    auto isAlt = [&](const V& x) { for (int k = 0; k < N; k++) { V r = As(x, x, unit(k)); for (int i = 0; i < N; i++) if (r.c[i]) return false; } return true; };
    auto condI = [&](const V& a, const V& b) { N = keepN; bool ok = true; for (int k = 0; k < N && ok; k++) { V r = As(a, unit(k), b); for (int i = 0; i < N; i++) if (r.c[i]) ok = false; } N = M2; return ok; };
    auto condII = [&](const V& a, const V& b) { N = keepN; bool ok = true; for (int k = 0; k < N && ok; k++) { V r = As(a, a, unit(k)), q = As(b, b, unit(k)); for (int i = 0; i < N; i++) if (r.c[i] + q.c[i]) ok = false; } N = M2; return ok; };
    auto altIn = [&](const V& a) { N = keepN; bool ok = true; for (int k = 0; k < N && ok; k++) { V r = As(a, a, unit(k)); for (int i = 0; i < N; i++) if (r.c[i]) ok = false; } N = M2; return ok; };
    int agree = 0, tot = 0, f1 = 0, f2 = 0, f3 = 0;
    for (int it = 0; it < 150; it++) {
      V a, b; int fam = it % 3;
      if (fam == 0 || fam == 1) { // a = unit or random; b = s + t a
        if (fam == 0) a.c[1 + g() % (keepN-1)] = 1; else for (int i = 1; i < keepN; i++) a.c[i] = d(g);
        int s = d(g), t = d(g); for (int i = 0; i < keepN; i++) b.c[i] = t*a.c[i]; b.c[0] += s;
      } else { // a, b alternative basis-like, independent: two different units
        int i = 1 + g() % (keepN-1), j = 1 + g() % (keepN-1); if (i == j) j = (j % (keepN-1)) + 1; a.c[i] = 1; b.c[j] = 1; b.c[0] = d(g);
      }
      bool z = true; for (int i = 1; i < keepN; i++) if (a.c[i]) z = false; if (z) continue;
      V x = embed(a, b); bool alt = isAlt(x), I = condI(a, b), II = condII(a, b);
      tot++; agree += (alt == (I && II));
      if (fam == 0) f1 += alt; if (fam == 1) f2 += (!alt && I && !II && !altIn(a)) || (alt && altIn(a)); if (fam == 2) f3 += (!alt && II && !I);
    }
    std::printf("A_%d: alternative(x) == (I)&&(II) in %d/%d; family checks %d %d %d\n", n+1, agree, tot, f1, f2, f3);
    N = keepN;
  }
  std::printf("n=%d dense pure a: dim{b:[a,u,b]=0 all u} ->", n); for (auto& kv : hist) std::printf(" %d:%d", kv.first, kv.second);
  std::printf("\nn=%d sparse pure a (units, 2-3 term sums):", n); for (auto& kv : histSparse) std::printf(" %d:%d", kv.first, kv.second); std::printf("\n");
}
