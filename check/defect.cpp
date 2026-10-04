// Defect census at the sedenions.
// For a quaternionic pair (x,y) in A_4 = S (dim 16), compute
//   N = dim Ass'[x,y] = dim ker (z -> (xz)y + x(zy))
//   A = dim Ass [x,y] = dim ker (z -> (xz)y - x(zy))
//   delta = N + A - 16
// and tabulate (N,A) against linear-algebra features of the pair that do not
// depend on a basis: the position of span{x,y} and of H = span{1,x,y,xy}
// relative to the lower octonion O (coords 0..7), the upper half Ol (8..15)
// and the block B = O + R.l (coords 0..8).
//
// Experiment A: the 7413 weight-2 pairs (signed sums of two imaginary units).
// Experiment B: integer orthogonal pairs inside each coordinate quaternion
//               H(i,j) = span{1,e_i,e_j,e_i e_j}, including generic directions.
//
// Exact integer arithmetic; ranks mod two primes; same multiplication as
// birth-function-v1.typ eq. (mul) and as quat-wall.cpp.
#include <array>
#include <cstdio>
#include <cstdlib>
#include <map>
#include <numeric>
#include <set>
#include <tuple>
#include <vector>
using std::array;
using std::vector;
static constexpr int D = 16;
struct V { array<long long, D> c{}; };
static V basis(int i) { V v; v.c[i] = 1; return v; }
static V add(V x, const V& y) { for (int i = 0; i < D; i++) x.c[i] += y.c[i]; return x; }
static V sub(V x, const V& y) { for (int i = 0; i < D; i++) x.c[i] -= y.c[i]; return x; }
static V sc(V x, long long s) { for (int i = 0; i < D; i++) x.c[i] *= s; return x; }
static bool is0(const V& a) { for (int i = 0; i < D; i++) if (a.c[i]) return false; return true; }
static bool eq(const V& a, const V& b) { return is0(sub(a, b)); }

// recursive CD multiplication on a window [o, o+n) of the 16-vector
static void mul_rec(const long long* x, const long long* y, long long* r, int n) {
  if (n == 1) { r[0] = x[0] * y[0]; return; }
  int h = n / 2;
  long long xa[D], xb[D], ya[D], yb[D], t1[D], t2[D], cx[D], cy[D];
  for (int i = 0; i < h; i++) { xa[i] = x[i]; xb[i] = x[h + i]; ya[i] = y[i]; yb[i] = y[h + i]; }
  // conj(xb): negate imaginary part
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
  if (r1 != r2) { std::fprintf(stderr, "rank mismatch between primes\n"); std::exit(2); }
  return r1;
}
// dim ker of z -> (xz)y + s * x(zy)
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
// dim (span rows  ∩  coordinate subspace with indices lo..hi)
static int dim_meet(const vector<V>& rows, int lo, int hi) {
  vector<V> all = rows;
  for (int i = lo; i <= hi; i++) all.push_back(basis(i));
  int rs = rank_rows(rows), ru = rank_rows(all);
  return rs + (hi - lo + 1) - ru;
}
static bool quaternionic(const V& x, const V& y) {
  if (x.c[0] || y.c[0]) return false;
  if (!is0(add(mul(x, y), mul(y, x)))) return false;           // anticommute
  V xy = mul(x, y), sq = mul(xy, xy);
  for (int i = 1; i < D; i++) if (sq.c[i]) return false;      // (xy)^2 real
  if (sq.c[0] >= 0) return false;                               // negative
  // span{1,x,y,xy} closed and 4-dimensional: check products land in the span
  vector<V> h = {basis(0), x, y, xy};
  if (rank_rows(h) != 4) return false;
  for (auto& a : h) for (auto& b : h) {
    vector<V> t = h; t.push_back(mul(a, b));
    if (rank_rows(t) != 4) return false;
  }
  return true;
}
static bool art_pair(const V& x, const V& y) {
  // x(xw) = x^2 w and (wx)x = w x^2 for w = y, and symmetric; x^2 = -|x|^2
  auto one = [&](const V& a, const V& w) {
    long long n2 = 0; for (int i = 0; i < D; i++) n2 += a.c[i] * a.c[i];
    return eq(mul(a, mul(a, w)), sc(w, -n2)) && eq(mul(mul(w, a), a), sc(w, -n2));
  };
  return one(x, y) && one(y, x);
}

struct Feat {
  int dXY_O, dXY_Ol;      // dim(span{x,y} ∩ O), dim(span{x,y} ∩ Ol)
  int dH_O, dH_Ol, dH_B;  // same for H = span{1,x,y,xy}; B = O + R l
  int xy_in_O, xy_in_Ol, xy_in_B;
  bool operator<(const Feat& o) const {
    return std::tie(dXY_O, dXY_Ol, dH_O, dH_Ol, dH_B, xy_in_O, xy_in_Ol, xy_in_B)
         < std::tie(o.dXY_O, o.dXY_Ol, o.dH_O, o.dH_Ol, o.dH_B, o.xy_in_O, o.xy_in_Ol, o.xy_in_B);
  }
};
static Feat features(const V& x, const V& y) {
  Feat f;
  vector<V> xy = {x, y};
  V p = mul(x, y);
  vector<V> h = {basis(0), x, y, p};
  f.dXY_O = dim_meet(xy, 0, 7); f.dXY_Ol = dim_meet(xy, 8, 15);
  f.dH_O = dim_meet(h, 0, 7); f.dH_Ol = dim_meet(h, 8, 15); f.dH_B = dim_meet(h, 0, 8);
  auto in = [&](int lo, int hi) { for (int i = 0; i < D; i++) if (p.c[i] && (i < lo || i > hi)) return 0; return 1; };
  f.xy_in_O = in(0, 7); f.xy_in_Ol = in(8, 15); f.xy_in_B = in(0, 8);
  return f;
}

struct Tab {
  std::map<Feat, std::map<std::pair<int,int>, int>> t;
  std::map<std::pair<int,int>, int> tot;
  void add(const Feat& f, int N, int A) { t[f][{N, A}]++; tot[{N, A}]++; }
  void print(const char* title) const {
    std::printf("== %s\n", title);
    std::printf("   totals (N,A):");
    for (auto& kv : tot) std::printf("  (%d,%d)x%d", kv.first.first, kv.first.second, kv.second);
    std::printf("\n");
    for (auto& kv : t) {
      const Feat& f = kv.first;
      std::printf("   XY∩O=%d XY∩Ol=%d | H∩O=%d H∩Ol=%d H∩B=%d | xy∈O=%d xy∈Ol=%d xy∈B=%d  ->",
                  f.dXY_O, f.dXY_Ol, f.dH_O, f.dH_Ol, f.dH_B, f.xy_in_O, f.xy_in_Ol, f.xy_in_B);
      for (auto& na : kv.second) std::printf("  (%d,%d)x%d", na.first.first, na.first.second, na.second);
      std::printf("%s\n", kv.second.size() == 1 ? "" : "   <-- not determined");
    }
  }
};

int main() {
  std::setvbuf(stdout, nullptr, _IONBF, 0);
  // ---------- Experiment A: weight-2 pairs ----------
  {
    vector<V> vs; vector<std::array<int,3>> id;
    for (int i = 1; i <= 15; i++) for (int j = i + 1; j <= 15; j++) for (int s = -1; s <= 1; s += 2) {
      vs.push_back(add(basis(i), sc(basis(j), s))); id.push_back({i, s, j});
    }
    Tab tab; int quat = 0, art = 0;
    std::map<std::pair<int,int>, std::array<int,3>> witness;
    for (size_t a = 0; a < vs.size(); a++) for (size_t b = a + 1; b < vs.size(); b++) {
      const V& x = vs[a]; const V& y = vs[b];
      if (!quaternionic(x, y)) continue;
      quat++;
      if (!art_pair(x, y)) continue;
      art++;
      int N = kerdim(x, y, +1), A = kerdim(x, y, -1);
      tab.add(features(x, y), N, A);
      if (!witness.count({N, A})) witness[{N, A}] = {(int)a, (int)b, 0};
    }
    std::printf("Experiment A: weight-2 quaternionic pairs=%d with art=%d\n", quat, art);
    tab.print("A: (N,A) by position of span{x,y} and H relative to O, Ol, B");
    std::printf("   one witness per (N,A):\n");
    for (auto& w : witness) {
      auto& p = id[w.second[0]]; auto& q = id[w.second[1]];
      std::printf("     (%d,%d): (e%d %+d e%d), (e%d %+d e%d)\n", w.first.first, w.first.second,
                  p[0], p[1], p[2], q[0], q[1], q[2]);
    }
  }
  // ---------- Experiment B: pairs inside coordinate quaternions ----------
  {
    // integer vectors (a,b,c) with entries in [-R,R], orthogonal pairs, both nonzero;
    // includes generic directions such as (1,2,3),(3,0,-1).
    const int R = 2;
    vector<array<int,3>> dirs;
    for (int a = -R; a <= R; a++) for (int b = -R; b <= R; b++) for (int c = -R; c <= R; c++)
      if (a || b || c) {
        // primitive, first nonzero positive
        int g = std::gcd(std::gcd(std::abs(a), std::abs(b)), std::abs(c));
        if (g != 1) continue;
        int first = a ? a : (b ? b : c);
        if (first < 0) continue;
        dirs.push_back({a, b, c});
      }
    std::printf("\nExperiment B: %zu primitive directions per quaternion, orthogonal pairs\n", dirs.size());
    // classify coordinate quaternions by how many of i,j,k are upper
    std::map<std::tuple<int,int,int>, Tab> byclass; // (i<8, j<8, k<8) pattern
    std::map<std::tuple<int,int,int>, int> nq;
    for (int i = 1; i <= 15; i++) for (int j = i + 1; j <= 15; j++) {
      int k = i ^ j; if (k < j) continue;  // each quaternion once: i<j<k
      V ei = basis(i), ej = basis(j), ek = mul(ei, ej);
      auto key = std::make_tuple(i < 8, j < 8, k < 8);
      nq[key]++;
      Tab& tab = byclass[key];
      for (size_t p = 0; p < dirs.size(); p++) for (size_t q = 0; q < dirs.size(); q++) {
        if (p == q) continue;
        auto& u = dirs[p]; auto& v = dirs[q];
        if (u[0]*v[0] + u[1]*v[1] + u[2]*v[2]) continue;
        V x = add(add(sc(ei, u[0]), sc(ej, u[1])), sc(ek, u[2]));
        V y = add(add(sc(ei, v[0]), sc(ej, v[1])), sc(ek, v[2]));
        if (!quaternionic(x, y)) { std::printf("   non-quaternionic pair inside H(%d,%d)?!\n", i, j); continue; }
        if (!art_pair(x, y)) { std::printf("   non-art pair inside H(%d,%d)?!\n", i, j); continue; }
        int N = kerdim(x, y, +1), A = kerdim(x, y, -1);
        tab.add(features(x, y), N, A);
      }
    }
    // ---------- Experiment C: full stratification inside one mixed quaternion ----------
    {
      int i = 1, j = 10; int k = i ^ j;   // H(1,10), k = 11; e_1 in O, e_10, e_11 in Ol
      V ei = basis(i), ej = basis(j), ek = mul(ei, ej);
      std::printf("\nExperiment C: H(%d,%d), e_%d e_%d = %+lld e_%d. Frame (e_%d, e_%d, e_%de_%d).\n",
                  i, j, i, j, ek.c[k], k, i, j, i, j);
      std::map<std::pair<int,int>, vector<std::pair<array<int,3>, array<int,3>>>> strata;
      const int R3 = 3;
      vector<array<int,3>> d3;
      for (int a = -R3; a <= R3; a++) for (int b = -R3; b <= R3; b++) for (int c = -R3; c <= R3; c++)
        if (a || b || c) {
          int g = std::gcd(std::gcd(std::abs(a), std::abs(b)), std::abs(c));
          if (g != 1) continue;
          int first = a ? a : (b ? b : c);
          if (first < 0) continue;
          d3.push_back({a, b, c});
        }
      for (size_t p = 0; p < d3.size(); p++) for (size_t q = p + 1; q < d3.size(); q++) {
        auto& u = d3[p]; auto& v = d3[q];
        if (u[0]*v[0] + u[1]*v[1] + u[2]*v[2]) continue;
        V x = add(add(sc(ei, u[0]), sc(ej, u[1])), sc(ek, u[2]));
        V y = add(add(sc(ei, v[0]), sc(ej, v[1])), sc(ek, v[2]));
        int N = kerdim(x, y, +1), A = kerdim(x, y, -1);
        int N2 = kerdim(y, x, +1), A2 = kerdim(y, x, -1);
        if (N != N2 || A != A2) std::printf("   asymmetric: (%d,%d,%d),(%d,%d,%d) -> (%d,%d) vs (%d,%d)\n",
                                            u[0],u[1],u[2],v[0],v[1],v[2],N,A,N2,A2);
        strata[{N, A}].push_back({u, v});
      }
      for (auto& kv : strata) {
        std::printf("   (N,A)=(%d,%d): %zu unordered pairs\n", kv.first.first, kv.first.second, kv.second.size());
        // print the non-generic strata in full, the generic one only in count
        if (kv.first == std::make_pair(4, 4)) continue;
        for (auto& pr : kv.second)
          std::printf("      x=(%d,%d,%d) y=(%d,%d,%d)\n", pr.first[0], pr.first[1], pr.first[2],
                      pr.second[0], pr.second[1], pr.second[2]);
      }
    }
    for (auto& kv : byclass) {
      char title[128];
      std::snprintf(title, sizeof title, "B: quaternions with (i<8,j<8,k<8)=(%d,%d,%d), count %d",
                    std::get<0>(kv.first), std::get<1>(kv.first), std::get<2>(kv.first), nq[kv.first]);
      kv.second.print(title);
    }
  }
  // ---------- Experiment D: generic quaternionic pairs by exact nullspace ----------
  // x random imaginary integer vector; L(x) = { y imaginary : xy+yx=0, x(xy)=x^2 y, (yx)x = y x^2 }
  // computed by fraction-free elimination over Z (values stay small); y = small random
  // combination of the kernel basis; keep pairs that are quaternionic with art.
  {
    typedef __int128 I;
    auto kernel_Z = [](vector<vector<long long>> M) {
      int n = (int)M.size(), m = (int)M[0].size();
      vector<vector<I>> A(n, vector<I>(m));
      for (int i = 0; i < n; i++) for (int j = 0; j < m; j++) A[i][j] = M[i][j];
      vector<int> pivcol; int r = 0;
      for (int col = 0; col < m && r < n; col++) {
        int piv = -1; for (int i = r; i < n; i++) if (A[i][col] != 0) { piv = i; break; }
        if (piv < 0) continue;
        std::swap(A[r], A[piv]);
        for (int i = 0; i < n; i++) if (i != r && A[i][col] != 0) {
          I f = A[i][col], g = A[r][col];
          for (int j = 0; j < m; j++) A[i][j] = A[i][j] * g - A[r][j] * f;
          // reduce row by gcd
          I gg = 0; for (int j = 0; j < m; j++) { I v = A[i][j] < 0 ? -A[i][j] : A[i][j]; gg = gg ? std::gcd((long long)gg, (long long)v) : v; }
          if (gg > 1) for (int j = 0; j < m; j++) A[i][j] /= gg;
        }
        pivcol.push_back(col); r++;
      }
      // free columns -> kernel vectors (rational, scaled to integers)
      vector<int> isPiv(m, -1); for (int i = 0; i < r; i++) isPiv[pivcol[i]] = i;
      vector<vector<long long>> K;
      for (int fcol = 0; fcol < m; fcol++) if (isPiv[fcol] < 0) {
        // y_fcol = L (lcm of pivots), y_pivcol[i] = -A[i][fcol] * L / A[i][pivcol[i]]
        I L = 1; for (int i = 0; i < r; i++) { I p = A[i][pivcol[i]]; if (p < 0) p = -p; L = L / std::gcd((long long)L, (long long)p) * p; }
        vector<long long> v(m, 0); v[fcol] = (long long)L;
        for (int i = 0; i < r; i++) v[pivcol[i]] = (long long)(-A[i][fcol] * L / A[i][pivcol[i]]);
        long long gg = 0; for (auto t : v) gg = std::gcd(gg, std::abs(t));
        if (gg > 1) for (auto& t : v) t /= gg;
        K.push_back(v);
      }
      return K;
    };
    unsigned long long seed = 20261003ULL;
    auto rnd = [&]() { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; return seed; };
    Tab tab; int tried = 0, kept = 0;
    std::map<std::pair<int,int>, std::pair<V,V>> wit;
    for (int trial = 0; trial < 4000; trial++) {
      V x; int w = 1 + rnd() % 8;
      for (int t = 0; t < w; t++) { int i = 1 + rnd() % 15; x.c[i] += (rnd() & 1) ? 1 : -1; }
      if (is0(x)) continue;
      // constraints on y (16 unknowns)
      vector<vector<long long>> M;
      { vector<long long> row(D, 0); row[0] = 1; M.push_back(row); }
      V x2 = mul(x, x);
      for (int k = 0; k < D; k++) {
        V e = basis(k);
        V c1 = add(mul(x, e), mul(e, x));
        V c2 = sub(mul(x, mul(x, e)), mul(x2, e));
        V c3 = sub(mul(mul(e, x), x), mul(e, x2));
        // store as columns: build later
        static vector<vector<long long>> cols; cols.assign(3 * D, vector<long long>(D, 0));
        for (int i = 0; i < D; i++) { cols[i][k] = c1.c[i]; cols[D + i][k] = c2.c[i]; cols[2 * D + i][k] = c3.c[i]; }
        if (k == D - 1) for (auto& r : cols) M.push_back(r);
      }
      auto K = kernel_Z(M);
      if (K.empty()) continue;
      for (int s = 0; s < 6; s++) {
        V y;
        for (auto& kv : K) { long long r = (long long)(rnd() % 5) - 2; for (int i = 0; i < D; i++) y.c[i] += r * kv[i]; }
        if (is0(y)) continue;
        long long g = 0; for (int i = 0; i < D; i++) g = std::gcd(g, std::abs(y.c[i]));
        if (g > 1) for (int i = 0; i < D; i++) y.c[i] /= g;
        tried++;
        if (!quaternionic(x, y) || !art_pair(x, y)) continue;
        kept++;
        int N = kerdim(x, y, +1), A = kerdim(x, y, -1);
        tab.add(features(x, y), N, A);
        if (!wit.count({N, A})) wit[{N, A}] = {x, y};
      }
    }
    std::printf("\nExperiment D: generic pairs, tried=%d quaternionic-with-art=%d\n", tried, kept);
    tab.print("D: (N,A) on generic quaternionic pairs");
    for (auto& kv : wit) {
      std::printf("   witness (%d,%d): x=[", kv.first.first, kv.first.second);
      for (int i = 0; i < D; i++) if (kv.second.first.c[i]) std::printf(" %+lld e%d", kv.second.first.c[i], i);
      std::printf(" ]  y=[");
      for (int i = 0; i < D; i++) if (kv.second.second.c[i]) std::printf(" %+lld e%d", kv.second.second.c[i], i);
      std::printf(" ]\n");
    }
  }
  return 0;
}
