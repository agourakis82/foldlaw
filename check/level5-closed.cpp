// Level 5, quaternionic pairs of alternative elements, standard Q = H(e1,e2).
// Moreno form: x = (alpha, s + t alpha), alpha = (X0, X1) in Q x Q = O', X0 pure; same for y with primes.
// Checks, exactly:
//   (1) the top block of W on F x F (F = Q^perp x Q^perp = span{e4..e7, e12..e15}) has the shape
//       W(f,g) = (P f + B g, -B f + P g), each 4x4 block of P and B acting on Q^perp = H by LEFT multiplication
//       by a quaternion: P = [[0,p],[-p,0]] (slot 1 -> slot 0 by p), B = [[a,b],[-conj b, c]];
//   (2) p = (1 + t t')([X0,Y1] - [X1,Y0]);
//   (3) a = (t'-t)(K + 2J), c = (t'-t)(K - 2J), b = (t'-t)([X0,Y1] - [X1,Y0] + 2 X0 conj(Y1) - 2 conj(X1) Y0),
//       K = [X0,Y0] + [X1,Y1],  J = Re(Y1) Im(X1) - Re(X1) Im(Y1);
//   (4) N_E = 12 iff t = t' or alpha, alpha' parallel; then B = 0 and beta_5 = 16 [p = 0];
//   (5) beta_5 = 4 (2 - rk_H (P + B P^{-1} B)) if p != 0, else 2 dim ker B; and dim Ass' in {4,8,12,20,28}.
#include <array>
#include <cstdio>
#include <cstdlib>
#include <map>
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
// quaternions (1,i,j,k) = (e0,e1,e2,e3) pattern
static int qs[4][4], qi[4][4];
// e1 e2 = -e3 in the product mul; the table is checked against mul at start-up
static void initq() { int t[4][4][2] = {{{0,1},{1,1},{2,1},{3,1}},{{1,1},{0,-1},{3,-1},{2,1}},{{2,1},{3,1},{0,-1},{1,-1}},{{3,1},{2,-1},{1,1},{0,-1}}};
  for (int a = 0; a < 4; a++) for (int b = 0; b < 4; b++) { qi[a][b] = t[a][b][0]; qs[a][b] = t[a][b][1]; } }
struct Q { long long c[4]{}; };
static Q qmul(Q a, Q b) { Q r; for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) r.c[qi[i][j]] += a.c[i]*b.c[j]*qs[i][j]; return r; }
static Q qadd(Q a, Q b) { for (int i = 0; i < 4; i++) a.c[i] += b.c[i]; return a; }
static Q qsub(Q a, Q b) { for (int i = 0; i < 4; i++) a.c[i] -= b.c[i]; return a; }
static Q qscl(Q a, long long k) { for (int i = 0; i < 4; i++) a.c[i] *= k; return a; }
static Q qconj(Q a) { a.c[1] = -a.c[1]; a.c[2] = -a.c[2]; a.c[3] = -a.c[3]; return a; }
static Q qcomm(Q a, Q b) { return qsub(qmul(a, b), qmul(b, a)); }
static bool qeq(Q a, Q b) { for (int i = 0; i < 4; i++) if (a.c[i] != b.c[i]) return false; return true; }
static bool q0(Q a) { return qeq(a, Q{}); }
static Q qq(const V& v, int o) { Q r; for (int i = 0; i < 4; i++) r.c[i] = v.c[o+i]; return r; }
static Q qim(Q a) { a.c[0] = 0; return a; }
// quaternion multiplication table check against the algebra: e1 e2 = e3 in CD with our mul? verify once
static void checkTable() {
  for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) {
    V a = unit(i), b = unit(j), p = mul(a, b);
    Q qa, qb; qa.c[i] = 1; qb.c[j] = 1; Q qp = qmul(qa, qb);
    for (int k = 0; k < 4; k++) if (p.c[k] != qp.c[k]) { std::printf("quaternion table mismatch at %d %d\n", i, j); std::exit(4); }
  }
}
struct Rng { unsigned long long s; long long operator()(int R) { s ^= s<<13; s ^= s>>7; s ^= s<<17; return (long long)(s % (2*R+1)) - R; } };
static const int Fb[8] = {4,5,6,7,12,13,14,15};
struct Blocks { Q p, a, b, c, b10; bool shape; };
static Blocks readBlocks(const V& x, const V& y) {
  long long A[8][8] = {}, Bm[8][8] = {};
  Blocks r; r.shape = true;
  for (int j = 0; j < 8; j++) {
    V w0 = W(x, y, unit(Fb[j])), w1 = W(x, y, unit(16+Fb[j]));
    for (int i = 0; i < D; i++) { bool inF = (i & 4); if (!inF && (w0.c[i] || w1.c[i])) r.shape = false; }
    for (int i = 0; i < 8; i++) {
      A[i][j] = w0.c[Fb[i]]; Bm[i][j] = w1.c[Fb[i]];
      if (w0.c[16+Fb[i]] != -w1.c[Fb[i]] || w1.c[16+Fb[i]] != w0.c[Fb[i]]) r.shape = false;
    }
  }
  for (int i = 0; i < 4; i++) { r.p.c[i] = A[i][4]; r.a.c[i] = Bm[i][0]; r.b.c[i] = Bm[i][4]; r.c.c[i] = Bm[4+i][4]; r.b10.c[i] = Bm[4+i][0]; }
  auto leftBlockOK = [&](long long M[8][8], int br, int bc, Q q) {
    for (int col = 0; col < 4; col++) { Q e; e.c[col] = 1; Q v = qmul(q, e); for (int row = 0; row < 4; row++) if (M[4*br+row][4*bc+col] != v.c[row]) return false; }
    return true;
  };
  if (!leftBlockOK(A, 0, 1, r.p) || !leftBlockOK(A, 1, 0, qscl(r.p, -1)) || !leftBlockOK(A, 0, 0, Q{}) || !leftBlockOK(A, 1, 1, Q{})) r.shape = false;
  if (!leftBlockOK(Bm, 0, 0, r.a) || !leftBlockOK(Bm, 0, 1, r.b) || !leftBlockOK(Bm, 1, 1, r.c) || !leftBlockOK(Bm, 1, 0, r.b10)) r.shape = false;
  return r;
}
// the bilinear formulas, in the four Q-coordinates X0..X3 of x (coords 0,8,16,24) and Y0..Y3 of y
struct Formulas { Q p, a, b, c; };
static Formulas formulas(const V& x, const V& y) {
  Q X[4] = {qq(x,0), qq(x,8), qq(x,16), qq(x,24)}, Y[4] = {qq(y,0), qq(y,8), qq(y,16), qq(y,24)};
  Formulas f;
  f.p = qsub(qadd(qcomm(X[0],Y[1]), qcomm(X[2],Y[3])), qadd(qcomm(X[1],Y[0]), qcomm(X[3],Y[2])));
  Q K = qsub(qadd(qcomm(X[0],Y[2]), qcomm(X[1],Y[3])), qadd(qcomm(X[2],Y[0]), qcomm(X[3],Y[1])));
  Q J = qsub(qsub(qmul(X[1], qconj(Y[3])), qmul(qconj(X[1]), Y[3])), qsub(qmul(X[3], qconj(Y[1])), qmul(qconj(X[3]), Y[1])));
  f.a = qadd(K, J); f.c = qsub(K, J);
  Q b = qadd(qsub(qcomm(X[0],Y[3]), qcomm(X[1],Y[2])), qsub(qcomm(X[3],Y[0]), qcomm(X[2],Y[1])));
  b = qadd(b, qscl(qmul(X[0], qconj(Y[3])), 2));
  b = qsub(b, qmul(X[2], qconj(Y[1])));
  b = qsub(b, qmul(qconj(X[1]), Y[2]));
  b = qadd(b, qscl(qmul(qconj(X[3]), Y[0]), 2));
  b = qadd(b, qmul(qconj(X[1]), qconj(Y[2])));
  b = qadd(b, qmul(qconj(X[2]), qconj(Y[1])));
  f.b = b;
  return f;
}
int main(int argc, char** argv) {
  initq(); checkTable();
  // PROOF STEP: the block entries are bilinear in (x,y); so are the formulas. Check all 16 x 16 basis pairs of E.
  {
    int okp = 0, oka = 0, okb = 0, okc = 0, okb10 = 0, okshape = 0;
    vector<int> Eidx0; for (int i = 0; i < D; i++) if (!(i & 4)) Eidx0.push_back(i);
    for (int i : Eidx0) for (int j : Eidx0) {
      V x = unit(i), y = unit(j);
      Blocks bl = readBlocks(x, y); Formulas f = formulas(x, y);
      // shape with the diagonal of P removed: only P's diagonal may fail, and only on i == j (handled by orthogonality)
      okp += qeq(bl.p, f.p); oka += qeq(bl.a, f.a); okb += qeq(bl.b, f.b); okc += qeq(bl.c, f.c); okb10 += qeq(bl.b10, qscl(qconj(bl.b), -1));
      okshape += bl.shape || (i == j);
      if (i && j && (!qeq(bl.p, f.p) || !qeq(bl.a, f.a) || !qeq(bl.b, f.b) || !qeq(bl.c, f.c) || !(bl.shape || i == j)))
        std::printf("  imaginary basis failure e%d e%d: p %d a %d b %d c %d shape %d\n", i, j, qeq(bl.p,f.p), qeq(bl.a,f.a), qeq(bl.b,f.b), qeq(bl.c,f.c), bl.shape);
    }
    std::printf("basis pairs of E (256): p %d a %d b %d c %d B10=-conj(b) %d shape-or-diagonal %d\n", okp, oka, okb, okc, okb10, okshape);
  }
  int want = argc > 1 ? std::atoi(argv[1]) : 4000;
  int R = argc > 2 ? std::atoi(argv[2]) : 3;
  Rng g{ 20261003ULL };
  vector<int> Eidx, Fidx; for (int i = 0; i < D; i++) (i & 4 ? Fidx : Eidx).push_back(i);
  int got = 0, shapeOK = 0, pOK = 0, aOK = 0, bOK = 0, cOK = 0, b10OK = 0, NEOK = 0, B0OK = 0, betaOK = 0, NE12 = 0, totalOK = 0;
  std::map<int,int> histN; std::map<std::pair<int,int>,int> histNEb;
  for (long trial = 0; trial < 200L*want && got < want; trial++) {
    // mix: general, t = t', parallel alphas
    int mode = trial % 3;
    Q X0{}, X1{}, Y0{}, Y1{};
    for (int i = 1; i < 4; i++) { X0.c[i] = g(R); Y0.c[i] = g(R); }
    long long s = g(R), t = g(R), s2 = g(R), t2 = g(R), sig = g(R), tau = g(R), sig2 = g(R), tau2 = g(R);
    if (trial % 2) { for (int i = 1; i < 4; i++) { if (g(1) == 0) X0.c[i] = 0; if (g(1) == 0) Y0.c[i] = 0; } if (g(1)==0) sig = 0; if (g(1)==0) tau = 0; if (g(1)==0) sig2 = 0; if (g(1)==0) tau2 = 0; }
    X1 = qscl(X0, tau); X1.c[0] += sig; Y1 = qscl(Y0, tau2); Y1.c[0] += sig2;   // Moreno: alpha = (X0, sigma + tau X0) is alternative in A_4
    if (mode == 1) t2 = t;
    if (mode == 2) { long long lam = g(2); if (!lam) continue; Y0 = qscl(X0, lam); sig2 = lam*sig; tau2 = tau; Y1 = qscl(Y0, tau2); Y1.c[0] += sig2; }
    V x, y;
    for (int i = 0; i < 4; i++) { x.c[i] = X0.c[i]; x.c[8+i] = X1.c[i]; y.c[i] = Y0.c[i]; y.c[8+i] = Y1.c[i]; }
    for (int i = 0; i < 16; i++) { x.c[16+i] = t*x.c[i]; y.c[16+i] = t2*y.c[i]; }
    x.c[16] += s; y.c[16] += s2;
    if (is0(x) || is0(y) || dot(x, y)) continue;
    got++;
    if (got <= 300) { // alternativity check on a prefix
      bool art = true;
      for (int k = 0; k < D && art; k++) { V e = unit(k); if (!is0(sub(mul(mul(x,x),e), mul(x,mul(x,e)))) || !is0(sub(mul(mul(y,y),e), mul(y,mul(y,e))))) art = false; }
      if (!art) { std::printf("NOT ALTERNATIVE\n"); return 5; }
    }
    // blocks
    long long A[8][8] = {}, Bm[8][8] = {};
    bool shape = true;
    for (int j = 0; j < 8; j++) {
      V w0 = W(x, y, unit(Fb[j])), w1 = W(x, y, unit(16+Fb[j]));
      for (int i = 0; i < D; i++) { bool inF = (i & 4); if (!inF && (w0.c[i] || w1.c[i])) shape = false; }
      for (int i = 0; i < 8; i++) {
        A[i][j] = w0.c[Fb[i]]; Bm[i][j] = w1.c[Fb[i]];
        if (w0.c[16+Fb[i]] != -w1.c[Fb[i]] || w1.c[16+Fb[i]] != w0.c[Fb[i]]) shape = false;
      }
    }
    // read quaternions: column 4 of A top = p (slot1 -> slot0), column 0 of A bottom = -p
    Q p; for (int i = 0; i < 4; i++) p.c[i] = A[i][4];
    for (int i = 0; i < 4; i++) { if (A[i][0] || A[4+i][4]) shape = false; if (A[4+i][0] != -p.c[i]) shape = false; }
    // A must be right multiplication by these quaternions: check the full 4x4 blocks
    auto rightBlockOK = [&](long long M[8][8], int br, int bc, Q q) {
      for (int col = 0; col < 4; col++) { Q e; e.c[col] = 1; Q r = qmul(q, e); for (int row = 0; row < 4; row++) if (M[4*br+row][4*bc+col] != r.c[row]) return false; }
      return true;
    };
    Q a, b, c, b10; for (int i = 0; i < 4; i++) { a.c[i] = Bm[i][0]; b.c[i] = Bm[i][4]; c.c[i] = Bm[4+i][4]; b10.c[i] = Bm[4+i][0]; }
    if (!rightBlockOK(A, 0, 1, p) || !rightBlockOK(A, 1, 0, qscl(p, -1))) shape = false;
    if (!rightBlockOK(Bm, 0, 0, a) || !rightBlockOK(Bm, 0, 1, b) || !rightBlockOK(Bm, 1, 1, c) || !rightBlockOK(Bm, 1, 0, b10)) shape = false;
    shapeOK += shape;
    // formulas
    Q pf = qscl(qsub(qcomm(X0, Y1), qcomm(X1, Y0)), 1 + t*t2);
    pOK += qeq(p, pf);
    Q K = qadd(qcomm(X0, Y0), qcomm(X1, Y1));
    Q J = qsub(qscl(qim(X1), Y1.c[0]), qscl(qim(Y1), X1.c[0]));
    Q af = qscl(qadd(K, qscl(J, 2)), t2 - t);
    Q cf = qscl(qsub(K, qscl(J, 2)), t2 - t);
    Q bf = qscl(qadd(qsub(qcomm(X0, Y1), qcomm(X1, Y0)), qsub(qscl(qmul(X0, qconj(Y1)), 2), qscl(qmul(qconj(X1), Y0), 2))), t2 - t);
    aOK += qeq(a, af); bOK += qeq(b, bf); cOK += qeq(c, cf); b10OK += qeq(b10, qscl(qconj(b), -1));
    // reduced (Moreno) forms: p = (1+tt')(tau'-tau)[X0,Y0]; a,c = (t'-t)((1+tau tau')[X0,Y0] +- 2(sigma' tau X0 - sigma tau' Y0));
    // b = (t'-t)(2(tau'-tau)<X0,Y0> + 2 sigma' X0 - 2 sigma Y0)
    { Q C0 = qcomm(X0, Y0); long long ip = -(X0.c[1]*Y0.c[1] + X0.c[2]*Y0.c[2] + X0.c[3]*Y0.c[3]); ip = -ip; // <X0,Y0>
      Q pr = qscl(C0, (1 + t*t2)*(tau2 - tau));
      Q Jr = qsub(qscl(X0, sig2*tau), qscl(Y0, sig*tau2));
      Q ar = qscl(qadd(qscl(C0, 1 + tau*tau2), qscl(Jr, 2)), t2 - t);
      Q cr = qscl(qsub(qscl(C0, 1 + tau*tau2), qscl(Jr, 2)), t2 - t);
      Q br{}; br.c[0] = 2*(tau2 - tau)*ip; br = qadd(br, qsub(qscl(X0, 2*sig2), qscl(Y0, 2*sig))); br = qscl(br, t2 - t);
      static int rp = 0, ra = 0, rb = 0, rc = 0; rp += qeq(p, pr); ra += qeq(a, ar); rb += qeq(b, br); rc += qeq(c, cr);
      if (got == want) std::printf("reduced Moreno formulas: p %d a %d b %d c %d of %d\n", rp, ra, rb, rc, want);
    }
    // N_E and beta
    auto nullityOn = [&](const vector<int>& idx) {
      int k = (int)idx.size(); vector<vector<long long>> M(D, vector<long long>(k));
      for (int j = 0; j < k; j++) { V w = W(x, y, unit(idx[j])); for (int i = 0; i < D; i++) M[i][j] = w.c[i]; }
      return k - rank2(M);
    };
    int NE = nullityOn(Eidx), beta = nullityOn(Fidx), N = nullityOn(vector<int>{});
    { vector<int> all; for (int i = 0; i < D; i++) all.push_back(i); N = nullityOn(all); }
    // parallel test: alpha' = lambda alpha  <=>  X0 x Y0 = 0 etc. Use commutator in O' = Q x Q: [alpha, alpha'] = 0
    V al, al2; for (int i = 0; i < 16; i++) { al.c[i] = x.c[i]; al2.c[i] = y.c[i]; }
    V c1, c2; mul_rec(al.c.data(), al2.c.data(), c1.c.data(), 16); mul_rec(al2.c.data(), al.c.data(), c2.c.data(), 16);
    bool parallel = is0(sub(c1, c2));
    bool pred12 = (t == t2) || parallel;
    NEOK += ((NE == 12) == pred12) && (NE == 12 || NE == 4);
    if (pred12) { NE12++; bool B0 = q0(a) && q0(b) && q0(c) && q0(b10); B0OK += B0; betaOK += (beta == (q0(p) ? 16 : 0)); }
    histN[N]++; histNEb[{NE, beta}]++;
    totalOK += (N == NE + beta);
  }
  std::printf("pairs %d: shape %d, p-formula %d, a %d, b %d, c %d, B10=-conj(b) %d, N_E rule %d, additivity %d\n",
              got, shapeOK, pOK, aOK, bOK, cOK, b10OK, NEOK, totalOK);
  std::printf("N_E = 12 cases %d: B = 0 in %d, beta_5 = 16[p=0] in %d\n", NE12, B0OK, betaOK);
  std::printf("dim Ass':"); for (auto& kv : histN) std::printf(" %d->%d", kv.first, kv.second); std::printf("\n");
  std::printf("(N_E, beta_5):"); for (auto& kv : histNEb) std::printf(" (%d,%d)x%d", kv.first.first, kv.first.second, kv.second); std::printf("\n");
}
