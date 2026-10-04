// Peer-review check: which Schur complement gives beta_5?
// K = [[P,B],[-B,P]] on H^4 (real 16x16), P=[[0,p],[-p,0]], B=[[a,b],[-conj b,c]].
// Compare nullity(K) with nullity(|p|^2 P + B P B) [= P + B P^{-1} B up to scale]
// and nullity(|p|^2 I + B P B) [= P^{-1}(P + P^{-1} B P B) up to scale].
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <array>
#include <random>
using namespace std;
typedef array<long long,4> Q; // e0,e1,e2,e3 with e1 e2 = -e3 (note's convention)
static int T[4][4][2] = {{{0,1},{1,1},{2,1},{3,1}},{{1,1},{0,-1},{3,-1},{2,1}},{{2,1},{3,1},{0,-1},{1,-1}},{{3,1},{2,-1},{1,1},{0,-1}}};
Q qm(const Q&x,const Q&y){Q r{0,0,0,0};for(int i=0;i<4;i++)for(int j=0;j<4;j++)r[T[i][j][0]]+=T[i][j][1]*x[i]*y[j];return r;}
Q qa(const Q&x,const Q&y){return {x[0]+y[0],x[1]+y[1],x[2]+y[2],x[3]+y[3]};}
Q qs(const Q&x,long long k){return {k*x[0],k*x[1],k*x[2],k*x[3]};}
Q qc(const Q&x){return {x[0],-x[1],-x[2],-x[3]};}
Q qneg(const Q&x){return qs(x,-1);}
Q com(const Q&x,const Q&y){return qa(qm(x,y),qneg(qm(y,x)));}
long long nrm(const Q&x){return x[0]*x[0]+x[1]*x[1]+x[2]*x[2]+x[3]*x[3];}
typedef vector<vector<Q>> QM;
QM mul(const QM&A,const QM&B){int n=A.size();QM C(n,vector<Q>(n,Q{0,0,0,0}));for(int i=0;i<n;i++)for(int j=0;j<n;j++)for(int k=0;k<n;k++)C[i][j]=qa(C[i][j],qm(A[i][k],B[k][j]));return C;}
QM add(const QM&A,const QM&B){int n=A.size();QM C=A;for(int i=0;i<n;i++)for(int j=0;j<n;j++)C[i][j]=qa(A[i][j],B[i][j]);return C;}
QM scal(const QM&A,long long k){QM C=A;for(auto&r:C)for(auto&q:r)q=qs(q,k);return C;}
// real matrix of left multiplication by q
vector<vector<long long>> real(const QM&A){int n=A.size();vector<vector<long long>> R(4*n,vector<long long>(4*n,0));
 for(int i=0;i<n;i++)for(int j=0;j<n;j++)for(int c=0;c<4;c++){Q e{0,0,0,0};e[c]=1;Q v=qm(A[i][j],e);for(int r=0;r<4;r++)R[4*i+r][4*j+c]=v[r];}return R;}
int rankp(vector<vector<long long>> M,long long p){int n=M.size(),m=M[0].size(),r=0;for(auto&row:M)for(auto&v:row){v%=p;if(v<0)v+=p;}
 for(int c=0;c<m&&r<n;c++){int piv=-1;for(int i=r;i<n;i++)if(M[i][c]){piv=i;break;}if(piv<0)continue;swap(M[piv],M[r]);
  long long inv=1,b=M[r][c],e=p-2;while(e){if(e&1)inv=inv*b%p;b=b*b%p;e>>=1;}
  for(int j=0;j<m;j++)M[r][j]=M[r][j]*inv%p;
  for(int i=0;i<n;i++)if(i!=r&&M[i][c]){long long f=M[i][c];for(int j=0;j<m;j++){M[i][j]=(M[i][j]-f*M[r][j])%p;if(M[i][j]<0)M[i][j]+=p;}}r++;}return r;}
int nullity(const vector<vector<long long>>&M){int a=rankp(M,1000003),b=rankp(M,1048573);if(a!=b){printf("RANK MISMATCH\n");exit(2);}return (int)M.size()-a;}
int main(){
 Q z{0,0,0,0};
 auto run=[&](Q p,Q a,Q b,Q c,const char*tag){
  QM P={{z,p},{qneg(p),z}}, B={{a,b},{qneg(qc(b)),c}};
  QM K={{P[0][0],P[0][1],B[0][0],B[0][1]},{P[1][0],P[1][1],B[1][0],B[1][1]},
        {qneg(B[0][0]),qneg(B[0][1]),P[0][0],P[0][1]},{qneg(B[1][0]),qneg(B[1][1]),P[1][0],P[1][1]}};
  int nK=nullity(real(K));
  long long n2=nrm(p);
  QM BPB=mul(mul(B,P),B);
  QM I={{Q{1,0,0,0},z},{z,Q{1,0,0,0}}};
  int nRight=nullity(real(add(scal(P,n2),BPB)));   // |p|^2 P + BPB  ~ P + B P^{-1} B
  int nWrong=nullity(real(add(scal(I,n2),BPB)));   // |p|^2 I + BPB  ~ P + P^{-1} B P B
  bool commute = mul(P,B)==mul(B,P);
  if(tag||nK!=nRight||nK==nWrong) ; 
  if(tag) printf("%s: nullity K=%d, ker(P+BP^-1B)=%d, ker(P+P^-1BPB)=%d, PB=BP:%d\n",tag,nK,nRight,nWrong,commute);
  return array<int,3>{nK,nRight,nWrong};
 };
 // witness of Proposition 6: p=-4e1, a=c=4e1, b=8
 run(Q{0,-4,0,0},Q{0,4,0,0},Q{8,0,0,0},Q{0,4,0,0},"witness");
 // random Moreno pairs via reduced formulas, p != 0 only
 mt19937 g(7); uniform_int_distribution<int> d(-2,2);
 int tot=0,okR=0,okW=0,shown=0;
 for(int it=0;it<20000;it++){
  Q X0{0,d(g),d(g),d(g)},Y0{0,d(g),d(g),d(g)}; int s=d(g),t=d(g),si=d(g),ta=d(g),s2=d(g),t2=d(g),si2=d(g),ta2=d(g);
  Q C=com(X0,Y0); if(nrm(C)==0) continue;
  Q p=qs(C,(1+t*t2)*(ta2-ta)); if(nrm(p)==0) continue;
  long long ip=-(X0[1]*Y0[1]+X0[2]*Y0[2]+X0[3]*Y0[3]); // <X0,Y0> = -(Re X0Y0) ... inner product positive
  ip=-ip;
  Q b=qs(qa(Q{2*(ta2-ta)*ip,0,0,0},qa(qs(X0,2*si2),qs(Y0,-2*si))),t2-t);
  Q m=qa(qs(X0,si2*ta),qs(Y0,-si*ta2));
  Q a=qs(qa(qs(C,1+ta*ta2),qs(m,2)),t2-t), c=qs(qa(qs(C,1+ta*ta2),qs(m,-2)),t2-t);
  auto r=run(p,a,b,c,nullptr); tot++; okR+=(r[0]==r[1]); okW+=(r[0]==r[2]);
  if(r[0]!=r[2]&&shown<3){shown++;printf("example: K=%d right=%d wrong=%d\n",r[0],r[1],r[2]);}
 }
 printf("random p!=0 pairs %d: nullity(K)==ker(P+BP^-1B) in %d, ==ker(P+P^-1BPB) in %d\n",tot,okR,okW);
}
