#include <iostream>
#include <complex>
#include <memory.h>
#include <assert.h>
#include <random>
using namespace std;
typedef long long ll;
// FFT
const double pi = acos(-1);
const int mxi = 5;
constexpr int to2exp(int x){
    int cnt1 = 0;
    int cnti = 0;
    while(x){
        ++cnti;
        cnt1 += (x&1);
        x >>= 1;
    }
    if(cnt1==1) return cnti-1;
    return cnti;
}
constexpr int pow(int a, int p){    // 用于验证
    int res = 1;
    while(p){
        if(p&1){
            res *= a;
        }
        a *= a;
        p >>= 1;
    }
    return res;
}
constexpr int N = pow(2,to2exp(mxi))<<1;
ll ll_pow_mod(ll a, ll p, ll mod){    // 用于验证较少位数时的准确性
    ll res = 1;
    while(p){
        if(p&1){
            res *= a;
            res %= mod;
        }
        a *= a;
        a %= mod;
        p >>= 1;
    }
    return res;
}
// 迭代版傅里叶变换的技巧
void init_pos(complex<double > *a, int n){    // 逆向加法
    for(int i=0, j=0;i!=n;i++){
        if(i>j) swap(a[i],a[j]);
        for(int l=n>>1;(j^=l)<l;l>>=1);
    }
}
void FFT(int I, complex<double > *a, int n){    // 傅里叶变换 or 插值
    for(int i=2, mid=1;i<=n;i<<=1, mid<<=1){
        complex<double > wn = {cos(2.0*pi/i),sin(I*2.0*pi/i)};
        for(int j=0;j<n;j+=i){
            complex<double > w = {1,0};
            for(int k=j;k<j+mid;k++,w=w*wn){
                complex<double > l = a[k], r = w*a[k+mid];
                a[k] = l + r;
                a[k+mid] = l - r;
            }
        }
    }
    if(I==1)
        return;
    for(int i=0;i<n;i++){
        a[i] /= n;
    }
}
complex<double > t[N<<1];
class bigNum{
public:
    // static complex<double > t[N<<1];    // undefined reference to `bigNum::t'

    complex<double > a[N<<1];

    bigNum(const complex<double > *b){
        memcpy(a,b,sizeof(a));
    }

    bigNum(int c){
        assert(0<=c&&c<=9);
        for(int i=0;i<N;++i) a[i].real(c);
    }

    bigNum(const bigNum& oth){
        memcpy(a,oth.a,sizeof(a));
    }

    bigNum& operator =(const bigNum& oth){
        if(this==&oth) return *this;
        memcpy(a,oth.a,sizeof(a));
        return *this;
    }

    void operator *=(bigNum& oth){
        // 虚数部分误差累计，踩坑
        normalize();
        oth.normalize();
        memcpy(t,oth.a,sizeof(t));

        init_pos(a,N<<1);
        FFT(1,a,N<<1);

        init_pos(t,N<<1);
        FFT(1,t,N<<1);

        for(int i=0;i<(N<<1);++i) a[i] *= t[i];

        init_pos(a,N<<1);
        FFT(-1,a,N<<1);

        normalize();
    }

    bool operator >(const bigNum& oth){
        for(int i=(N<<1)-1;i>=0;--i){
            if((ll)round(a[i].real())==(ll)round(oth.a[i].real())) continue;
            else return (ll)round(a[i].real())>(ll)round(oth.a[i].real());
        }
        return false;
    }

    void operator -=(bigNum& oth){
        assert(!(oth>(*this)));
        for(int i=0;i<(N<<1)-1;++i){
            if((ll)round(a[i].real())<(ll)round(oth.a[i].real())){
                a[i] += 10;
                a[i] -= oth.a[i];
                a[i+1] -= 1;
            }else{
                a[i].real((ll)round(a[i].real())-(ll)round(oth.a[i].real()));
            }
        }
    }

    void operator +=(const bigNum& oth){
        for(int i=0;i<(N<<1)-1;++i){
            a[i] += oth.a[i];
            if((ll)round(a[i].real())>9){
                a[i+1] += (ll)round(a[i].real())/10;
                a[i].real((ll)round(a[i].real())%10);
            }
        }
        assert((ll)round(a[(N<<1)-1].real())<=9);
    }

    void div2(){
        for(int i=(N<<1)-1;i>0;--i){
            if((ll)round(a[i].real())&1){
                a[i-1] += 10;
                a[i] -= 1;
            }
            a[i] /= 2;
        }
        if((ll)round(a[0].real())&1) a[0] -= 1;
        a[0] /= 2;
    }

    void add1(){
        a[0] += 1;
        int i = 0;
        while(i<(N<<1)-1&&(ll)round(a[i].real())==10){
            a[i+1] += 1;
            a[i] = 0;
            ++i;
        }
    }

    void sub1(){
        a[0] -= 1;
        int i = 0;
        while(i<(N<<1)-1&&(ll)round(a[i].real())==-1){
            a[i+1] -= 1;
            a[i] += 10;
            ++i;
        }
    }

    void normalize(){
        for(int i=0;i<(N<<1)-1;++i){
            if((ll)round(a[i].real())>9){
                a[i+1] += (ll)round(a[i].real())/10;
                a[i].real((ll)round(a[i].real())%10);
            }
            a[i].real((ll)round(a[i].real()));
            a[i].imag(0);
        }
        a[(N<<1)-1].real((ll)round(a[(N<<1)-1].real()));
        a[(N<<1)-1].imag(0);
        assert((ll)round(a[(N<<1)-1].real())<=9);
    }

    bool is0(){
        for(int i=(N<<1)-1;i>=0;--i){
            if((ll)round(a[i].real())>0) return false;
        }
        return true;
    }

    bool is1(){
        for(int i=(N<<1)-1;i>0;--i){
            if((ll)round(a[i].real())>0) return false;
        }
        return (ll)round(a[0].real())==1;
    }

    bool isplural(){
        return (ll)round(a[0].real())%2==0;
    }

    void print(){
        bool non0 = false;
        for(int i=(N<<1)-1;i>0;--i){
            if(!non0&&(ll)round(a[i].real())==0) continue;
            non0 = true;
            cout << (ll)round(a[i].real());
        }
        cout << (ll)round(a[0].real());
    }
};
// 二分+FFT实现n*logn*logV大数除法
bigNum DIV(const bigNum &a, bigNum &b){
    bigNum lo(0), hi(9);    // [lo,hi)
    bigNum mid(0);
    bigNum t(0);
    while(mid=lo,mid+=hi,mid.div2(),t=lo,t.add1(),hi>t){
        t = mid;
        t *= b;
        if(t>a){    // mid*b>a
            hi = mid;
        }else{    // mid*b<=a
            lo = mid;
        }
    }
    return lo;
}
// 大数求余运算
void MOD(bigNum &a, bigNum &mod){
    bigNum d = DIV(a, mod);
    d *= mod;
    a -= d;
}
// 利用FFT做大数的快速幂运算
bigNum pow_mod(bigNum a, bigNum n, bigNum &mod){
    bigNum res(0), t(0);
    res.add1();
    while(!n.is0()){
        if(!n.isplural()){
            res *= a;
            MOD(res, mod);
        }
        t = a;
        a *= t;
        MOD(a, mod);
        n.div2();
    }
    return res;
}
bigNum generate(int N, bigNum *limit){
    assert(N<=mxi);
    bigNum p(0);
    std::mt19937 rng;
    rng.seed(std::random_device()());
    std::uniform_int_distribution<std::mt19937::result_type> u(0,9);
    for(int i=0;i<N;++i){
        p.a[i] = u(rng);
    }
    if(limit&&p>(*limit)) return generate(N, limit);
    return p;
}
// 留坑：卡迈克尔(Carmichael)数
bool Miller_Rabin(bigNum &n, int t, int N){
    if(n.is0()||n.is1()) return false;
    if(n.isplural()){
        n.div2();
        return n.is1();
    }
    bigNum d = n;
    d.sub1();
    int s = 0;
    while(!d.is0()&&d.isplural()){
        ++s;
        d.div2();
    }
    bigNum bN2(0);
    bN2.a[0] = 2;
    while(t--){
        bigNum a = generate(N,&n);
        bigNum x = pow_mod(a,d,n);
        bigNum tx = x;
        if(x.is1()||(tx.add1(),MOD(tx,n),tx.is0())) continue;
        for(int r=0;r<s;++r){
            tx = x;
            x = pow_mod(x, bN2, n);
            if(x.is1()&&!tx.is1()&&!(tx.add1(),MOD(tx,n),tx.is0())) return false;
        }
        if(!x.is1()) return false;
    }
    return true;
}
bigNum generate_prime(int N, int k, int t){
    for(int i=0;i<k;++i){
        bigNum n = generate(N,nullptr);
        if(Miller_Rabin(n,t,N)) return n;
    }
    return bigNum(0);
}
bigNum PrimitiveRoot(int N, bigNum &p){
    bigNum bN2(0);
    bN2.a[0] = 2;
    bigNum q(p);
    q *= bN2;
    q.add1();
    bigNum g(0);
    bigNum pg2(0), pgq(0);
    do{
        g = generate(N, &p);
        pg2 = pow_mod(g,bN2,p);
        pgq = pow_mod(g,q,p);
    }while(pg2.is1()||pgq.is1());
    return g;
}
int main(){
    bigNum res = generate_prime(mxi,100,100);
    res.print();
    cout << endl;
    bigNum resg = PrimitiveRoot(mxi,res);
    resg.print();
    cout << endl;
    return 0;
}