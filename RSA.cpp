#include <iostream>
#include <complex>
#include <memory.h>
#include <assert.h>
#include <random>
#include <time.h>  
using namespace std;
typedef long long ll;
// FFT
const double pi = acos(-1);
const int mxi = 16;
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
class bigNum{
private:
    complex<double > t[N<<1];
public:
    // static complex<double > t[N<<1];    // undefined reference to `bigNum::t'

    complex<double > a[N<<1];

    bigNum(const complex<double > *b){
        memcpy(a,b,sizeof(a));
    }

    bigNum(const char num[]){
        if(num==NULL) bigNum(0);
        else{
            int l = strlen(num);
            for(int i=0;i<l;++i){
                a[i] = num[l-1-i]-'0';
            }
        }
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
bigNum gcd(bigNum a, bigNum b){
    if(b.is0()) return a;
    bigNum c = DIV(a, b);
    bigNum d = b;
    d *= c;
    a -= d;
    return gcd(b, a);
}
bigNum ext_gcd(bigNum a, bigNum b, int &ss, bigNum& s, int &st, bigNum& t){
    if(b.is0()){
        ss = 1;
        s = bigNum(0);
        s.add1();
        st = 1;
        t = bigNum(0);
        return a;
    }
    bigNum c = DIV(a, b);    // c=a/b
    bigNum d = b;
    d *= c;
    a -= d;    // a=a%b
    bigNum g = ext_gcd(b,a,ss,s,st,t);
    cout << "ext_gcd: ";
    cout << (ss==-1?"-":"");s.print();cout << " * ";b.print();cout << " + " << (st==-1?"-":"");t.print();cout << " * ";a.print();cout << " = ";g.print();cout << endl;
    int tss = ss;
    bigNum ts = s;
    ss = st;
    s = t;
    t *= c;
    if(tss==1&&st==1){
        if(t>ts){
            st = -1;
            t -= ts;
        }else{
            st = 1;
            ts -= t;
            t = ts;
        }
    }else if(tss==1&&st==-1){
        st = 1;
        t += ts;
    }else if(tss==-1&&st==1){
        st = -1;
        t += ts;
    }else if(tss==-1&&st==-1){
        if(ts>t){
            st = -1;
            ts -= t;
            t = ts;
        }else{
            st = 1;
            t -= ts;
        }
    }
    return g;
}
bigNum inv_mod(bigNum a, bigNum b){
    bigNum s(0), t(0);
    int ss, st;
    bigNum g = ext_gcd(a,b,ss,s,st,t);
    cout << "g: ";g.print();cout << endl;
    t *= b;
    t.add1();
    t = DIV(t, a);
    return t;
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
    bigNum d = n;
    if(n.isplural()){
        d.div2();
        return d.is1();
    }
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
    // clock_t start, finish;    
    // double  duration;
    // start = clock();
    for(int i=0;i<k;++i){
        bigNum n = generate(N,nullptr);
        if(Miller_Rabin(n,t,N)){
            // finish = clock();
            // duration = (double)(finish - start) / CLOCKS_PER_SEC;
            // cout << "used " << duration << " secs to generate a prime." << endl;
            return n;
        }
    }
    return bigNum(0);
}
#include <pthread.h>
// 开启threadnum个线程，每个线程都在循环求可行的bigNum，直到超过总的尝试次数，或有一个可行bigNum产生则退出线程
pthread_mutex_t cnt_mutex;
int calcnt;
int totcnt;
pthread_mutex_t res_mutex;
bool hasres;
bigNum res(0);
const int mxth = 5;    // 最大的支持线程数
pthread_t threads[mxth];    // 保存所有线程的句柄
void *generate_prime_thread(void *arg){
    int *t = (int*)arg;
    while(!hasres&&calcnt<totcnt){
        pthread_mutex_lock(&cnt_mutex);
        ++calcnt;
        pthread_mutex_unlock(&cnt_mutex);
        bigNum n = generate(t[0],nullptr);
        cout << "working in thread " << t[2] << ", trying ";n.print();cout << endl;
        if(Miller_Rabin(n,t[1],t[0])){
            pthread_mutex_lock(&res_mutex);
            hasres = true;
            res = n;
            pthread_mutex_unlock(&res_mutex);
        }
    }
}
void pthread_join_all(pthread_t threads[], int threadnum){
    for(int i=0;i<threadnum;i++){
        pthread_join(threads[i],NULL);
    }
}
bigNum generate_prime_multithreaded(int N, int k, int t, int threadnum){
    // clock_t start, finish;    
    // double  duration;
    // start = clock();
    calcnt = 0;
    totcnt = k;
    hasres = false;
    pthread_mutex_init(&cnt_mutex, NULL);
    pthread_mutex_init(&res_mutex, NULL);
    for(int i=0;i<threadnum;i++)
    {
        int arg[3] = {N,t,i};
        pthread_create(&threads[i], NULL, generate_prime_thread, (void*)&arg);
    }
    pthread_join_all(threads, threadnum);
    pthread_mutex_destroy(&cnt_mutex);
    pthread_mutex_destroy(&res_mutex);
    // finish = clock();
    // duration = (double)(finish - start) / CLOCKS_PER_SEC;
    // cout << "used " << duration << " secs to generate a prime." << endl;
    return res;
}

const int mxk = 100;
const int mxt = 100;
int main(){
    // // 该部分用于对比单线程与多线程的生成效率
    // bigNum prime = generate_prime(10,100,100);
    // // bigNum prime = generate_prime_multithreaded(10,100,100,5);
    // cout << "prime: ";prime.print();cout << endl;

    int pi, qi;
    cout << "Input the digits of prime numbers p and q respectively (up to "<< mxi/2 << "): ";
    cin >> pi >> qi;
    // 小BUG：如果最终生成的素数p<q，则不能正确加密解密。所以最好输入的pi>qi来保证p>q。
    bigNum p = generate_prime(pi,mxk,mxt), q = generate_prime(qi,mxk,mxt);
    if(p.is0()||q.is0()){
        cout << "Cannot find two prime numbers." << endl;
        exit(1);
    }
    cout << "p: ";p.print();cout << endl;
    cout << "q: ";q.print();cout << endl;
    bigNum phip = p, phiq = q;
    bigNum n = p;
    n *= q;
    p.sub1();
    q.sub1();
    p *= q;
    bigNum &phin = p;
    bigNum e(0);
    int ei = pi + qi;
    cout << "n: ";n.print();cout << endl;
    cout << "phin: ";phin.print();cout << endl;
    do{
        e = generate(ei,NULL);
        cout<< "try e: ";e.print();cout << endl;
    }while(!gcd(e,phin).is1());
    MOD(e, phin);
    bigNum d = inv_mod(e,phin);
    cout << "Public key: (n: ";n.print();cout << ", e: ";e.print();cout << ")" << endl;
    cout << "Private key: (n: ";n.print();cout << ", d: ";d.print();cout << ")" << endl;

    cout << "e.g. " << endl;
    char numM[] = "6451";
    bigNum M(numM);
    cout << "M: ";M.print();cout << endl;
    M = pow_mod(M, e, n);
    cout << "C(encrypted M): ";M.print();cout << endl;
    M = pow_mod(M, d, n);
    cout << "M(decrypted C): ";M.print();cout << endl;

    // // 该部分用于验证大数gcd的正确性
    // bigNum rnd1 = generate(5,NULL);
    // rnd1.print();
    // cout << endl;
    // bigNum rnd2 = generate(5,NULL);
    // rnd2.print();
    // cout << endl;
    // bigNum res = gcd(rnd1, rnd2);
    // res.print();
    // cout << endl;
    // bigNum res = generate_prime(mxi,100,100);
    // res.print();
    // cout << endl;
    return 0;
}