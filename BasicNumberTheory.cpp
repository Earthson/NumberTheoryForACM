#include <cstdio>
#include <cmath>
#include <cstdlib>
#include <cstring>

typedef long long typec;
/******************************************************************************
  * Variables using below
  ****************************************************************************/
const int N = 1000000;
int prime[N + 1];
int fac_table[N + 1][2];
int phi_table[N + 1];
int facque[100];
/******************************************************************************
  * Lib Functions
  ****************************************************************************/
typec gcd(typec a, typec b)
{
	return b ? gcd(b, a % b) : a;
}
typec extended_gcd(typec a, typec b, typec& x, typec& y)
{
	if(!b) return x = 1, y = 0, a;
	typec res = extended_gcd(b, a % b, x, y), tmp = x;
	x = y, y = tmp -(a /b) * y;
	return res;
}
///ax = b mod m, be sure that (b, m) = (a, m)
typec mod_equation(typec a, typec b, typec m)
{
	typec x, y;
	y = extended_gcd(a, m, x, y);
	while(x < 0) x += m;
	return (x * (b / y)) % m;
}
///return x^k, x^k < typec_MAX
typec power(typec x, typec k)
{
	typec res = 1;
	while(k) {
		if(k&1) res *= x;
		x *= x, k >>= 1;
	}
	return res;
}
///x * y mod m, for large m, 2 * m < typec_MAX
typec mul_mod(typec x, typec y, typec m)
{
	typec res = 0;
	while(y) {
		if(y&1) res += x, res %= m;
		x <<= 1, y >>= 1, x %= m;
	}
	return res;
}
/******************************************************************************
  * x^k mod m, m * m < typec_MAX, O(lgk)
  * if m * m > typec_MAX and 2 * m < typec_MAX
  * you should use mul_mod to replace operator*
  ****************************************************************************/
typec power_mod(typec x, typec k, typec m)
{
	typec res = 1;
	while(x %= m, k) {
		if(k&1) res *= x, res %= m;
		x *= x, k >>= 1;
	}
	return res;
}
/******************************************************************************
  * 1 + q + q^2 + q^3 + ... + q^(n - 1) mod m
  * O(lg(n))
  * similar to function power_mod, if m is too large, mul_mod is recommended
  ****************************************************************************/
typec power_sum_mod(typec q, typec n, typec m)
{
	typec res = 0, tmp = 1;
	while(q %= m, n) {
		if(n&1) res *= q, res += tmp, res %=m;
		tmp *= 1 + q, q *= q, tmp %= m, n >>= 1;
	}
	return res;
}
/******************************************************************************
  * Inverse in mod m system
  * a * b = g mod m, return b, and g = (a, m)
  ****************************************************************************/
typec inverse(typec a, typec m)
{
	typec x, y;
	y = extended_gcd(a, m, x, y);
	while(x < 0) x += m;
	return x;
}
/******************************************************************************
  * Linear congruence theorem
  * x = a (mod p)
  * y = b (mod q)
  * for (p, q) = 1, 0 <= x < pq < typec_MAX
  ****************************************************************************/
typec linear_congruence(typec a, typec b, typec p, typec q)
{
	typec x, y;
	y = extended_gcd(p, q, x, y);
	if(x < 0 && b > a) {
		x += q / y;
	} else if(x > 0 && b < a) {
		x -= q / y;
	}
	x *= (b - a) / y;
	x = p * x + a;
	x %= p * q / y;
	return x;
}
/******************************************************************************
  * Prime Table
  * O(n)
  * Need: int* prime
  ****************************************************************************/
int prime_table()
{
	memset(prime, 0, sizeof(prime));
	for(int i = 2; i <= N; i++) {
		if(!prime[i]) prime[++prime[0]] = i;
		for(int j = 1; j <= prime[0] && prime[j] <= N / i; j++) {
			prime[prime[j] * i] = 1;
			if(i % prime[j] == 0) break;
		}
	}
	return prime[0];
}
/******************************************************************************
  * factor Table
  * O(n)
  * Note: You can get a prime table from this function too
  * Need: int* prime, facque
  ****************************************************************************/
void get_factors() 
{
	memset(fac_table, 0, sizeof(fac_table));
	memset(prime, 0, sizeof(prime));
	prime[0] = 0;
	fac_table[0][0] = 0, fac_table[0][1] = 1;
	for(int i = 2; i <= N; i++) {
		if(!prime[i]) {
			prime[++prime[0]] = i;
			fac_table[i][0] = i;
			fac_table[i][1] = 1;
		}
		for(int j = 1; j <= prime[0] && prime[j] <= N / i; j++) {
			prime[i * prime[j]] = 1;
			if(fac_table[i][0] != 1) {
				fac_table[i * prime[j]][1] = i;
			} else {
				fac_table[i * prime[j]][1] = fac_table[i][1];
			}
			if(i % prime[j]) {
				fac_table[i * prime[j]][0] = prime[j];
			} else {
				fac_table[i * prime[j]][0] = 1;
				break;
			}
		}
	}
}
/******************************************************************************
  * return factors of given n, using fac_table above, O(1)
  * facque[0] is the number of factors, facque[1~facque[0]] are factors
  * Note!!!:every factor is prime.
  * eg. 2 is one factor of 12, factor would return 2 instead of 4
  * Need: int* facque
******************************************************************************/
void getfac(int n)
{
	facque[0] = 0;
	do {
		if(fac_table[n][0] != 1) {
			facque[++facque[0]] = fac_table[n][0];
		}
		n = fac_table[n][1];
	} while(n != 1);
}
/******************************************************************************
  * get factor of n
  * O(sqrt(n))
  * factor[][0] is prime factor
  * factor[][1] is factor generated by this prime
  * factor[][2] is factor counter
  * eg. n = 4, then factor[][0] = 2, factor[][1] = 4, factor[][2] = 2
  * Need: Prime Table
  ****************************************************************************/
int factor[100][3], facnt;
int get_fac2(int n)
{
	facnt = 0;	
	for(int i = 1; prime[i] <= n / prime[i]; i++) {
		factor[facnt][1] = 1, factor[facnt][2] = 0;
		if(!(n % prime[i])) {
			factor[facnt][0] = prime[i];
		}
		while(!(n % prime[i])) {
			factor[facnt][2]++;
			factor[facnt][1] *= prime[i];
			n /= prime[i];
		}
		if(factor[facnt][1] > 1) facnt++;
	}
	if(n != 1) {
		factor[facnt][0] = n;
		factor[facnt][1] = n;
		factor[facnt++][2] = 1;
	}
	return facnt;
}
/******************************************************************************
  * Miller-rabin Primality Test
  * be sure that x * x <= typec_MAX
  * if x is large, please use mul_mod instead of operator*
  ****************************************************************************/
bool MR_primality_test(typec x)
{
	bool flag = true;
	int k = 0, cnt = 30; ///cnt is test times
	typec a, q = x - 1, s;
	while(!(q&1)) k++, q >>= 1;
	while(cnt-- && flag) {
		a = rand() % (x - 1), a++;
		s = power_mod(a, q, x);
		if(s == 1) continue;
		for(int j = k; j && flag; j--) {
			if(s == x - 1) flag = false;
			s *= s, s %= x;
		}
		flag = !flag;
	}
	return flag;
}
bool is_prime(typec x)
{
	return MR_primality_test(x);
}
/******************************************************************************
  * Pollard rho Algorithm for integer factorization
  * O(n^0.25)
  * return: one factor of n
  * be sure that n is not a prime
  ****************************************************************************/
typec pollard_rho(typec n)
{
	typec x, y, d, c = 1;
	while(1) {
		y = x = 2;
		while(1) {
			x *= x, x %= n, x += c, x %= n;
			y *= y, y %= n, y += c, y %= n;
			y *= y, y %= n, y += c, y %= n;
			d = gcd(abs(y - x), n);
			if(d == n) break;
			if(d > 1) return d;
		}
		c++;
	}
	return 0;
}
/******************************************************************************
  * pollard rho and basic algorithm for integer factorization
  * for n < 10^18
  ****************************************************************************/
typec facs[100], faccnt[100];
int cnt = 0;
void rho(typec x)
{
    int i, flag = 1;
    typec a;
	while(x != 1) {
		if(is_prime(x)) {
			for(i = 0; i < cnt && flag; i++) {
				if(facs[i] == x) {
					faccnt[i]++;
					flag = 0;
				}
			}
			if(flag) {
				facs[cnt] = x;
				faccnt[cnt++] = 1;
			}
			flag = 1;
			return;
		} else {
			a = pollard_rho(x);
			while(x != 1) {
				rho(a);
				x /= a;
				a = x;
			}
		}
	}
}
void get_facs(typec x)
{
	int i;
	for(i = 1; x != 1 && i <= prime[0]; i++) {
		if(!(x % prime[i])) {
			facs[cnt] = prime[i];
			faccnt[cnt] = 0;
			while(!(x % prime[i])) {
				faccnt[cnt]++;
				x /= prime[i];
			}
			cnt++;
			}
	}
	if(x == 1) return;
	if(x / N < N) {
 		facs[cnt] = x;
		faccnt[cnt++] = 1;
		return;
	}
	rho(x);
}
/******************************************************************************
  * phi(n)
  * O(sqrt(n))
  ****************************************************************************/
typec phi(typec n)
{
	typec res = n;
	for(int i = 2; i <= n / i; i++) {
		if(!(n % i)) res /= i, res *= i -1;
		while(!(n % i)) n /= i;
	}

	if(n > 1) res /= n, res *= n - 1;
	return res;
}
/******************************************************************************
  * phi(n)
  * O(sqrt(n))
  * Need: Prime Table
  * if size of table is N, be sure that n * n <= N
  ****************************************************************************/
typec phi2(typec n)
{
	typec res = n;
	for(int i = 1; i <= prime[0] && prime[i] <= n; i++) {
		if(!(n % prime[i])) res /= prime[i], res *= prime[i] - 1;
		while(!(n % prime[i])) n /= prime[i];
	}
	if(n > 1) res /= n, res *= n - 1;
	return res;
}
/******************************************************************************
  * Phi Table
  * O(n)
  * Need: int* phi_table, prime
  * Note: You can get a prime table from this function, too.
  ****************************************************************************/
void get_phis()
{
	memset(phi_table, 0, sizeof(phi_table));
	prime[0] = 0;
	for(int i = 2; i <= N; i++) {
		if(!phi_table[i]) {
			prime[++prime[0]] = i;
			phi_table[i] = i - 1;
		}
		for(int j = 1; j <= prime[0] && prime[j] <= N / i; j++) {
			if(i % prime[j]) {
				phi_table[i * prime[j]] = phi_table[i] * (prime[j] - 1);
			} else {
				phi_table[i * prime[j]] = phi_table[i] * prime[j];
				break;
			}
		}
	}
}
/******************************************************************************
  * K-th root mod m
  * x^k = b (mod m), find x
  * be sure that (b, m) = 1, and (k, phi(m)) = 1
  ****************************************************************************/
typec kth_root_mod(typec b, typec k, typec m)
{
	typec u, v, phm;
	phm = phi(m); ///you can use other phi function
	v = extended_gcd(k, m, u, v);
	if(u < 0) u += phm / v;
	return power_mod(b, u, m);
}
/******************************************************************************
  * Polya for Diheral group
  * (n rotational symmetries and n reflection symmetries)
  * with n points and c colors
  ****************************************************************************/
typec polya(typec c, int n)
{
	typec res = 0;
	for(int i = 0; i < n; i++) {
		res += power(c, gcd(i, n));
	}
	if(n&1) {
		for(int i = 0; i < n; i++) {
			res += power(c, n / 2 + 1);
		}
	} else {
		for(int i = 0; i < n / 2; i++) {
			res += power(c, n / 2) + power(c, n / 2 + 1);
		}
	}
	return res;
}

/******************************************************************************
  * Differential Sequence
  * init: O(order^2)
  * you should init the cof[i] with the value of i-th value of sequence
  * the sequene start from startfrom, default is 0, so a[0] is the first one
  * 	of sequence a
  * calc: O(order)
  ****************************************************************************/

const int ORDERLIM = 100;

double cof[ORDERLIM + 1];
int order;
const int startfrom = 0;

void init()
{
	int i, j;
	for(i = 1; i <= order; i++) {
		for(j = order; j >= i; j--) {
			cof[j] -= cof[j - 1];
		}
	}
}

double calc(double n)
{
	int i;
	double res = 0;
	for(i = order; i > 0; i--) {
		res += cof[i];
		res *= (n - i + 1 - startfrom) / i;	
	}
	res += cof[i];
	return res;
}

/******************************************************************************
  * MOD version of Differential Sequence
  * cof <= MOD
  * MOD >= order
  * MOD should be prime
  * need inverse in mod MOD system
  ****************************************************************************/
typec MOD = 1000000007;
typec cof[ORDERLIM + 1];
typec inv[ORDERLIM + 1];
int order;
const int startfrom = 0;

void init()
{
	int i, j;
	for(i = 1; i <= order; i++) {
		inv[i] = inverse(i, MOD);
		for(j = order; j >= i; j--) {
			cof[j] -= cof[j - 1];
		}
	}
}

typec calc(typec n)
{
	int i;
	typec res = 0;
	for(i = order; i > 0; i--) {
		res += cof[i], res %= MOD;
		res *= (n - i + 1 - startfrom) % MOD * inv[i] % MOD;
		res %= MOD;
	}
	res += cof[i], res %= MOD;
	while(res < 0) res += MOD;
	return res;
}
