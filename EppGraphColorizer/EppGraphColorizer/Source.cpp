#define _CRT_SECURE_NO_WARNINGS
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include "time.h"
#include <cmath>
#include <algorithm>
//#include <map>
//#include <vector>
//#include <set>

#define MIN(x,y) ((x)<(y)?(x):(y))
#define MAX(x,y) ((x)>(y)?(x):(y))
#define TMALLOC(type,size) ((type*)malloc(sizeof(type)*(size)))

//Maximum size for full calculation. Full calculation could require 2^n (bytes) space and less than O(2.5^n) time
#define MAXCALCSIZE 30

//masks for CSP
#define HM (long long)0b11111
#define VM (long long)0b100001000010000100001
#define MAX_D (long long)5

//using namespace std;

//count number of non-zero bits in 64bit number
int popcount64(unsigned long long x)
{
	const unsigned long long m1 = 0x5555555555555555;
	const unsigned long long m2 = 0x3333333333333333;
	const unsigned long long m4 = 0x0f0f0f0f0f0f0f0f;
	x -= (x >> 1) & m1;
	x = (x & m2) + ((x >> 2) & m2);
	x = (x + (x >> 4)) & m4;
	x += x >> 8;
	x += x >> 16;
	x += x >> 32;
	return x & 0x7f;
}

//Check if graph have any edges at all
bool isIndep(int* graph, int n)
{
	int i, j;
	for (i = 0; i < n; i++)
		for (j = 0; j < n; j++)
			if (graph[i * n + j])
				return false;
	return true;
}

//Check if bit graph have any edges at all
bool isIndepBit(long long* graph, int n)
{
	int i;
	for (i = 0; i < n; i++)
		if (graph[i])
			return false;
	return true;
}

//Check if graph is full
bool isClique(int* graph, int n)
{
	int i, j;
	for (i = 0; i < n; i++)
		for (j = 0; j < n; j++)
			if ((!graph[i * n + j]) && (i != j))
				return false;
	return true;
}

//Check if bit graph is full
bool isCliqueBit(long long* graph, int n)
{
	int i, j;
	for (i = 0; i < n; i++)
		if ((~graph[i]) ^ ((long long)1 << i))
			return false;
	return true;
}

//Check if graph is binary, returns colored graph (array with size n) if it is, 0 if it isn't
int* isBin(int* cols, int* graph, int n)
{
	int i, j, * tovisit = (int*)malloc(sizeof(int) * n), top = 1;
	for (i = 1; i < n; i++)
	{
		tovisit[i] = -1;
		cols[i] = -1;
	}
	cols[0] = 0;
	tovisit[0] = 0;
	for (i = 0; i < n; i++)
	{
		if (tovisit[i] < 0)
		{
			for (j = 0; j < n; j++)
				if (cols[j] < 0)
				{
					cols[j] = 0;
					tovisit[i] = j;
					top++;
				}
		}
		for (j = 0; j < n; j++)
			if (graph[tovisit[i] * n + j])
			{
				if (cols[j] < 0)
				{
					tovisit[top] = j;
					top++;
					cols[j] = cols[tovisit[i]] ^ 1;
				}
				else
					if (cols[j] != (cols[tovisit[i]] ^ 1))
					{
						free(tovisit);
						return 0;
					}
			}
	}
	free(tovisit);
	return cols;
}

//Check if bit graph is binary, returns colored graph (array with size n) if it is, 0 if it isn't
bool isBinBit(long long* graph, int n)
{
	int i, j, * cols = (int*)malloc(sizeof(int) * n), * tovisit = (int*)malloc(sizeof(int) * n), top = 1;
	for (i = 1; i < n; i++)
	{
		tovisit[i] = -1;
		cols[i] = -1;
	}
	cols[0] = 0;
	tovisit[0] = 0;
	for (i = 0; i < n; i++)
	{
		if (tovisit[i] < 0)
		{
			for (j = 0; j < n; j++)
				if (cols[j] < 0)
				{
					cols[j] = 0;
					tovisit[i] = j;
					top++;
				}
		}
		for (j = 0; j < n; j++)
			if (graph[tovisit[i]] & ((long long)1 << j))
			{
				if (cols[j] < 0)
					cols[j] = cols[tovisit[i]] ^ 1;
				else
					if (cols[j] != (cols[tovisit[i]] ^ 1))
					{
						free(tovisit);
						free(cols);
						return 0;
					}
			}
	}
	free(tovisit);
	free(cols);
	return 1;
}

//converts initMask, reduced by Mask into full mask
long long convToFullMask(long long initMask, long long Mask, int Mn, int n)
{
	long long res = 0;
	for (int i = n; i >= 0; i--)
		if (Mask & ((long long)1 << i))
		{
			Mn--;
			res |= (initMask & ((long long)1 << Mn)) << (i - Mn);
		}
	return res;
}

//Bron-Kerbosh algorithm for finding all cliques in the graph. Graph must be converted into bit graph
void BronKerbosh(long long* output, int* oun, long long* graph, int n, long long Rm, long long Pm, long long Xm)
{
	if (!(Pm | Xm))
	{
		output[*oun] = Rm;
		(*oun)++;
	}
	for (int i = 0; i < n; i++)
	{
		BronKerbosh(output, oun, graph, n, Rm | ((long long)1 << i), Pm & graph[i], Xm & graph[i]);
		Pm &= (~((long long)1 << i));
		Xm |= ((long long)1 << i);
	}
}

//finilizer for CSPd2Solve's random coloring algorithm
int* CSPd2RandFinalizer(long long* constr, int* avail, int* conn, int n, int d)
{
	//at this this point every "connected" vertex is not directly constrained by each other 
	//FOR SOME REASON UNCONNECTED ONES DON'T SEEM TO ALWAYS GET COLOURED ON A FIRST TRY, need inestigation  
	//but I check for all outcomes for some reason *shrug*
	//also, this version of algorithm assumes d=3, so all those vertices are full
	int* availbckp = TMALLOC(int, n), tav, * filstack = TMALLOC(int, n), filsize = 0, curfil = 0;
	long long t, tk;
	for (int i = 0; i < n; i++)
	{
		t = avail[i];
		t = (t & 21) + ((t & 42) >> 1);
		t = (t & 3) + ((t & 12) >> 2) + ((t & 48) >> 4);
		if ((conn[i])&&(t==d))
		{
			//conn[i] = 0;
			for (long long k = 0; k < d; k++)
			{
				filsize = 0;
				curfil = 0;
				memcpy(availbckp, avail, n * sizeof(int));
				avail[i] = 1 << k;
				for (int j = 0; j < n; j++)
				{
					tav = avail[j];
					avail[j] &= ~((constr[i * n + j] & (HM << (k * MAX_D))) >> (k * MAX_D));
					if (!avail[j])
					{
						goto connchoiceisinvalid;
					}
					if (tav != avail[j])
					{
						filstack[filsize] = j;
						filsize++;
					}
				}
				while (filsize > curfil)
				{
					t = 1;
					tk = 0;
					while (!(avail[filstack[curfil]] & t))
					{
						t <<= 1;
						tk++;
					}
					for (int j = 0; j < n; j++)
					{
						tav = avail[j];
						avail[j] &= ~((constr[filstack[curfil] * n + j] & (HM << (tk * MAX_D))) >> (tk * MAX_D));
						if (!avail[j])
						{
							goto connchoiceisinvalid;
						}
						if (tav != avail[j])
						{
							filstack[filsize] = j;
							filsize++;
						}
					}
					curfil++;
				}
				if (CSPd2RandFinalizer(constr, avail, conn, n, d))
				{
					return avail;
				}
			connchoiceisinvalid:
				memcpy(avail, availbckp, n * sizeof(int));
			}

			//if it reaches this place, it means that previously chosen colourings are invalid
			free(availbckp);
			free(filstack);
			//conn[i] = 1;
			return 0;
		}
	}
	for (int i = 0; i < n; i++)
	{
		t = avail[i];
		t = (t & 21) + ((t & 42) >> 1);
		t = (t & 3) + ((t & 12) >> 2) + ((t & 48) >> 4);
		if (t == 0)
		{
			//if it reaches this place, it means that previously chosen colourings are invalid
			free(availbckp);
			free(filstack);
			return 0;
		}
		if (t > 1)
		{
			//some weren't connected but weren't coloured yet either, should only have 2 choices of colour
			t = 1;
			tk = 0;
			for (long long k = 0; k < 2; k++)
			{
				filsize = 0;
				curfil = 0;
				while (!(avail[i] & t))
				{
					t <<= 1;
					tk++;
				}
				memcpy(availbckp, avail, n * sizeof(int));
				avail[i] = 1 << tk;
				for (int j = 0; j < n; j++)
				{
					tav = avail[j];
					avail[j] &= ~((constr[i * n + j] & (HM << (tk * MAX_D))) >> (tk * MAX_D));
					if (!avail[j])
					{
						goto unconnchoiceisinvalid;
					}
					if (tav != avail[j])
					{
						filstack[filsize] = j;
						filsize++;
					}
				}
				while (filsize > curfil)
				{
					int tt = 1;
					long long ttk = 0;
					while (!(avail[filstack[curfil]] & tt))
					{
						tt <<= 1;
						ttk++;
					}
					for (int j = 0; j < n; j++)
					{
						tav = avail[j];
						avail[j] &= ~((constr[filstack[curfil] * n + j] & (HM << (ttk * MAX_D))) >> (ttk * MAX_D));
						if (!avail[j])
						{
							goto unconnchoiceisinvalid;
						}
						if (tav != avail[j])
						{
							filstack[filsize] = j;
							filsize++;
						}
					}
					curfil++;
				}
				if (CSPd2RandFinalizer(constr, avail, conn, n, d))
				{
					return avail;
				}
			unconnchoiceisinvalid:
				memcpy(avail, availbckp, n * sizeof(int));
				t <<= 1;
				tk++;
			}

			//if it reaches this place, it means that previously chosen colourings are invalid
			free(availbckp);
			free(filstack);
			return 0;
		}
	}

	//graph is already fully coloured
	free(availbckp);
	free(filstack);
	return avail;
}

//Constraint Satisfaction Problem solver for David Eppstein's algorithm
int* CSPd2Solve(long long* constr, int* avail, int* conn, int n, int d = 3)
{
	long long dloc = d;
	if (dloc > 3)
	{
		printf("not supported yet");
		return 0;
	}
	if (n < 1)
		return 0;
	int* flist = (int*)malloc(sizeof(int) * n), * slist = (int*)malloc(sizeof(int) * n);
	long long t, i, j, k1, k2, k;
	bool wasreduced = true;
	//this part is less than O(n^4), but each run should reduce number of vertices by at least 1
	while (wasreduced)
	{
		//constraint correctness check
		for (i = 0; i < n; i++)
			for (j = 0; j < n; j++)
				if (constr[i * n + j] && constr[j * n + i])
				{
					for  (k1 = 0; k1 < dloc; k1++)
						for (k2 = 0; k2 < dloc; k2++)
						{
							if ((!(constr[i * n + j]&((long long)1<<(k2*MAX_D+k1)))) != (!(constr[j * n + i] & ((long long)1 << (k1 * MAX_D + k2)))))
								printf("incorrect constraints\n");
						}
				}
				else
				{
					if (constr[i * n + j] != constr[j * n + i])
						printf("incorrect constraints\n");
				}
		wasreduced = false;
		//constraint cleanup, seems to introduce bugs
		/*for (k = 0; k < dloc; k++)
		{
			for (i = 0; i < n; i++)
			{
				if (!(avail[i] & (1 << k)))
				{
					for (j = 0; j < n; j++)
					{
						constr[i * n + j] ^= constr[i * n + j] & (HM << (MAX_D * k));
						constr[j * n + i] ^= constr[j * n + i] & (VM << k);
					}
				}
			}
		}*/
		//reductions
		for (i = 0; i < n; i++)
		{
			t = avail[i];
			t = (t & 21) + ((t & 42) >> 1);
			t = (t & 3) + ((t & 12) >> 2) + ((t & 48) >> 4);
			if (t == 0) 
				return 0;
			if (t == 1)
			{
				//doing it outside of connectedness check is important because of lemma 2
				k = 0;
				while (!(avail[i] & t))
				{
					t <<= 1;
					k++;
				}
				for (j = 0; j < n; j++)
				{
					avail[j] &= ~((constr[i * n + j] & (HM << (k * MAX_D))) >> (k * MAX_D));
				}
				//conn[i] = 0;
				//add constraint cleanup?
			}
			else
			{
				if (conn[i])
				{
					//Lemma6
					for (k = 0; k < dloc; k++)
					{
						if (avail[i] & (1 << k))
						{
							for (int j = 0; j < n; j++)
								if (conn[j] && ((constr[i * (long long)n + j] & (HM << (k * MAX_D))) == (1 << (dloc - 1))))
								{
									avail[i] ^= (1 << k);
									//add cleanup
									wasreduced = true;
									break;
								}
						}
					}
					//Lemma4, possibly bugged
					for (k1 = 0; k1 < (dloc - 1); k1++)
						for (k2 = k1 + 1; k2 < dloc; k2++)
						{
							if ((avail[i] & (1 << k1)) && (avail[i] & (1 << k2)))
							{
								bool canredl = true, canredr = true;
								for (int j = 0; j < n; j++)
								{
									long long t1 = (constr[i * (long long)n + j] & (HM << (k1 * MAX_D))) >> (k1 * MAX_D);
									long long t2 = (constr[i * (long long)n + j] & (HM << (k2 * MAX_D))) >> (k2 * MAX_D);
									//if (conn[j]) //seems to introduceq bugs
									{
										if ((t1 & t2) ^ t1)
										{
											canredl = false;
										}
										if ((t1 & t2) ^ t2)
										{
											canredr = false;
										}
									}
								}
								if (canredl)
								{
									avail[i] ^= (1 << k2);
									//add cleanup
									wasreduced = true;
								}
								else
									if (canredr)
									{
										avail[i] ^= (1 << k1);
										//add cleanup
										wasreduced = true;
									}
							}
						}
					//Lemma2
					t = avail[i];
					t = (t & 21) + ((t & 42) >> 1);
					t = (t & 3) + ((t & 12) >> 2) + ((t & 48) >> 4);
					if (t == 2)
					{
						wasreduced = true;
						int fltop = 0, sltop = 0;
						for (k1 = 0; !(avail[i] & (1 << k1)); k1++);
						for (k2 = k1 + 1; !(avail[i] & (1 << k2)); k2++);
						for (j = 0; j < n; j++)
						{
							if (constr[i * n + j] & (HM << (k1 * MAX_D)))
							{
								flist[fltop] = j;
								fltop++;
							}
							if (constr[i * n + j] & (HM << (k2 * MAX_D)))
							{
								slist[sltop] = j;
								sltop++;
							}
						}
						for (j = 0; j < fltop; j++)
							for (k = 0; k < sltop; k++)
								if (slist[k] != flist[j])
								{
									for (t = 0; t < dloc; t++)
									{
										if (((constr[i * n + slist[k]] & (HM << (k2 * MAX_D))) >> (k2 * MAX_D)) & (1 << t))
											constr[slist[k] * n + flist[j]] |= ((constr[i * n + flist[j]] & (HM << (k1 * MAX_D))) >> (k1 * MAX_D)) << (t * MAX_D);
										if (((constr[i * n + flist[j]] & (HM << (k1 * MAX_D))) >> (k1 * MAX_D)) & (1 << t))
											constr[flist[j] * n + slist[k]] |= ((constr[i * n + slist[k]] & (HM << (k2 * MAX_D))) >> (k2 * MAX_D)) << (t * MAX_D);
									}
								}
						conn[i] = 0;
						continue;
					}
					//Lemma3
					bool l3fl = true;
					for (k1 = 0; (k1 < dloc) && (l3fl); k1++)
					{
						k = 0;
						long long p = -1;
						for (j = 0; j < n; j++)
						{
							if (constr[i * (long long)n + j] & (HM << (k1 * MAX_D)))
							{
								k++;
								p = j;
							}
						}
						if (k == 1)
						{
							for (k2 = 0; k2 < dloc; k2++)
							{
								k = 0;
								int p = -1;
								if (!constr[i * (long long)n + p] & ((1 << k2) << (k1 * MAX_D)))
								{
									bool canred = true;
									for (j = 0; j < n; j++)
									{
										if ((j != i) && (constr[p * (long long)n + j] & (HM << (k2 * MAX_D))))
										{
											canred = false;
											break;
										}
									}
									if (canred)
									{
										avail[i] = 1 << k1;
										avail[p] = 1 << k2;
										for (j = 0; j < n; j++)
										{
											avail[j] &= ~((constr[i * n + j] & (HM << (k1 * MAX_D))) >> (k1 * MAX_D));
											avail[j] &= ~((constr[p * n + j] & (HM << (k2 * MAX_D))) >> (k2 * MAX_D));
											if (avail[j] == 0)
												j = j;
										}
										//conn[i] = 0;
										//conn[p] = 0;
										l3fl = false;
										wasreduced = true;
										break;
									}
								}
							}
						}
					}
					//Lemma5
					for (k = 0; k < dloc; k++)
					{
						if (avail[i] & (1 << k))
						{
							bool cancol = true;
							for (int j = 0; j < n; j++)
								if (conn[j] && (constr[i * n + j] & (HM << (k * MAX_D))))
								{
									cancol = false;
									break;
								}
							if (cancol)
							{
								avail[i] = 1 << k;
								//conn[i] = 0;
								for (j = 0; j < n; j++)
								{
									avail[j] &= ~((constr[i * n + j] & (HM << (k * MAX_D))) >> (k * MAX_D));
									if (avail[j] == 0)
										j = j;
								}
								//add cleanup
								wasreduced = true;
								break;
							}
						}
					}
				}
			}
		}
	}
	free(flist);
	free(slist);
	//random coloring, not yet suitable for d>3
	{
		int p[4] = { 1,1,1,1 }, k = 4, v1 = -1, v2, *availt = (int*)malloc(sizeof(int) * n);
		int* connt = (int*)malloc(sizeof(int) * n);
		long long* constrt = (long long*)malloc(sizeof(long long) * n * n), c1 = -1, c2;
		for (i = 0; (i < n) && (v1 < 0); i++)
		{
			t = avail[i];
			t = (t & 21) + ((t & 42) >> 1);
			t = (t & 3) + ((t & 12) >> 2) + ((t & 48) >> 4);
			if (conn[i] && t > 2)
				for (j = 0; j < n; j++)
				{
					t = avail[j];
					t = (t & 21) + ((t & 42) >> 1);
					t = (t & 3) + ((t & 12) >> 2) + ((t & 48) >> 4);
					if (conn[j] && constr[i * n + j] && t > 2)
					{
						v1 = i;
						v2 = j;
					}
				}
		}
		if (v1 >= 0)
		{
			for (i = 0; (i < dloc) && (c1 < 0); i++)
				if (avail[v1] & (1 << i))
					for (j = 0; j < dloc; j++)
					{
						if ((avail[v2] & (1 << j)) && (constr[v1 * n + v2] & ((1 << i) << (j * MAX_D))))
						{
							c1 = i;
							c2 = j;
						}
					}
		}
		if (v1 >= 0 && c1 >= 0)
		{
			for (i = 0; i < 4; i++)
			{
				memcpy(availt, avail, sizeof(int) * n);
				memcpy(constrt, constr, sizeof(long long)* n * n);
				memcpy(connt, conn, sizeof(int)* n);
				t = rand() % k;
				for (j = 0; t > 0 && j < 4; j++)
				{
					if (p[j])
						t--;
				}
				if (j < 4)
				{
					k--;
					if (j & 1)
					{
						avail[v1] ^= 1 << c1;
						avail[v2] ^= 1 << ((c2 + (j >> 1)) % dloc);
					}
					else
					{
						avail[v1] ^= 1 << ((c1 + (j >> 1)) % dloc);
						avail[v2] ^= 1 << c2;
					}
					if (CSPd2Solve(constrt, avail, connt, n, dloc))
					{
						//finisher
						free(availt);
						free(constrt);
						free(connt);
						return availt;
					}
				}
				memcpy(avail, availt, sizeof(int)* n);
				memcpy(constr, constrt, sizeof(long long)* n* n);
				memcpy(conn, connt, sizeof(int)* n);
			}
		}
		else
		{
			//all available vertices are not connected, so begin coloring
			return CSPd2RandFinalizer(constr, avail, conn, n, d);
		}
	}
	//Lemma 8(isolated constraint, recursion either way, branching in case of >3)
	//Lemma 9(dangling constraint, branching recursion)

	return avail;
}

//Check if graph is trinary (using David Eppstein's algorithm)
//Works by optimizing the graph and converting it into Constraint Satisfaction Problem
int* isTri(int* cols, int* graph, int n)
{
	int i, j, maxi=-1, max = 0, c, * conn = TMALLOC(int, n),*ans;
	long long* constr = TMALLOC(long long, n * n);
	for (i = 0; i < n; i++)
	{
		cols[i] = 7;
		conn[i] = 1;
		c = 0;
		for (j = 0; j < n; j++)
		{
			if (graph[i * n + j])
			{
				c++;
				constr[i * n + j] = (long long)1 | ((long long)1 << (MAX_D + 1)) | ((long long)1 << ((MAX_D + 1) * 2));
			}
			else
			{
				constr[i * n + j] = 0;
			}
		}
		if (c > max)
		{
			max = c;
			maxi = i;
		}
		//get rid of vertices that don't matter in 3-coloring (a very simple and not throughout way of doing that, tbh)
		if (c < 3)
			conn[i] = 0;
	}
	//colour the vertex with the max amount of neighbours, thus easily getting rid of max+1 vertices
	if (maxi >= 0)
		cols[maxi] = 1;
	ans = CSPd2Solve(constr, cols, conn, n, 3);
	free(constr);
	free(conn);
	return ans;
}

bool isTriBit(long long* graph, int n)
{
	int i, j, * avail = (int*)malloc(sizeof(int) * n), maxi = -1, max = 0, c, *conn = TMALLOC(int, n), *ret;
	long long* constr = TMALLOC(long long, n * n);
	for (i = 0; i < n; i++)
	{
		avail[i] = 7;
		conn[i] = 1;
		c = 0;
		for (j = 0; j < n; j++)
		{
			if (graph[i]&((long long)1<<j))
			{
				c++;
				constr[i * n + j] = (long long)1 | ((long long)1 << (MAX_D + 1)) | ((long long)1 << ((MAX_D + 1) * 2));
			}
			else
			{
				constr[i * n + j] = 0;
			}
		}
		if (c > max)
		{
			max = c;
			maxi = i;
		}
		//get rid of vertices that don't matter in 3-coloring (a very simple and not throughout way of doing that, tbh)
		if (c < 3)
			conn[i] = 0;
	}
	//colour the vertex with the max amount of neighbours, thus easily getting rid of max+1 vertices
	if (maxi > 0)
		avail[maxi] = 1;
	ret = CSPd2Solve(constr, avail, conn, n, 3);
	free(constr);
	free(conn);
	free(avail);
	return (ret?true:false);
}

//gen bit graph from array graph using provided mask. Will return size of the graph to rn
long long* GenBitGraph(int* rn, long long mask, int* graph, int n)
{
	int j;
	*rn = 0;
	long long* res = (long long*)malloc(sizeof(long long) * n);
	for (int i = 0; i < n; i++)
		if (mask & ((long long)1 << i))
		{
			for (j = n - 1; j >= 0; j--)
				if (mask & ((long long)1 << j))
					res[*rn] |= (((long long)graph[i * n + j]) << j);
				else
					res[*rn] >>= 1;
			*rn++;
		}
	return res;
}

//gen bit graph from bit graph using provided mask. Will return size of the graph to rn
long long* GenBitGraphBit(int* rn, long long mask, long long* graph, int n)
{
	int j;
	*rn = 0;
	long long* res = (long long*)malloc(sizeof(long long) * popcount64(mask));
	for (int i = 0; i < n; i++)
		if (mask & ((long long)1 << i))
		{
			for (j = n - 1; j >= 0; j--)
				if (mask & ((long long)1 << j))
					res[*rn] |= (graph[i] & ((long long)1 << j));
				else
					res[*rn] >>= 1;
			*rn++;
		}
	return res;
}

//MIS section

//tries to get three vertexes of a cycle that do nat make cycle on their own (for addMIS)
bool getTrio(int* res, long long* graph, int n)
{
	long long pars = ~(((~(long long)0) >> n) << n);
	int c = 0, i = n - 1, ni;
	while (pars)
		if (pars & ((long long)1 << i))
		{
			if (c < 2)
			{
				ni = (int)floor(log(graph[i]) / log(2));
				if (pars ^ ((long long)1 << ni))
					ni = (int)floor(log(graph[i] ^ ((long long)1 << ni)) / log(2));
				res[c] = i;
				c++;
				pars ^= ((long long)1 << i);
				i = ni;
			}
			if (c >= 3)
			{
				ni = (int)floor(log(graph[i]) / log(2));
				if (pars ^ ((long long)1 << ni))
					ni = (int)floor(log(graph[i] ^ ((long long)1 << ni)) / log(2));
				if (pars ^ ((long long)1 << ni))
				{
					c = 0;
					i = (int)floor(log(pars) / log(2));
				}
				else
				{
					return true;
				}
			}
		}
	return false;
}

//smallMIS from David Epstein's article "Small Maximal Independent Sets and Faster Exact Graph Coloring" adapted for colouring
void addMIS(long long S, long long I, int k, char* X, long long* graph, int n)
{
	int ti, tu;
	if (k == 0 || S == 0)
	{
		X[S | I] = MIN(X[S | I], X[S] + 1);
		return;
	}
	int tgrsize;
	long long* tgraph = GenBitGraphBit(&tgrsize, S, graph, n);
	//Check for >=3
	for (int i = 0; i < tgrsize; i++)
		if (popcount64(tgraph[i]) > 2)
		{
			ti = (int)round(log(convToFullMask((long long)1 << i, S, tgrsize, n)) / log(2));
			addMIS(S & (~((long long)1 << ti)), I, k, X, graph, n);
			addMIS(S & (~graph[ti]), I | ((long long)1 << ti), k - 1, X, graph, n);
			return;
		}
	//Check for ==1
	for (int i = 0; i < tgrsize; i++)
		if (popcount64(tgraph[i]) == 1)
		{
			ti = (int)round(log(convToFullMask((long long)1 << i, S, tgrsize, n)) / log(2));
			tu = (int)round(log(convToFullMask(tgraph[i], S, tgrsize, n)) / log(2));
			addMIS(S & (~graph[tu]), I | ((long long)1 << tu), k - 1, X, graph, n);
			addMIS(S & (~graph[ti]), I | ((long long)1 << ti), k - 1, X, graph, n);
			return;
		}
	//Check for ==0
	for (int i = 0; i < tgrsize; i++)
		if (!tgraph[i])
		{
			ti = (int)round(log(convToFullMask((long long)1 << i, S, tgrsize, n)) / log(2));
			addMIS(S & (~graph[ti]), I | ((long long)1 << ti), k - 1, X, graph, n);
			return;
		}
	//Check for triangle
	int trio[3];
	if (k >= (popcount64(S) / 3) || (getTrio(trio, tgraph, tgrsize)))
	{
		tu = (int)round(log(convToFullMask((long long)1 << trio[1], S, tgrsize, n)) / log(2));
		addMIS(S & (~graph[tu]), I | ((long long)1 << tu), k - 1, X, graph, n);
		tu = (int)round(log(convToFullMask((long long)1 << trio[0], S, tgrsize, n)) / log(2));
		addMIS(S & (~graph[tu]), I | ((long long)1 << tu), k - 1, X, graph, n);
		ti = (int)round(log(convToFullMask((long long)1 << trio[2], S, tgrsize, n)) / log(2));
		addMIS(S & (~(((long long)1 << tu) | graph[ti])), I | ((long long)1 << ti), k - 1, X, graph, n);
	}
}

//Colorize the graph using David Eppstein algorithms
int* DavidEppColorize(int* cols, int* graph, int n)
{
	if (n <= MAXCALCSIZE)
	{
		long long max = (long long)1 << n;
		char* colc = (char*)malloc((long long)sizeof(char) * max);
		if (colc == NULL)
		{
			printf("not enough memory");
			return 0;
		}
		long long i, j;
		colc[0] = 0;
		for (i = 1; i < max; i++)
		{
			colc[i] = 127;
		}
		long long* tgraph;
		int tgrsize;
		{
			tgraph = GenBitGraph(&tgrsize, ~(long long)0, graph, n);
			long long* cliques = (long long*)malloc(sizeof(long long) * n * n);
			int clin = 0;
			BronKerbosh(cliques, &clin, tgraph, n, 0, ~(((~(long long)0) >> n) << n), 0);
			for (i = 0; i < clin; i++)
			{
				colc[cliques[i]] = popcount64(cliques[i]);
			}
			free(tgraph);
			free(cliques);
		}

		for (i = 0; i < max; i++)
		{
			if (colc[i] == 127)
			{
				tgraph = GenBitGraph(&tgrsize, i, graph, n);
				if (isIndepBit(tgraph, tgrsize))
					colc[i] = 1;
				else
				{
					if (isBinBit(tgraph, tgrsize))
						colc[i] = 2;
					else
					{
						if (isTriBit(tgraph, tgrsize))
							colc[i] = 3;
					}
				}
			}
		}
		for (i = 0; i < max; i++)
		{
			if ((colc[i] > 2) && (colc[i] < 127))
			{
				//tgraph = GenBitGraph(&tgrsize, i, graph, n);
				//tgrsize = popcount64(i);
				tgraph = GenBitGraph(&tgrsize, ~((long long)0), graph, n);
				addMIS((max - 1) & (~i), 0, tgrsize / colc[i], colc, tgraph, n);
			}
		}

		int col;
		col = colc[max - 1];
		long long s = max - 1, dist;
		for (i = max - 1; i >= 0 && i < max; i--)
		{
			if ((colc[i] != 127 && colc[i] > colc[max - 1]) || (colc < 0))
				printf("\nERROR\n");
			if (((i & (~s)) == 0) && (colc[i] == colc[s]) && (colc[s & (~i)] == 1))
			{
				dist = s & (~i);
				for (j = 0; j < n; j++)
					if ((long long)1 << j & dist)
						cols[i] = col;
				col--;
			}
		}
		return cols;
	}
	else
	{
		printf("Graph is too big!\n");
		return 0;
	}
}

//main colourizing algorithm
int* mainColorizer(int* cols, int* graph, int n)
{
	int i, j;
	bool fl;
	if (isIndep(graph, n))
	{
		for (i = 0; i < n; i++)
			cols[i] = 1;
	}
	else
	{
		if (isClique(graph, n))
		{
			for (i = 0; i < n; i++)
				cols[i] = i;
		}
		else
		{
			fl = isBin(cols, graph, n);
			if (!fl)
			{
				fl = isTri(cols, graph, n);
				if (!fl)
					fl = DavidEppColorize(cols, graph, n);
			}
		}
	}
	return cols;
}

int main()
{
	while (1)
	{
		int n;
		scanf("%i", &n);
		if (n <= 100)
		{
			int* graph = TMALLOC(int, n * n);
			int* cols = TMALLOC(int, n);
			int i, j;
			for (i = 0; i < n; i++)
				for (j = 0; j < n; j++)
				{
					scanf("%i", graph + i * n + j);
					if (i == j)
						graph[i * n + j] = 0;
				}
			mainColorizer(cols, graph, n);
			if (cols)
				for (i = 0; i < n; i++)
					printf("%i ", cols[i]);
		}
		printf("\n");
	}
	return 0;
}