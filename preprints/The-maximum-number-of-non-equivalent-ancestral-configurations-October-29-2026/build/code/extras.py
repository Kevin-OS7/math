import sys
sys.setrecursionlimit(10000)
LEAF=()
def node(x,y): return (x,y) if x<=y else (y,x)
def f(n):
    if n==1: return 0
    m,r=divmod(n,3); return (3**m*(2*r*r+8*r+23))//27
NMAX=int(sys.argv[1])
shapes={1:[LEAF]}
for n in range(2,NMAX+1):
    s=set()
    for a in range(1,n//2+1):
        for x in shapes[a]:
            for y in shapes[n-a]: s.add(node(x,y))
    shapes[n]=sorted(s)
P={LEAF:frozenset([LEAF])}; TOT={LEAF:0}; SZ={LEAF:1}
def prun(t):
    if t in P: return P[t]
    A,B=prun(t[0]),prun(t[1])
    P[t]=frozenset({LEAF}|{node(x,y) for x in A for y in B}); return P[t]
def tot(t):
    if t in TOT: return TOT[t]
    TOT[t]=len(prun(t))-1+tot(t[0])+tot(t[1]); return TOT[t]
def sz(t):
    if t not in SZ: SZ[t]=sz(t[0])+sz(t[1])
    return SZ[t]
def show(t):
    return "*" if t==LEAF else "("+show(t[0])+","+show(t[1])+")"
# extremal family
U={1:LEAF}
U[2]=node(LEAF,LEAF); U[3]=node(LEAF,U[2]); U[4]=node(LEAF,U[3])
for n in range(5,NMAX+1):
    U[n]=node(U[2],U[n-2]) if n in (5,6,7,8,9,11) else node(U[3],U[n-3])
for n in range(2,NMAX+1):
    vals=[(len(prun(t))-1,t) for t in shapes[n]]
    M=max(v for v,_ in vals); maxi=[t for v,t in vals if v==M]
    m=min(v for v,_ in vals); mini=[t for v,t in vals if v==m]
    tv=[(tot(t),t) for t in shapes[n]]; TM=max(v for v,_ in tv); tmaxi=[t for v,t in tv if v==TM]
    print(f"n={n}: max c*={M} (f={f(n)}) #argmax={len(maxi)} U_n is argmax: {U[n] in maxi}; min c*={m} #argmin={len(mini)}; max total={TM} #argmax_total={len(tmaxi)} U_n total={tot(U[n])} same={set(tmaxi)==set(maxi)}")
    if n<=9:
        print("   maximizers:", [show(t) for t in maxi])
        print("   total-maximizers:", [show(t) for t in tmaxi])
