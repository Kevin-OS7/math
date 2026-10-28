def f(n):
    if n == 1: return 0
    m, r = divmod(n, 3)
    return (3**m * (2*r*r + 8*r + 23)) // 27
def C2(k): return k*(k-1)//2
bad=[]; eq=[]; near=[]
for n in range(2, 400):
    for a in range(1, n//2+1):
        b = n-a
        lhs = (f(a)+1)*(f(b)+1) - C2(min(a,3))
        if lhs > f(n): bad.append((a,b,lhs,f(n)))
        elif lhs == f(n): eq.append((a,b))
print("violations:", bad[:10])
print("equality cases:", eq)
# check closed form for n>=9
for n in range(9, 60):
    m, r = divmod(n,3); C={0:23,1:33,2:47}[r]
    assert f(n) == C*3**(m-3)
print("f(n)=C_r*3^(m-3) exact for 9<=n<60")
print([f(n) for n in range(1,12)])
