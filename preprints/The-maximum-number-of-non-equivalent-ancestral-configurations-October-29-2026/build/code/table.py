def F(n):
    if n==1: return 0
    m,r=divmod(n,3); return (3**m*(2*r*r+8*r+23))//27
C={0:23,1:33,2:47}
def C2(k): return k*(k-1)//2
rows=[]
for a in range(1,9):
    beta=F(a)+1-C2(min(a,3))
    cells=[]
    for r in range(3):
        alpha=(F(a)+1)*C[r]; rp=(a+r)%3; carry=(a+r)//3; gamma=C[rp]*3**carry
        assert gamma-alpha>=beta, (a,r)
        cells.append(f"{alpha} & {gamma} & {gamma-alpha}")
    rows.append(f"{a} & {F(a)} & {beta} & " + " & ".join(cells) + r" \\")
print("\n".join(rows))
# finite cases a<=b<=8
for a in range(1,9):
    for b in range(a,9):
        assert (F(a)+1)*(F(b)+1)-C2(min(a,3)) <= F(a+b)
print("finite ok")
# slack table for a,b>=9
for ra in range(3):
    for rb in range(ra,3):
        carry=(ra+rb)//3; rp=(ra+rb)%3
        print(ra,rb, 27*3**carry*C[rp]-C[ra]*C[rb], C[ra]+C[rb])
