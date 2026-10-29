#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <inttypes.h>

/* Enumerate exactly the necessary family in Theorem 2 of Coronado et al.
   Gray coding uses constant memory; all comparisons are integer-exact. */
int main(int argc,char **argv) {
    uint64_t n = argc>1 ? strtoull(argv[1],0,10) : 67256579;
    int m=63-__builtin_clzll(n);
    __int128 best=((__int128)1)<<126;
    uint64_t count=0, ties=0;
    for(int h=m;h<=m+2;h++) {
        int k=h-6;
        if(k<0)k=0;
        if(k>32) {fprintf(stderr,"too many candidates\n");return 2;}
        int64_t a=0,s=0,q=0,j=0;
        uint64_t prev=0;
        for(uint64_t i=0;i<(1ULL<<k);i++) {
            uint64_t gray=i^(i>>1);
            if(i) {
                int bit=__builtin_ctzll(gray^prev),l=bit+5;
                int sg=(gray&(1ULL<<bit))?1:-1;
                a+=sg*((1LL<<l)-1);s+=sg*l;q+=sg*l*l;j+=sg;
            }
            prev=gray;
            int64_t p1=(1LL<<h)-(int64_t)n-a,p0=(int64_t)n-p1-j;
            if(p1<0 || p0<=0)continue;
            count++;
            int64_t P=p1+s,Q=p1+q;
            __int128 D=(__int128)n*Q-(__int128)P*P;
            if(D<best) {best=D;ties=1;}
            else if(D==best)ties++;
        }
    }
    printf("n=%"PRIu64" candidates=%"PRIu64" minimum_D=%"PRIu64" ties=%"PRIu64"\n",n,count,(uint64_t)best,ties);
    for(int h=m;h<=m+2;h++) {
        int k=h-6;if(k<0)k=0;
        int64_t a=0,s=0,q=0,j=0;uint64_t prev=0;
        for(uint64_t i=0;i<(1ULL<<k);i++) {
            uint64_t g=i^(i>>1);
            if(i) {int b=__builtin_ctzll(g^prev),l=b+5,sg=(g&(1ULL<<b))?1:-1;
                a+=sg*((1LL<<l)-1);s+=sg*l;q+=sg*l*l;j+=sg;}
            prev=g;
            int64_t p1=(1LL<<h)-(int64_t)n-a,p0=(int64_t)n-p1-j;
            if(p1<0 || p0<=0)continue;
            int64_t P=p1+s,Q=p1+q;
            if((__int128)n*Q-(__int128)P*P!=best)continue;
            printf("height=%d p0=%"PRId64" p1=%"PRId64" gaps=",h,p0,p1);
            for(int b=0;b<k;b++)if(g&(1ULL<<b))printf(" %d",b+5);
            printf("\n");
        }
    }
    return 0;
}
