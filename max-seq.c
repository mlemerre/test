int max_seq(int* p, int n) {
  int res =*p;
  //@ ghost int e = 0;
  /*@ loop invariant \forall integer j; 0 <= j < i ==> res >=\at(p[j],Pre);
      loop invariant \valid(\at(p,Pre)+e) && \at(p,Pre)[e] == res;
      loop invariant 0 <= i <= n;
      loop invariant p == \at(p,Pre)+i;
      loop invariant 0 <= e < n; */
  for(int i = 0; i < n; i++) {
    if(res <*p) {
      res =*p;
      //@ghost e = i;
    }
    p++;
  }
  return res;
}
