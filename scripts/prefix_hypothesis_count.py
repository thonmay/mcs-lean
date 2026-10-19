#!/usr/bin/env python3
# Exhaustive count for the prefix stability theorem (insertion-only F).
# For every labelled host G and nonempty F disjoint from G on n vertices:
#   hyp_all: +0/+1 bound for every x on every proper common prefix set
#   hyp_un : same bound only for x not in the prefix (the Lean statement)
#   common : MCS(G) and MCS(G+F) share an ordering
# Checks soundness (hyp_un -> common) and counts non-matching F covered.
import sys

def popc(x):
    return bin(x).count("1")

def analyse(n, A, B):
    full = (1 << n) - 1
    seen = {0}
    stack = [0]
    hyp_all = hyp_un = True
    while stack:
        S = stack.pop()
        if S == full:
            continue
        cnt_a = [popc(A[x] & S) for x in range(n)]
        cnt_b = [popc(B[x] & S) for x in range(n)]
        for x in range(n):
            if cnt_b[x] - cnt_a[x] > 1:
                hyp_all = False
                if not (S >> x) & 1:
                    hyp_un = False
        free = [x for x in range(n) if not (S >> x) & 1]
        ma = max(cnt_a[x] for x in free)
        mb = max(cnt_b[x] for x in free)
        for x in free:
            if cnt_a[x] == ma and cnt_b[x] == mb:
                T = S | (1 << x)
                if T not in seen:
                    seen.add(T)
                    stack.append(T)
    return hyp_all, hyp_un, full in seen

def run(n):
    pairs = [(a, b) for a in range(n) for b in range(a + 1, n)]
    m = len(pairs)
    tot = all_nm = un_nm = un_total = all_total = unsound = 0
    for gm in range(1 << m):
        for fm in range(1, 1 << m):
            if gm & fm:
                continue
            A = [0] * n
            B = [0] * n
            Fd = [0] * n
            for e, (a, b) in enumerate(pairs):
                if (gm >> e) & 1:
                    A[a] |= 1 << b; A[b] |= 1 << a
                    B[a] |= 1 << b; B[b] |= 1 << a
                if (fm >> e) & 1:
                    B[a] |= 1 << b; B[b] |= 1 << a
                    Fd[a] += 1; Fd[b] += 1
            matching = max(Fd) <= 1
            h_all, h_un, common = analyse(n, A, B)
            tot += 1
            all_total += h_all
            un_total += h_un
            if h_all and not matching:
                all_nm += 1
            if h_un and not matching:
                un_nm += 1
            if h_un and not common:
                unsound += 1
    print(f"n={n} pairs={tot} hyp_all={all_total} hyp_all_nonmatching={all_nm} "
          f"hyp_unchosen={un_total} hyp_unchosen_nonmatching={un_nm} "
          f"unsound(hyp_unchosen and no common)={unsound}", flush=True)

for n in range(3, (int(sys.argv[1]) if len(sys.argv) > 1 else 5) + 1):
    run(n)
