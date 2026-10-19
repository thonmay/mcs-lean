#!/usr/bin/env python3
"""Sanity checks for the probe section of the paper, against from-scratch
canonical MCS recomputation on random graphs (standard library only, fixed
seeds, so the printed counts are reproducible).

(F) insertion: the first window position satisfying the old-graph break
    criterion, located by plateaus + per-value position lists + range-max
    descent, equals the first changed position of the new canonical order.
(N) after a no-break insertion, (w_j) is unchanged and (M_j) changes only at
    j = pos(v), by +1.
(D) deletion: the step at pos(v) breaks iff R = M or (R = M - 1 and r < v),
    with (R, r) the per-step runner-up count and smallest runner-up vertex.
(R) a no-break deletion can change the runner-up data at other steps.
"""
import random, bisect

def canon(n, adj):
    S = set(); o = []; M = []; R = []; r = []
    for _ in range(n):
        c = {y: len(adj[y] & S) for y in range(n) if y not in S}
        m = max(c.values()); w = min(y for y in c if c[y] == m)
        rest = {y: k for y, k in c.items() if y != w}
        if rest:
            rm = max(rest.values()); R.append(rm); r.append(min(y for y in rest if rest[y] == rm))
        else:
            R.append(None); r.append(None)
        o.append(w); M.append(m); S.add(w)
    return o, M, R, r

class Sparse:
    def __init__(s, a):
        s.t = [a[:]]; k = 1
        while (1 << k) <= len(a):
            p = s.t[-1]; h = 1 << (k - 1)
            s.t.append([max(p[i], p[i + h]) for i in range(len(a) - (1 << k) + 1)]); k += 1
    def first_gt(s, lo, hi, x):
        # smallest index p in [lo, hi) with a[p] > x, by greedy power-of-two descent
        p = lo
        for k in range(len(s.t) - 1, -1, -1):
            if p + (1 << k) <= hi and s.t[k][p] <= x:
                p += 1 << k
        return p if p < hi and s.t[0][p] > x else None

def probe(n, adj, o, M, u, v):
    pos = {x: i for i, x in enumerate(o)}
    if pos[u] > pos[v]: u, v = v, u
    a, b = pos[u] + 1, pos[v]
    if a >= b: return None
    Pos = {}; W = {}
    for j, (m, w) in enumerate(zip(M, o)):
        Pos.setdefault(m, []).append(j); W.setdefault(m, []).append(w)
    SM = {m: Sparse(W[m]) for m in W}
    nb = sorted(pos[x] for x in adj[v])
    c = sum(1 for p in nb if p < a)
    bounds = [a] + [p + 1 for p in nb if a <= p < b - 1] + [b]
    for i in range(len(bounds) - 1):
        l, rr = bounds[i], bounds[i + 1]
        cand = []
        L = Pos.get(c, []); k = bisect.bisect_left(L, l)
        if k < len(L) and L[k] < rr: cand.append(L[k])
        L2 = Pos.get(c + 1, []); k1 = bisect.bisect_left(L2, l); k2 = bisect.bisect_left(L2, rr)
        if k1 < k2:
            q = SM[c + 1].first_gt(k1, k2, v)
            if q is not None: cand.append(L2[q])
        if cand: return min(cand)
        c += 1
    return None

random.seed(11)
badD = badN = badF = nD = nN = nF = 0
for t in range(40000):
    n = random.randint(2, 13); p = random.random()
    E = {(i, j) for i in range(n) for j in range(i + 1, n) if random.random() < p}
    adj = [set() for _ in range(n)]
    for a_, b_ in E: adj[a_].add(b_); adj[b_].add(a_)
    o, M, R, r = canon(n, adj)
    pos = {x: i for i, x in enumerate(o)}
    if E:  # deletion
        u, v = random.choice(sorted(E))
        if pos[u] > pos[v]: u, v = v, u
        adj2 = [s | set() for s in adj]; adj2[u].discard(v); adj2[v].discard(u)
        o2 = canon(n, adj2)[0]
        k = pos[v]
        pred = R[k] is not None and (R[k] >= M[k] or (R[k] == M[k] - 1 and r[k] < v))
        truth = next((j for j in range(n) if o2[j] != o[j]), None)
        nD += 1
        if pred != (truth is not None) or (truth is not None and truth != k): badD += 1
    non = [(i, j) for i in range(n) for j in range(i + 1, n) if (i, j) not in E]
    if non:  # insertion
        u, v = random.choice(non)
        adj2 = [s | set() for s in adj]; adj2[u].add(v); adj2[v].add(u)
        o2, M2, _, _ = canon(n, adj2)
        truth = next((j for j in range(n) if o2[j] != o[j]), None)
        nF += 1
        if probe(n, adj, o, M, u, v) != truth: badF += 1
        if truth is None:
            nN += 1
            lv = max(pos[u], pos[v])
            diff = [j for j in range(n) if M2[j] != M[j]]
            if o2 != o or diff != [lv] or M2[lv] != M[lv] + 1: badN += 1
print(f"(D) deletions {nD}, runner-up criterion wrong: {badD}")
print(f"(F) insertions {nF}, located first break wrong: {badF}")
print(f"(N) no-break insertions {nN}, w/M change claim wrong: {badN}")

# (R) runner-up drift under no-break deletions
random.seed(5); cnt = changed = 0; ex = None
for t in range(20000):
    n = random.randint(3, 9); p = random.random()
    E = sorted({(i, j) for i in range(n) for j in range(i + 1, n) if random.random() < p})
    if not E: continue
    adj = [set() for _ in range(n)]
    for a, b in E: adj[a].add(b); adj[b].add(a)
    o, M, R, r = canon(n, adj)
    u, v = random.choice(E)
    adj2 = [s | set() for s in adj]; adj2[u].discard(v); adj2[v].discard(u)
    o2, M2, R2, r2 = canon(n, adj2)
    if o2 != o: continue
    cnt += 1
    if (R2, r2) != (R, r):
        changed += 1
        if ex is None or len(E) < len(ex[1]): ex = (n, E, (u, v), R, r, R2, r2)
print("no-break deletions", cnt, "runner-up data changed", changed, "example", ex)
