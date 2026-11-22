#!/usr/bin/env python3
"""Tiny exact support-only audit; no integral embeddings or CM paths."""
import json
from math import gcd, prod

D = -311
F = 241
EXCEPTIONAL = {2, 3, 5, 7, 29, F, abs(D)}

def factor(n):
    assert n > 0
    ans = {}
    p = 2
    while p * p <= n:
        k = 0
        while n % p == 0:
            n //= p
            k += 1
        if k:
            ans[p] = k
        p = 3 if p == 2 else p + 2
    if n > 1:
        ans[n] = 1
    return ans

def symbol(a, p):
    assert p > 2
    v = pow(a % p, (p - 1) // 2, p)
    assert v in (0, 1, p - 1)
    return -1 if v == p - 1 else v

def support(M, g0, y):
    x, g = 2 * y, M * g0
    DA = -20 * g0**2
    assert x % 16 == 0
    S, m = 5 * abs(D) * g**2 - y**2, M**2 * D * DA - x * x
    assert m == 4 * S > 0
    d = gcd(g, abs(y))
    g0p, y0p = g // d, abs(y) // d
    S0 = 5 * abs(D) * g0p**2 - y0p**2
    assert S == d * d * S0
    # Factor both forms *separately* in the audit, test cached reconstruction.
    fs, f0, fd = factor(S), factor(S0), factor(d)
    assert fs == {p: f0.get(p, 0) + 2 * fd.get(p, 0) for p in f0.keys() | fd.keys()}
    assert prod(p**e for p, e in fs.items()) == S
    odd_inert = tuple(p for p, e in fs.items() if p not in (2, 5) and e % 2 and symbol(-5, p) == -1)
    assert len(odd_inert) % 2 == 1
    out = dict(scale=M, auxiliary_g=g0, g=g, x=x, y=y, m=m, S=S, factors=list(fs.items()),
               normalized_gcd=d, normalized=[g0p, y0p], normalized_S=S0, odd_inert=odd_inert)
    if len(odd_inert) != 1:
        return dict(out, result="not_a_ramified_prime_and_infinity_algebra")
    p, = odd_inert
    if p in EXCEPTIONAL:
        return dict(out, result="already_exceptional", p=p)
    assert symbol(D, p) == -1
    assert fs[p] == f0[p]
    t5, t6, tf = (symbol(a, p) for a in (5, 6, F))
    ti = symbol(F * D, p)
    assert ti == -tf
    splits = [s for s in (1, 5, 6, 30) if symbol(s * F * D, p) == 1]
    assert splits == [s for s, v in zip((1, 5, 6, 30), (1, t5, t6, t5*t6)) if v*ti == 1]
    assert len(splits) == (2 if (t5, t6) != (1, 1) else (4 if ti == 1 else 0))
    tag = "full_anti_ideal_zero" if (t5, t6, ti) == (1, 1, -1) else "keep_marked_tests"
    assert (not splits) == (tag == "full_anti_ideal_zero")
    return dict(out, result=tag, p=p, symbols_5_6_241=[t5, t6, tf], paired_Ms=splits, depth=(fs[p]+1)//2)

def main():
    assert D % 8 == 1 and symbol(D, 5) == 1 and symbol(-5, 29) == 1
    choices = [support(F, 4, y) for y in (8, 32, 16, 56, 512)]
    assert choices[0]["odd_inert"] == (11, 17, 199)
    assert (choices[1]["result"], choices[1]["p"]) == ("full_anti_ideal_zero", 1115011)
    assert (choices[2]["paired_Ms"], choices[2]["p"]) == ([1, 5], 4300759)
    assert all(c["p"] == 19 and c["paired_Ms"] == [1, 5, 6, 30] for c in choices[-2:])
    c3, c5 = support(F, 12, 168), support(5 * F, 4, 280)
    assert c3["normalized"] == c5["normalized"] == choices[3]["normalized"]
    assert c3["S"] == 9 * choices[3]["S"] and c5["S"] == 25 * choices[3]["S"]
    assert choices[3]["depth"] == c3["depth"] == c5["depth"] == 1
    assert dict(c3["factors"])[3] == dict(choices[3]["factors"])[3] + 2
    assert dict(c5["factors"])[5] == 2
    # One scale, one prefix, inclusive y=0 and 127 positive magnitude controls.
    from collections import Counter
    census = Counter(support(F, 4, 8*k)["result"] for k in range(128))
    print(json.dumps(dict(D=D, exceptional=sorted(EXCEPTIONAL), examples=choices,
                          reuse=[c3, c5], prefix={"n": 128, "census": dict(census)}),
                     sort_keys=True, indent=2))

if __name__ == "__main__":
    main()
