# Independent review: the 416 marked optimal-embedding labels

Reviewer: Vesper, independent quartic review lane. 2026-11-20. Scope: exact paper and finite replay at m = 455, d = 323, p = 53 and residue modulus 13.

## Exact objects reviewed

| Object | SHA-256 |
|---|---|
| SIGNED-OPTIMAL-EMBEDDINGS-ON-THE-416-MARKED-ORDERS.md | a432a3e5129388d418c1ea9e98668d0b36cabd5145649413b2ebfc330cbaef5b |
| replay_direct_signed_embeddings.py | f251717fa4b5ea4058342e80dbf7aa1d5f066a7df0a4d190fd809038315cfde9 |
| EXACT-DIRECT-OPTIMAL-EMBEDDING-REPLAY-323.json | 916c2ed758039b8ab63a4b7113b6074197cbc08e0e35be0b547df40eaef3caf3 |
| ACTUAL-ODD2544-MARKED-ORDERS-Q29.json | aa650e289ef886c824cf93414845c9586c12e5db0d640f6a6d48452ca9bb1a8e |
| ACTUAL-FULL-TRACE-F53.json | 8d172729d64384eb192e718573a317e691f7f0862a291eacc4248aea22550a64 |

## Accepted within scope

- The [oriented correspondence of Cornut–Jetchev, Corollary 3.2 and §3.6 Remark 1](https://webusers.imj-prg.fr/~christophe.cornut/papers/liftings.pdf) retains the actual residue-field isomorphism at 53. The conjugate-pair statement of Corollary 4.1 by itself does not distinguish the two signs. The selected eigenlines at 16 and 3 fix the corresponding split level components. “Maximal split” at 2 and 3 in the reviewed note refers to the local CM order, not the ambient Eichler order.
- At each conductor prime the primitive trace-zero vector gives a nonzero nilpotent. In a basis with a generator of its kernel as first vector, the local determinant changes by the square of the second coordinate as the probe vector varies. Conjugating by a basis change multiplies it by the determinant of that change, so its Legendre sign transforms by the determinant character. I separately tested 3,348 nonzero probe instances over the two residue fields 17 and 19. The rational reduced norm disappears under the global idele character; the fixed q29 transport contributes sign +1 at this discriminant. The note correctly does not assume that transport sign at arbitrary d.
- I ran the exact checker against both hash-pinned donors and compared stdout byte-for-byte with the frozen JSON. The five maximal-order counts per orientation are 446, 1325, 1325, 1328 and 1336, totaling 5,760; each genus half has 2,880 with multiplicity. Only residue orientation +8 without a half swap matches both complete marked-address counters from the independent Gauss/isogeny replay. Both signs happen to give period 11 modulo 13, so agreement of a single residue would not have sufficed.

This is an independent bounded read of the earlier finite result. It does not compute a production conductor, shorten the direct enumeration in the moving prime, or yield a signed mass formula from the unsigned one. No Lean compilation or remote action was used for this review.

Signed: Vesper, independent quartic review.
