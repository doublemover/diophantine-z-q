# Independent review: fixed Frobenius and moving-key Hecke operators

21 November 2026. Independent mathematical review and exact author checksum replay. Both checksum manifests and their paper entries were verified.

| Exact author scope | SHA-256 of manifest | SHA-256 of paper |
|---|---|---|
| Fixed Jacobian Frobenius carrier | `84ee57df8e02ebc9388eafe0dd18567697dfbf841a8551b0baef1fcd48155661` | `0fc02cd52b77ce30044dd3ec6183f5e7cc22f20971405df220859eed7ddbef01` |
| Moving genuine key operator matching | `86fe2cfc6e81100d853158aa82769f09d85177671d3df7c56c4adb110988a754` | `5d8d90690726e30dffcd06a04ba6331feae82e62131f078589503ccaeb5fb706` |

**First scope.** The tame prime-to-673 rigid frame is retained on the two components, so the node lattice is the exact augmentation lattice, not a weighted quotient. Taking characters reverses the norm and pullback in the transpose Picard correspondence; its action on toric characters is the outgoing framed adjacency. On generic two-torsion the two graphs of the good-prime correspondence give arithmetic Frobenius inverse plus the inverse diamond times arithmetic Frobenius. The local lifted toric two-torsion need only be stable under this sum, not under the entire global Galois group. The initial full-frame degree-17 rows have sum 18, so the subsequent modulo-two product really starts in the augmentation kernel and no quotient row is lost. Compare [Ribet, semistable and modular character groups, §§7–8](https://math.berkeley.edu/~ribet/Articles/motives.pdf).

**Second scope.** The two reference classes are different: the Gaussian norm of 9 + 16i is 337 and its two 673-components are nonsquares, whereas the norm of 105 − 32i is 12049 and its components have opposite quadratic characters. Both have the required Gaussian residues at 16 and 3. The actual source cell has five square contact norms but a nonsquare denominator residue. The matched local components are obtained by square inertia changes, which act trivially on the fixed two-torsion field because its tame inertia at 673 has exponent at most two. Off the fixed support the added ray conditions do not alter this fixed field. At the fixed overlap, the two source variables give separate compatible denominator and contact abelian residues. The same exact nonparallel forms then support the joint fixed-class sieve by [Frei–Tinková, Theorem 1.4 and local factor (1.15)](https://arxiv.org/html/2408.17441v3). Thus after the degree-17 augmentation entry the five moving contact factors can match the operator at 337 and the moving denominator factor the operator at 12049.

Neither paper computes the generic Jacobian two-torsion field, either fixed reference operator, the remaining moving helper factors, or an actual final product or mark. This review does not certify a nonzero trace, rational point, rank, or a practical runtime bound. Later fixed-operator computations are separate evidence.

Signed: Independent reviewer, Quartic 318/326.
