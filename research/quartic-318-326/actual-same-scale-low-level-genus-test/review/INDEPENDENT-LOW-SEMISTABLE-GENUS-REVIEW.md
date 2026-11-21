# Independent cold review: lower semistable genus trace

Signed: independent mathematical reviewer, 2026-11-21. PASS.
Author packet `joined-semistsable-genus2207-r1`, exact manifest
3927abd5 and proof 6c04dc6a (full digests below). I verified all four
manifest files and replayed the author's adjacent witness/checker
byte-for-byte. No modular trace, numerical selected D, Lean, or
class-group computation was run.

I rederived the square scaling E_*=Eflat^976393, the multiplicative
tangent signs at each prime of the squarefree conductor 205042530,
and the index 630374400. The fixed auxiliary twist -2207 has the
exact four Sel2 basis directions from its 18-minus-14 local system.
The three tangent seeds are primitive on the true omitted-root
conics; the only local negative contributions are infinity, 2 and
2399. At omitted good primes the actual projected triple is primitive
and the smooth tangent has even valuation, so there is no missing
unit Hilbert residue. The ordinary essential pairing is rank 2;
the standard radical rule implies rank zero and 2-primary Sha
C2^2 without assuming Sha finiteness. [Burungale–Tian Theorem A,
exact v1](https://arxiv.org/html/2611.11566v1#S1) then applies to
that even donor (full rational 2-torsion, hence abelian 2-division),
not to the unknown odd trace.

I checked [Cai–Shu–Tian's Heegner conditions (1),(2) and
Theorem 1.1](https://msp.org/ant/2014/8-10/ant-v8-n10-p05-p.pdf#page=4)
on the actual squarefree level. The c=1 level primes 2,3,5,7 split;
11,37,2399 ramify with character values +,-,+ obtained from
the unramified -2207 character, opposite to their Hecke eigenvalues
-,+,-. The quotient by the actual oriented ideal is cyclic,
including the ramified factors; there is no inert level prime.
The two coprime quadratic discriminants give the unramified
relative genus character. The geometric height formula includes
the nonzero factor 2^-3, without an averaging or a loss of
orientation. The product of the split level-shift characters
is +; the product of the three ramified shift characters is -.
The total shift - cancels Fricke - on Eflat, and the constant
cusp translation cancels in the nontrivial weighted sum.
The actual based trace is thus fixed by conjugation and is
anti-invariant in the indicated real quadratic field, giving
the desired rational twist, not the even companion.

Direct residue enumeration gives #Eflat(F13)=16 and #Eflat(F61)=68;
(r/13)=-1, (r/61)=+1 and (-2207/61)=-1. At 61 the inert prime of K'
is principal and splits in its Hilbert class field, yielding a
coherent F61^2 realization of the sum; the rational-twist trace
reduces in F61. A nonzero [4] of the same oriented modular-map sum
would have order 17, impossible for a rational torsion point by
the good 13 count 12 on the target twist. This would prove a
nontorsion point and rank one through Gross–Zagier and the fixed
even factor. No such nonzero finite trace has been established.
The smaller level is not an enumeration-cost claim, and none of
the remaining actual contact-cell conditions follows.

3927abd57fa1a903cc114051a13d258c962fccbf231d1714703f1f8b2de4ab3e  SHA256SUMS
6c04dc6a0bff7e0c82ab3171cd4a8f6a14a937473260fc6fae991961e49fd37c  ONE-RAMIFIED-LEVEL-HEEGNER-DETECTOR-ON-THE-LOWER-BASE.md
02e1fda40cffecf30e66014c0625aea7273252d998c068a61717771664dea0ce  EXACT-LOW-EVEN2207.json
ff4b420cd91f181350919c2252124cb0a26bde21af08566148fb78671c350391  check_low_even2207.py
