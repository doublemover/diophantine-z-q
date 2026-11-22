# Independent review: the actual point-divisor law and anchored Abel fibre

**Verdict: PASS, classical proofs only.** Verified these exact author
papers, their manifests and the cited strict native source bytes:

- Point-divisor law, `POINT-DIVISOR-LAW.md` SHA-256
  `14a7aaa24322cea1a3860bf457c459592e2ee51788e3716c4571a097d4bc0990`;
  author manifest `99ed3d66e14913eb27430a54ea7f64e97b4e397e3d56e5aa94a1ae12cc4d409f`.
- Anchored fibre calculation, `PROOF-PLAN.md` SHA-256
  `061d2ea061fdd0ace234c24fbbcf51a4396c9ba91745d4778e632fee598ba018`;
  author manifest `efec78c1a92cc3d2858124e76d518370e2b1dc00a8839a37a9a398e6dcb1cf1e`.

The first proof invokes [Milne's Abel theorem, §18.4](https://www.jmilne.org/math/CourseNotes/AV.pdf#page=78)
on the same filled compact normalization. The required equality is in
the full integral homology period lattice of the same exponential.
A zero class supplies a single integral cycle for all holomorphic
forms, for any point-path choices. The retained saturation proof is
independent of this invocation of Abel. Meromorphic moments over all
actual monic sheets extend through branch values and infinity, are
rational on the base, and recover the unique original field element
by the ordinary transpose Vandermonde trace matrix. That readback does
not use GAGA. The smooth local order and canonical Cartier section
comparisons remain classical inputs. The multiplier with divisor E−D
maps the positive line O(E) to O(D).

The second proof uses that same divisor-line class at one reduced
regular tuple. A second effective divisor would give a pencil in the
same line. A simple root outside its support moves by a local
holomorphic inverse; the other roots remain simple in disjoint disks.
The degree counts the entire divisor. Thus a distinct nearby tuple
would have the same Abel value, contradicting local injectivity.
A repeated tuple coordinate is nonregular by the antisymmetric
tangent test. Properness of the same algebraic map and its one
analytic full-rank patch supply surjectivity; the full fibre over
each specified good value consists of the g! orderings.

This retains the same pointed map, actual algebraic/analytic filled
comparison, and the classical inputs above. The proof is not native
Lean, a prescribed arithmetic center's noncriticality, the exceptional
image nullness, a volume identity, or a height theorem. It invokes
neither Riemann–Roch nor Jacobi inversion.

**Signed:** Independent quartic reviewer, 2026-11-22 UTC.
