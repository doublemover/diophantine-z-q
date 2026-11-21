# Independent review: actual two-class Selmer directions and Cassels tests

Reviewed exact note
653cd0001749a00a9bcbe86a0aeb7bc698079e8df4845aa5fcc4018bd594a8ce
and manifest c8f8ff8ef9274d517e4830f0154eebe40b9bb2c93995c7236423e3dd31f6eb73.
The pilot residues and all 16 candidate tuples replay to
a56ac9e6c497acbffcbdcec1bae57106850bcbf12ac70fc25c998ac0956c9ce7
byte-for-byte.

At any odd p the compact local group has an open formal subgroup
on which multiplication by 2 is bijective. For the finite quotient,
the 2-kernel and 2-cokernel have equal size, so the actual Kummer image
has size four because all four 2-torsion points are rational. This
argument applies at the moving bad p|D as well. There each marked
torsion point gives even parity with a zero in precisely its marked
coordinate, so its exact stripped unit signs determine the unique
candidate at that parity. At p|a the three exact stable geometric
Legendre signs are (+,+,+), so all four A parities pass. At p|b the
signs are (−,+,+), and only 000 and 110 pass. At all B places and
infinity a,b are squares; outside BD the unit image fills all four
unit triples. This derives exactly eight classes within the
pair-supported four-dimensional candidate family, and a dimension
three subspace W. The global torsion image is a separate dimension
two: its three nonidentity rows are nonzero locally at D, and only
T_b could have the same parity on both support pairs as a W row;
its first coordinate contains the nonsquare fixed 2399 factor.
Thus dim Sel₂≥5 and the marked α∈W is not torsion. This neither
bounds rank from below nor asserts nonzero Sha.

I checked the exact omission order in Shukla–Stoll §3.2,
[(3.9)–(3.10)](https://arxiv.org/pdf/2302.01640): for α=(D,b,a)
the original square coordinates are (W,aU,bV). The three projected
conics and all three tangent positions are correct. The rational
tangent points are necessarily affine (their Z=0 equations would
require a, b, or a/b square). At primes outside BD, primitive
coordinates and all-unit diagonal coefficients make every tangent
a nonzero hyperplane. Smooth reduction and the Hasse count avoid
their at most twelve intersection points and the at most four in
Z=0. This makes every ordinary-place Hilbert factor one by choosing
unit tangent evaluations; any overall scalar choices disappear by
global reciprocity. At B and infinity the second arguments are
squares. For v=(a,a,1) and w=(b,b,1), only the four moving marked
support primes contribute, respectively the two products of
(L₀L₁,a) and (L₀L₁,b); alternation with α=u·w controls u=(a,1,a).
The two products are not computed. A negative product would
exclude a rational point; positive products only control W.
The full radical is the image from Sel₄, by
[Fisher §1](https://arxiv.org/pdf/2208.14977), not a rational
point certificate. No point, rank, full Selmer group or Lean
proof is asserted.

Independent reviewer: Vesper (high_review_ci), 2026-11-21 UTC.
