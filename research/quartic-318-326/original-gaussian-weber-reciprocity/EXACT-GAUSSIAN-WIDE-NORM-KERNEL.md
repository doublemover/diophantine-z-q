# Exact wide norm-one kernel: the cyclotomic abelianization

Let M=16·m with m odd squarefree, R=(ℤ[i]/M)^×, A=R/U₄,
D=2M, and δ(x)=x/bar(x). The wide norm N:A→(ℤ/D)^× is
literal (a²+b²) mod D. Replacing a,b by different lifts preserves
N because M is even. Its image is precisely the units 1 mod 4.

If u∈R has wide norm 1, its reductions at odd primes p∣m have
ordinary norm 1. At 16, the norm condition is 1 modulo 32. The
canonical rotation -i when the real part is even puts u on its
real-odd arm, by a SINGLE choice e∈{1,-i}. In that arm the only
pairs are (±1,0),(±1,8),(±7,4),(±7,12) modulo 16. Put x=1+it
for t=0,2,4,6; δ(x) respectively gives (1,0),(9,4),(1,8),(9,12).
Multiplying x by i negates δ(x); this yields the full eight
possibilities. The native finite core verifies this using the
literal equality (e u)·bar(x)=x, with norm(x) odd. Working only
modulo 16 for the input norm does NOT give this implication:
(7,0) has norm 1 mod16 but 17 mod32, and is not a coboundary
even modulo a global Gaussian unit.

Now use the SAME rotation e in every component, not one e_p per
prime. The odd component of e u still has norm 1. Gaussian
Hilbert 90 in F_p[i], split or inert, supplies x_p:
x_p=1+e u unless e u=-1, otherwise x_p=i.
Unit CRT on the actual (16,∏p) splits supplies a single x with
these residues. Conjugation commutes with every component
reduction, so injectivity gives δ(x)=e u in R. After quotienting
by U₄, [u]=δ([x]), proving ker(N)=im(δ:A→A).
The reverse inclusion is immediate because N is conjugation
invariant. No CFT or analytic estimate enters these finite steps.

For the image, odd coordinate reductions can realize every
n∈F_p^× as a sum of two squares: the (p+1)/2 squares and their
n-translates intersect. At the dyadic component, the finite
literal eight outputs are 1,5,…,29 modulo 32. Independent
scalar/ring CRT realizes every unit 1 mod 4 modulo D.

In the index-two relative Artin presentation G=A⋊⟨j⟩, j the
actual field conjugation, [G,G]=im δ: certainly every δ is a
commutator, and the quotient by that normal image is generated
by abelian A commuting with j, so abelian. Extend N by j↦-1;
since N(A) consists of 1 modulo 4 and -1 isn't in it, the
kernel on G is again exactly im δ and image is all
(ℤ/D)^×. Thus |G^ab|=φ(D) by this direct kernel computation.
It replaces a delicate fixed-unit cardinal comparison.

To identify that character as the actual cyclotomic
restriction still requires only standard reciprocity (no
independent maximal-abelian calculation): the cyclotomic
extension of ℚ(i) to ℚ(μ_D) is a subfield of the full M-ray
field, because on a ray-principal fractional ideal (α)
locally α≡1 mod M and Nα≡1 mod D. At 2 the extra power
comes from Tr(β)=2Re β in N(1+Mβ), valid in the 2-adic
Gaussian integers. The odd exponents are unchanged.
For prime ideals, arithmetic Frobenius then restricts
to the ideal norm; for ordinary complex conjugation it is
-1. Hence the character above is restriction to ℚ(μ_D),
and the kernel calculation proves exactly L^ab=ℚ(μ_D).
The rational conductor is D, since D divisible by 32 and
φ of any proper divisor is strictly smaller here, together
with cyclotomic intersection for arbitrary f.

Scope: exact finite dyadic solver/image source and independent
controls only, no Lean build. Odd H90 and literal unit CRT are
existing source donors. The global topological class-field
existence/Artin law and actual field identification remain
external to Lean, as does Frei–Tinková 1.4.
