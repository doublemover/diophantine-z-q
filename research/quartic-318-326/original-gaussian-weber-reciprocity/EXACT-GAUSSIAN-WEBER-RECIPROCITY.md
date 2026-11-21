# CFT-free construction of the exact Gaussian Artin field for the linear-q route

**Scope.** On paper, construct the field, the actual signed Artin tags,
and the exact wide-norm cyclotomic character needed for the original
linear-q application of Frei–Tinková. This construction uses classical
elliptic-curve theorems but neither global class field theory nor a
prime-distribution theorem in Gaussian progressions. None of the new
elliptic-curve/number-field input is asserted Lean-green.

## The theorem, on the actual modulus

Set K=ℚ(i), O=ℤ[i], and
E/K : y²=x³−x. For an integer N divisible by 6 let

    T_N = K(E[N]),   L_N = K(x(P)² : P∈E[N], P≠O_E),
    U_N=(O/NO)^×,   A_N=U_N/image(O^×).

Use the arithmetic Frobenius convention: its residue action over a
prime of norm q is the q-th power. For every such N:

* L_N/ℚ is finite Galois, and the O-linear torsion action gives
  Gal(L_N/K) ≅ A_N. For every Gaussian prime ideal 𝔭 coprime to N,
  with any generator π, the arithmetic Frobenius in L_N/K maps to
  the class of π mod N. Consequently the exact Artin rule on
  all coprime ideals agrees with the full N-ray quotient.
* Rational complex conjugation acts on this A_N by a↦bar(a), and
  gives the outside branch. There are exactly two cosets; the
  calculation of the old rational class size now applies to this
  *actual* Galois group.
* When N=M=16·m with m odd squarefree and 3∣m, as in the actual
  fixed base plus fresh-prime carrier, let D=2M. Then
  L_M^ab=ℚ(μ_D), with least rational conductor D. On the relative
  subgroup, restriction to this field is the literal unit-valued
  wide norm a↦a·bar(a) evaluated modulo D, using **any lift**
  from U_M to U_D. On complex conjugation it is −1.
  Thus the exact representative at each shifted norm remains the
  same literal finite tag used in the already staged class coefficient.

The 6-divisibility condition is stronger than needed but is automatic
on the original base (16 and 51 divide it). It means every prime
factor ever used below is above a rational p>3, including all factors
of representatives used to prove surjectivity.

## 1. Faithful quotient, not the CM main theorem

Write j=[i] for (x,y)↦(−x,iy), extending to the origin. It is an
O_E-preserving automorphism, j²=[−1], and the regular invariant
differential ω=dx/(2y) satisfies j^*ω=iω. In particular,
a+bi↦[a]+[b]j defines the O-action used throughout.

**An algebraic rank-one basis, no uniformization.** Over any
characteristic under consideration, the dual of j is j⁻¹=−j, duality
is additive, and [a+bi][a−bi]=[a²+b²]. The scalar is nonzero for a
nonzero Gaussian integer, so [a+bi] is a nonzero isogeny and has
degree a²+b². In characteristic zero it is separable. Factor N in O
and for each exact Gaussian prime power π^e select Tπ in ker[π^e]
outside ker[π^(e−1)], possible since the two kernel cardinalities are
N(π)^e and N(π)^(e−1). Use ker[1]={O_E} also when e=1.

The annihilator of Tπ as an O-module element contains (π^e); since
O is a PID every such ideal is (π^j) for 0≤j≤e. No j<e is possible,
as it would kill Tπ by [π^(e−1)]. Hence evaluation t↦[t]Tπ from
O/(π^e) into ker[π^e] is injective and, by the equal cardinalities,
bijective. On E[N], the CRT idempotent for π^e maps to ker[π^e],
since π^e times that idempotent is 0 modulo N. Conversely it is
the identity on ker[π^e] because its residue is 1 modulo π^e.
All other idempotents vanish there. The sum T=ΣπTπ therefore
gives a single rank-one generator E[N]≃O/NO, and T,jT genuinely
form a basis over ℤ/N. All torsion points are algebraic because
[N] is finite, so its finite geometric kernel lies in E(bar K).

As all O-actions commute with Gal(bar K/K), the faithful action on
T_N embeds Gal(T_N/K) into U_N. For any two affine points, equality
of x² implies Q∈{P,−P,jP,−jP}: factor x_Q²−x_P²; if x_Q=x_P,
the two possible y's differ by sign, and if x_Q=−x_P, the equation
gives y_Q=±i y_P. This also tolerates exceptional y=0 (though the
chosen O/NO-generator has order N>2). The four automorphisms
preserve all x². Evaluate at one O/NO-generator to conclude
that Gal(T_N/L_N) is exactly the preimage of the global-unit
image, not a conjectured full group of four automorphisms of T_N.
Therefore Gal(L_N/K) embeds into A_N.

Separately, the set of all torsion Weber values is stable under
Gal(bar ℚ/ℚ), since E and x² are defined over ℚ, and the adjunction
of i is stable too. Thus L_N/ℚ is finite normal and separable.
Actual complex conjugation restricts nontrivially on K, has order
two, and conjugates the O-action [a] to [bar(a)]. It conjugates a
relative scalar a to bar(a), even if its action on a particular
chosen generator is not itself the naive conjugation of that
generator. This gives exactly the two-coset Presentation.

Classical input: [Silverman, *The Arithmetic of Elliptic Curves*](https://www.pdmi.ras.ru/~lowdimma/BSD/Silverman-Arithmetic_of_EC.pdf),
III.4 for separable isogenies and kernel cardinality, III.5 for
invariant differentials, III.6 for dual-isogeny algebra, and III.10.1
for origin-preserving automorphisms. The PID/CRT construction and
Weber fibre arguments here are direct. No theorem requiring N coprime
to 2 or 3 is invoked, and complex uniformization is unnecessary.

## 2. Local arithmetic Frobenius at the same Gaussian ideal

The model E has discriminant 64, hence good reduction at every
odd rational p. If p does not divide N, all N-torsion reduces
isomorphically to the geometric N-torsion of the smooth special fibre
and inertia acts trivially. For example use the prime-to-p reduction
injection and equality of the two N² cardinalities; inertia acts
trivially on the residue field. Frobenius actions then agree by
equivariance of reduction. Equivalently, the prime-to-p torsion of
the smooth integral model is finite étale. This proves unramifiedness
rather than assuming it for the new fields. Work over the residue
field of the chosen Gaussian prime 𝔭.

**Split p.** The Gaussian contraction 𝔭 with norm p determines
the generator π=a+bi up to the four global units. The same
endomorphism [π]=[a]+[b]j is defined on the integral smooth model:
the group law and j extend, with the latter on the explicit equation.
On the reduction, its differential is multiplication by the residue
a+bi=0 at *this* ideal. Its degree is p. One direct proof in the
special fibre uses duality: the dual of j is j⁻¹=−j, duality is
additive, and the dual of [π] is [bar π]. Their product equals
[p], which is a nonzero morphism of degree p² even in characteristic
p. Thus deg[π]=p, and the vanishing differential makes it purely
inseparable. Over the split residue field F_p, factor through the
relative p-Frobenius E→E^(p)=E; the remaining morphism is a degree-one
origin-preserving automorphism of the reduced E. In characteristic
p>3 the exact automorphism group over the algebraic closure is μ4
(j-invariant 1728); it is precisely the reductions of ±1,±j,
and in this split case all four are already defined over the
residue field. Therefore

    [π] = ε ∘ Fr_p                  for ε ∈ {±1,±j}.

The equalities on reduced N-torsion lift through the injective
reduction map, and quotienting by the global units removes ε.
The arithmetic Frobenius class is therefore [π], not its inverse
and not the class of the conjugated Gaussian generator unless it
is that other ideal which was selected. No chosen CM Hecke-character
normalization is necessary.

**Inert p.** Here 𝔭=(p), with residue field F_{p²}. Over F_p,
the quadratic character χ extended by χ(0)=0 satisfies
χ(−1)=−1. Substitution x↦−x cancels the sum of
χ(x³−x), including x=0, hence #E(F_p)=p+1. The characteristic
relation Fr_p²−[a_p] Fr_p+[p]=0 therefore gives
Fr_{p²}=−[p] on E, and after quotienting by μ4 it is the class
of the same Gaussian generator p of 𝔭. No imaginary quadratic
class theorem was used on this branch.

Classical input: [Silverman, *AEC*](https://www.pdmi.ras.ru/~lowdimma/BSD/Silverman-Arithmetic_of_EC.pdf)
VII.3.1 and VII.4.1 for reduction and unramifiedness;
III.5 for invariant differentials, III.6.2 for dual isogenies
and degrees, II.2.11 for inseparable Frobenius factorization,
III.10.1 for the exact char>3 automorphisms, and V.2.3 for
the trace and Frobenius characteristic relation. The explicit
differential argument fixes the split-prime sign without a
character or prime-distribution theorem.

## 3. Surjectivity by factorization; no circular use of distribution

Given any specific unit u∈U_N, choose any integral representative
α of this same class, using quotient surjectivity. Since its class is
a unit, there exists β with αβ≡1 mod N, so no Gaussian prime ideal
dividing (N) can divide (α). In particular α≠0, and no factors above
2 or 3 occur since 6∣N. Factor α in the Gaussian UFD:
α=ε∏π_j (repetitions allowed, empty product for a global unit).
Each π_j gives a genuine arithmetic Frobenius in L_N/K by §2;
their product maps to u modulo global units. This proves every
class in A_N is attained by an AUTOMORPHISM, not that every
class must contain one prime at this stage. No Dirichlet, Chebotarev,
FT, or use of the eventual desired simultaneous pattern is involved.
This identifies the finite quotient isomorphism used to label the
actual fields. The ideal class normal form is exact because O is a
PID, so the ambiguity in generators is only membership in O^×.

For a selected *rational* Frobenius whose absolute class lies in
this relative subgroup, restriction to K is the identity. The
prime of K under the same prime of L_N has residue degree one,
and arithmetic tower compatibility identifies this very absolute
Frobenius with the above relative one. On ring integers,
R=O_{L_N}, the rational invariants are exactly ℤ (they are the
rational algebraic integers). Thus the prime over p and the
Gaussian principal generator computed in the old native ideal
reduction are literally the ones used here, not another prime
picked independently. This is the external proof of the narrowly
stated IdealReciprocity, giving finite ideal Frobenius equality
rather than a fabricated positive Gaussian witness.

## 4. Cyclotomic character, including the extra dyadic bit

Apply §§1–3 at N=M and N=D=2M. Natural restriction on
Gal(L_D/K) corresponds to reduction A_D→A_M: restricting the
actual torsion scalar from E[D] to E[M]=[2]E[D] does exactly this.
For the Weil pairing at D, choose the basis P,jP of the underlying
free (ℤ/D)-module. Its pairing is primitive. The matrix for a+bi
has columns (a,b),(-b,a); equivariance and alternation give its
cyclotomic action ζ_D↦ζ_D^(a²+b²). A global unit has determinant
one. Thus the absolute-Weber field L_D already contains ℚ(μ_D):
the subgroup fixing all x² acts trivially on that primitive root.

Any class in ker(A_D→A_M) has a representative congruent to a
global unit mod M; divide by that SAME global unit to write
α≡1 mod M. If α=1+M(a+bi) in integral coordinates, then

    N(α)=1+2Ma+M²(a²+b²)≡1 mod 2M,

because M is even. Arbitrary lifts give the same value by the
same identity for differences. Therefore the entire kernel fixes
μ_D, giving **ℚ(μ_D) ⊂ L_M**, not just μ_M. The character
on the relative subgroup of L_M is the earlier literal
wideClassNorm. This step only uses equivariance of Weil pairing
([Silverman, *AEC*, III.8.1](https://www.pdmi.ras.ru/~lowdimma/BSD/Silverman-Arithmetic_of_EC.pdf))
and quotient reduction; no local/global Artin norm-map theorem
or analytic prime theorem is used. Actual complex conjugation has
character −1 and, independently, semilinear determinant −1.

By the earlier finite wide-norm commutator calculation for
M=16 times odd squarefree, the kernel of wideClassNorm on A_M
is exactly {a/bar(a):a∈A_M}; its image is the D-units congruent
to 1 mod 4. Adjoining the complex conjugation character −1
gives full unit image, and the kernel on the absolute group
is exactly the commutator. Therefore the displayed cyclotomic
subfield is precisely the maximal abelian subextension. Its
least conductor is D: if contained in ℚ(μ_f), intersect the
two cyclotomic fields to get ℚ(μ_g) with g=gcd(D,f). Every
proper divisor g of D has smaller φ, since 32∣D and the odd
part is squarefree; thus g=D. In particular every rational
prime dividing D ramifies (at the dyadic place D has full
2^5 factor), so the exact FT weight can send p∣D to none with
no mismatch of ramified versus unramified masks.

## 5. Exact analytic and native boundaries

The actual chosen Weber field therefore supplies the Gaussian
field inputs of the fixed-field adapter on paper: presentation,
relative arithmetic Frobenius, and its wide-norm cyclotomic
restriction. There is no extra hypothesis of suitable ray
characters or a larger compositum with a guessed conductor.
The same fixed auxiliary field at each selected m is used for
all merged affine positions; the previously reviewed application of
[Frei–Tinková, Thm. 1.4](https://arxiv.org/html/2408.17441v3#S1.SS2)
is still the genuine remaining analytic theorem, outside Lean.
This is not evidence for any elliptic rank, B(Sha), or final quartic
claim.

For native development, the deepest ports left here are the algebraic
torsion rank-one argument via this E’s separable isogeny kernel degrees; good-reduction
prime-to-p torsion and arithmetic reduction comparison; degree
and inseparability factorization for this E; and Weil pairing with
explicit Galois-equivariant determinant descent. The smallest
clean independent native consequences are the literal Weber fibre
(x² equality iff a single global unit), factorization-to-surjectivity
and the conductor-doubling principal transition. These do not
prove those omitted geometry theorems. The Python control checks
the exact local point actions, not an assertion about abstract
torsion fields or a large prime search.
