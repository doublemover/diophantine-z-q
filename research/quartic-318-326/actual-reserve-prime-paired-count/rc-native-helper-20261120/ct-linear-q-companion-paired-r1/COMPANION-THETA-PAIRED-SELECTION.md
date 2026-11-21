# The same optimized auxiliary set selects both twists of a literal linear-q pole

## Statement and scope

For each actual detector pole from the original linear-q four-Ready
construction (labels 190, 241, 292, separately), let b be its exact rational
pole value. Put β=[17b] and θ=[1−b/17] using positive squarefree integer
representatives. In the established minus/plus Legendre phases
ε=(u/q)=−1/+1, one can choose just **three/four** new type-one helper primes
I_i and **one common** final prime q₀, such that

    n = β q₀ ∏ I_i,     m = nθ,

are positive squarefree, are both 11 modulo 12, and the literal curves
E_d : y²=x(x−d)(x+3d), d=n,m, both have full Sel₂ of size 8 with the
same original mark (β,1), in the (x+3d,x−d) convention. The choice
is *existential*, and both helpers and final q₀ are chosen after θ has
been fixed. It does not assert that any already chosen q₀ works, that
a single n works across different poles, or that either curve has a
rational nontorsion point. No global bound on the number of θ primes,
nor any individual β–θ symbol control, is necessary. If θ=1 then
the two parameter choices are the same and the extra block is empty.

The exact Ready paper is
`independent-review-nov20/original-linear-denominator-prime-route-r1/
LINEAR-GAUSSIAN-PRIMES-TO-ORIGINAL-READY-POLES.md`,
SHA-256 29e5419420d73d1699801548e411527e265378ebd22bde95d7f7653d59fbc3e0.
The fixed first-twist patterns are in
`joined-work-20261120/linear-denominator-prime-small-marked-selmer-r1/
ACTUAL-LINEAR-Q-MARKED-SEL2-WITH-FEWER-AUXILIARIES.md`,
SHA-256 9be6129b… (full donor hash in manifest).
This extends those patterns, not the original six-helper arbitrary-support
scheme and not a fixed historic integer-u branch.

## 1. Literal companion and its needed support

Write b=A/D² in lowest terms, A,D positive and coprime. Ready gives
0<b<17, and b is a nonzero local square of valuations ≥3, ≥1, ≥2 at
2,3,17 respectively. Hence 17² divides A and 17 does not divide D.
Put B=A/17 and C=D²−B>0. Then

    17b = 17² B/D²,    1−b/17 = C/D²,
    gcd(B,C)=gcd(B,D²)=1,    β=sf(B), θ=sf(C).

At 2, square b has even depth ≥4, so 1−b/17 is a unit square (≡1 mod
16); at 3 it is ≡1 mod3, also a unit square. At 17 it is again ≡1 mod17,
also a unit square. The squareclass of 17b at 2 is trivial and at 3 is 17.
Thus β≡17 mod24 and θ≡1 mod24, no 2 or 3 divides either, and 17 does
not divide θ. The exact linear-q β is 17 times the six distinct known
primes q,p₀,…,p₄, each 1 modulo 408; its five contact labels and q are
actual support, not arbitrary masks.

For every r dividing β, C≡D² modulo r is a unit square; consequently
(θ/r)=+1. Symmetrically for every r dividing θ, B≡D² modulo r is a unit
square and (β/r)=+1. This yields exactly the two **product** row
conditions, not all individual (r/s)=+1. The actual native form is
`ActualTwoDescentMutualSymbolRows318.MutualSymbols`.
A fresh helper is also chosen unit square with each θ prime in both
directions. This is extra simultaneous CRT modulus, not an extra
helper. Nothing restricts the θ–θ edges or requires factoring θ to
bound it uniformly. Finding a numerical companion certificate still
requires a numerical θ or a proof of its actual arithmetic data.

## 2. Shared three/four-help state and final q₀ choice

Order β's support as (17,p₀,p₁,p₂,p₃,p₄,q). For ε=+1 take helper
columns (3,5,9,65); for ε=−1 take (3,5,9), with bit 0 at 17.
Each helper is fresh, 1 modulo 24, with designated β bits, mutually
square with the other helpers and square at each θ prime. This is
ordinary CRT+Dirichlet successively; reciprocity supplies the opposite
bit because a helper is 1 modulo 4. Avoid any specified finite set.
A provisional q₀ ≡7 modulo 24 may first be taken with XOR of helper
columns on β and all plus on the helpers; θ bits at this stage may
be arbitrary. The original native prime-choice theorem requires
q₀≡7 modulo 12, not its stronger optional mod24 lift.

Write L for the original row-sum-zero Laplacian with column numerator
and row denominator, λ_r the nonsquare bit (3/r), and let a be the sum
of the two coordinate indicators e₁₇+e_{q₀}. Then ∑a=0 and a·β=1
where β here denotes its indicator vector. In the old block λ is
supported exactly on 17,q₀. The original sharp=L+λ aᵀ, with its q₀ row
and column deleted, has these exact binary-mask rows, least significant
bit first:

    ε=+1: [1921,128,292,512,48,20,1024,3,5,9,65] (rank 11)
    ε=−1: [897,254,346,638,78,106,126,3,5,9]      (rank 10)

This is the sharper needed calculation, not just the earlier full
Sel₂ row rank. The replay also checks Lβ=0 on the entire old support
including q₀: β−β terms cancel against each diagonal, every helper
column has even weight, and q₀ has their XOR.

Adjoin all θ primes to the index, leaving θ coordinates zero in a and
in the mark β. The old off-diagonal entries are unchanged. For each old
β row, its Laplacian diagonal changes by the sum of (θ-support/row)
bits, which is zero by (θ/r)=1. For each helper row, its respective
sum is zero by the chosen CRT. Thus the **entire old deleted sharp
core is preserved** even if individual β–θ symbols are nontrivial.
The β mark also remains in ker L: old rows retain their equations,
new θ rows have zero β sum by (β/r)=1, and q₀'s mark-coordinate is zero
so its diagonal is irrelevant. This does not require q₀'s θ bits to
be fixed, or invoke symmetry on the θ block.

In any block extension of an invertible matrix C, append next off-diagonal
column/row u,v, and set the new diagonal to 1+v C⁻¹u. Its Schur
complement is then 1. Repeat until all θ vertices are included; this
works for arbitrary (including asymmetric) off-diagonal blocks.
For each θ vertex r, changing its symbol (q₀/r) flips exactly its own
diagonal in the deleted sharp core. Retain all old q₀ symbols and
type 7 modulo 12; impose the prescribed θ bits at the same new prime
q₀ by a single CRT+Dirichlet class. All other primes remain literally
unchanged. The old core, the enlarged core, the mark equations and
both product residues now hold for these **same actual primes**.
With a request to retain 7 or 19 modulo 24, impose that compatible
condition in the CRT; no step below needs it. Set either q₀ or any I_i
away from specified bad places, and make q₀ arbitrarily large.

Exact pinned generic native search/realization:
- `ActualTwoDescentSimultaneousCoreChoice318.actual_simultaneous_core_choice`
  on Option (U ⊕ J), where U indexes the seven old β primes and the
  three/four helpers, and J indexes θ. Its hypotheses are the injective
  prime list prime to 12, provisional q₀ of type 7 modulo 12, total
  residue 11, a fixed a and the old invertible sharp restriction.
  Its outputs fix every some prime, retain old sharp core and old
  q₀ directed bits, and give the enlarged invertible core.
- `ActualTwoDescentThetaDiagonal318.actual_theta_diagonal` and
  `ActualTwoDescentQ0PrimeReplacement318.actual_q0_prime_replacement`
  are the exact two underlying witnesses, not a formal matrix edit.
- Apply `ActualTwoDescentFiniteConclusion318.actual_finite_conclusion`
  to both the old list (after q₀ replacement) and full list. Same
  retained β monomial; all hypotheses are proven above.

## 3. Native consequences of the generic finite conclusion

All of these generic consumers accept arbitrary finite U, not the old
`CoreIndex d = BetaIndex d ⊕ Fin d` convention. Apply to U and U ⊕ J:
- `ActualTwoDescentBetaSupportPoints318.actual_beta_support_points`
  takes the exact β kernel equation and supplies β points at support.
- `ActualTwoDescentExceptionalLocalPoints318.actual_two_adic_kummer_point`
  and `actual_three_adic_kummer_point` use β≡17 mod24 and d≡11 mod12.
- `ActualTwoDescentPrimeFamilyAllPlaces318.actual_family_all_places`
  assembles literal real/good/support rows; then
  `ActualTwoDescentAllPlacesExactCardinality318.actual_all_places_card_eight`
  uses mark 0 at q₀ and mark 1 at 17 to give exact card eight.
- `ActualTwoDescentRationalEightClasses318.actual_rational_eight_classes`,
  `ActualTwoDescentActualQuotientControl318.actual_quotient_control`, and
  `ActualTwoDescentMordellWeilControl318.actual_mordell_weil_control`
  give actual rank ≤1 and an actual marked Kummer point if supplied
  infinitude of E_d(Q). This is not a rank lower bound.

These are exact call signatures and a paper assembly, not new hosted
Lean declarations. The prior constructed-paired `RestrictedRC` wrapper
indexes the six-helper case and cannot be silently used on this smaller
index. The unbuilt generic tail `CTSelectedOriginalTwoRankWitness318`
instead accepts same-mark generic conclusions and two literal infinitude
proofs, with no old-helper-count dependence. The original six-helper
construction remains a separate immediately available native-scope route.

## 4. Exact, fixed low-level analytic gate and a false optimistic shortcut

For positive squarefree d≡11 mod12 the parameter E_d is the (−d)-twist
of E_{−1}; translating x=X+1 takes E_{−1} to
Y²=X³+X²−4X−4, Cremona 48a1 / LMFDB 48.a4, with w₂=+1,w₃=−1
and w∞=−1. See [literal curve data](https://www.lmfdb.org/EllipticCurve/Q/data/48.a4).
Its conductor is 48. The fundamental discriminant −d is coprime to
48 and χ_{−d}(3)=+1. Hence w(E_d)=χ_{−d}(−48)=−1 by the coprime
twist-root formula (e.g. [Kriz–Li, §4](https://intlpress.com/site/pub/files/_fulltext/journals/mrl/2019/0026/0004/MRL-2019-0026-0004-a010.pdf)).
Central zero for both actual curves does not need constructing their
large-level symbols. This is not a simple zero statement.

For a chosen auxiliary odd prime p of the established good ordinary,
irreducible type (e.g. p≡5,13,17 mod28, p∤nθ), let Φ be the pinned
primitive odd integral level-48 Manin eigensymbol. With
S_d(r)=Σ_{a mod d} χ_{−d}(a) Φ(r+a/d), the literal companion has

    S_{nθ}(r) = Σ_{c mod θ} χ_θ(c) S_n(r+c/θ).

In fact r+a/n+c/θ enumerates CRT fractions at nθ, with multiplier
χ_{−n}(θ) χ_θ(n)=(n/θ)(θ/n)=1, since θ≡1 mod4. This proves an exact
same-symbol convolution, not a factorization into two nonvanishing
sums. The existing ordinary p² group polynomial P_d(Z) of the pinned
rank criterion uses this d-twisted symbol and central augmentation
zero. For ζ_p primitive, P_d=(Z−1)H_d implies

    v_p Norm(P_d(ζ_p)) = 1 iff P'_d(1) ≠ 0 mod p.

Indeed Norm(ζ_p−1)=p and ζ_p≡1 modulo the prime above p, so the
remaining norm is a unit iff H_d(1) is a p-unit. The established α-unit
and normalizer in the old criterion give the same nonzero p-adic first
digit. Two such digits on the same selected pair suffice via the
rational cyclotomic main conjecture and the p-converse
([Yan–Zhu v4, Theorems 5.2, 5.11](https://arxiv.org/pdf/2412.20078v4)).
No assumption on 2-primary Sha or integral (Im) is made in this route.
A zero digit only rejects this specific first-digit certificate;
higher precision or a different eligible p may still work.

This uses honest modular symbols on level 48 and degree-p evaluation;
there is no need to construct newspace data at 48(nθ)². The call count
for a direct twist-sum replay can still be proportional to nθ p².
Allow preselecting p and avoiding it in both supports when actually
guaranteed (e.g. known θ square unit at p from the selected detector
chart). This is only an eligibility/local simplification, never a
substitute for the arithmetic digit.

The exact control has n=11, θ=601≡1 mod 24·5², m=6611, and p=5.
They have the same Q₅ twist, same a₅=−2, same residual unit root α=3,
and both central zero. The computed first digits are nevertheless
0 and 4. Exact P coefficients are respectively
(−8,16,0,−16,8) and (128,416,0,−416,−128), with norm valuations
3 and 1 (`512000` and `53482618880`). This is a deliberately
nonproduction test, disallowing an inference from matching real/
2/3/5² residue and p-local reduction data to equal digits. It is not
a claim about ranks of the actual selected linear-q instances.

## Replay and residual

```sh
python3 -B verify_paired_sharp_core.py | cmp - EXACT-PAIRED-SHARP-CONTROLS.json
python3 -B ../ct-original-same-pole-odd-cyclotomic-r1/verify_exact_cyclotomic_rank_gate.py \
  --n 11 --theta 601 --p 5 | cmp - TOY-LOCAL-GATE-NOT-ENOUGH.json
```

The first script rederives the old cores and exercises Schur choices
on synthetic appended mod-2 support, not candidate-prime search.
The second uses the frozen old exact symbol donor. No Lean, remote
publication, true selected θ numeral, or nonvanishing is supplied.
The remaining arithmetic input is a positive-rank witness **on both**
literal curves after the shared q₀ selection, or some actual procedure
to find such a pair within allowable helper/q₀ classes. The old
same-fiber detector and alternative lower-model symbols cannot be
substituted for these original twists.
