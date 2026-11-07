# Simultaneous prime-pattern and order-separation audit

## Scope and result

This is a fresh mathematical read of the actual proof in the pinned `quartic_v10.tex`, not an inference from historical PASS receipts. The checked checkout is `e96c25a48a09034a52c3444cdd515c09720cd19d`. The consuming 318-source completeness construction is in `COMPLETENESS-ASSEMBLY.md`.

**Current result:** no concrete mathematical error was found in the prime-pattern argument in this pass. Its elementary order-separation and CRT consequences are now independently proved and partly kernel checked. The full analytic prime-existence argument is not a Lean theorem, nor has every published input been freshly retrieved and independently proved. Consequently this audit does not change the formal source-arithmetic boundary or assert an unconditional kernel-checked 318 theorem.

This pass read the source argument from its simultaneous-primes theorem through its final order of limits, including the Gaussian nilsequence bridge, rather than replacing the argument by a conjectural general Artin-prime-pattern statement. The manuscript explicitly proves only its fixed Gaussian-ray-field special case. Frei–Tinková is methodological background, not an assumed theorem.

## 1. Exact prime-pattern contract consumed by completeness

After merging repeated contact forms and clearing fixed rational denominators, the forms are `p_j = u + c_j w²`, with distinct fixed integer coefficients. The required congruence factor `q` is absorbed into the coefficients before applying the theorem, so the output parameter satisfies `q | w`. The theorem allows arbitrarily large `u/w²` and an arbitrary finite prime cutoff.

Each selected prime has a generator π in `Z[i]` satisfying:

- π = 9 modulo 16;
- π = 1+3i modulo 7;
- π = i modulo an arbitrary fixed odd squarefree avoidance modulus M, coprime to 7.

Writing `d₋ = N(π−1)` and `d₊ = N(π+1)`, the theorem excludes every odd common divisor between the two orders at one position and between all orders at distinct positions. It gives `v₂(d₋)=6`, `v₂(d₊)=2`, and `gcd(d₋(π_i),d₊(π_j))=4` for all i,j.

The CM/reduction identification is in `lem:v5-two-reductions`, source lines 11138–11165. The two reductions over the primes of Q(√2) have opposite square classes of the curve parameter because `(7/p)=-1`; they are the two quadratic twists of the j=1728 model. The Gaussian Frobenius norm formulas give the two orders as the unordered pair `N(π±1)`. The rational two-torsion and the ray parity distinguish the required labeling. This is not an arbitrary-curve assertion.

## 2. Local sieve and large-prime tail

Source labels: `lem:v5-local-counts`, `lem:v5-medium-sieve`, `lem:v5-large-sieve`, `prop:v5-obstruction-tail`; approximately lines 16543–16921.

The cross-position representation lies on the five-variable quadric

`a²+b²−c²−d²−κw² = 0`,

where κ is a fixed nonzero coefficient difference. Away from the fixed bad primes, the quadric is nondegenerate and has `ℓ⁴−1` nonzero residue points. Simultaneously forcing two neighboring Gaussian norms to vanish costs two dimensions, including the inert-prime degeneration. The ordinary prime sieve has dimension k; its local first-order fluctuation contains the nonprincipal character modulo 4 and has bounded cumulative effect.

The application of Browning–Loughran Theorem 4.1 was checked against the author manuscript and a page image: its dimension hypothesis is **n ≥ 5**, not n > 5. An OCR rendering of the inequality must not be treated as a defect. The present rank-five quadratic form is within scope. The congruence modulus excludes the discriminant and 2, and the residue set excludes the zero vector as the theorem requires.

For large common divisors the source changes coordinates to

`x₀x₁ = κw² − xz`.

The cases with a common divisor of both x₀,x₁ and the zero right-hand side are removed first. In either remaining chart, fixing a nonzero t leaves an injective parametrization by the other three coordinates. The two sieve polynomials are coprime, including the exceptional chart t=−2. Their contents acquire no relevant common prime after the invertible lattice substitution.

The rank-three lattice cover uses the squarefree good-prime part q of t. The lattice determinants are q², their number is at most `9^ω(q)q`, and their large-third-minimum tail is of order `9^ω(q)q³/T³`. The squarefree-radical fiber of t has only `O(B^ε)` members by Rankin's bound. Choosing the successive-minimum cutoff `T=B^(3/4)` gives the stated power saving after summing. I checked these exponent calculations and the separate zero cases.

The resulting weighted obstruction tail has shape

`C τ N^(3/2)/(L log L) + O_τ(N^(3/2−1/800))`.

The coefficient C does not depend on τ or L; only the power-saving remainder may depend on τ. This quantifier distinction is essential for the later fixed-L argument.

## 3. Fixed Gaussian ray-field analytic bridge

Source labels include `lem:ga-hecke-sw`, the Gaussian norm-transfer, Type-I/II extraction and recombination lemmas, `prop:gf-factorization`, and `cor:ga-fixed-centered-nilsequence`; approximately lines 16921–18377.

### Progression main term

A rational prime in the conjugation-invariant Gaussian ray set has exactly two degree-one prime ideals counted by the ideal weight. Prime powers and higher residue degree contribute an elementary square-root error. Finite ray characters reduce the progression calculation to a fixed Gaussian Hecke character times a rational Dirichlet character composed with norm.

The source's Hecke Siegel–Walfisz deduction keeps the number field and ray modulus fixed. The varying modulus has norm at most a fixed constant times q², with q logarithmically bounded. The principal-character indicator is interpreted on the primitive inducing character, so imprimitive excluded Euler factors do not silently alter the main term. The extension to every endpoint `1 ≤ Y ≤ X` is split at √X; below that point a trivial ideal count suffices.

I checked the deduction printed in the manuscript against its retained Mitsui audit and explicit unsmoothing calculation. A fresh direct retrieval of the Mitsui publisher PDF was unsuccessful in this pass, so this is not being described as a new page-by-page verification of that parent source. The earlier audit records the actual published PDF hash and page images. Kane's historically corrected proposition is not the source currently used here.

### Norm pullback, bilinear reduction, and factorization

The Gaussian norm transfer works with residue classes of lattice points and quadratic polynomial pullbacks to one-parameter nilsequences. Its quantitative contradiction uses a horizontal character and triangular coefficient extrapolation. I checked the treatment of even residue steps, the bounded-index lattice decomposition, and the range of the equidistribution parameter.

The Type-I/II reductions preserve the progression restrictions. The bilinear argument first fixes a positive-density row, then uses recurrence in the remaining dilation variable; it does not assume that each individual dilation remains equidistributed. Published Green–Tao Lemma 4.5 allows a short arc with arbitrary center, as needed for the Type-II differences. The coefficient and Cauchy–Schwarz losses are incorporated in a positive power of the initial equidistribution parameter.

The later factorization stage is not circular in its parameter choices: the rational-conjugation loss is fixed independently of the factorization exponent, that exponent is then selected, and only afterward is the stronger progression saving chosen. Affine pullback includes the rational coefficients created by replacing `g(n)` with an orbit interpolating `g(Wn+b)`.

**Boundary:** these are substantive analytic derivations read and checked for the stated applications. They have not been formalized here. This audit establishes neither a general varying-field estimate nor a general theorem on polynomial patterns with arbitrary Artin conditions.

## 4. Ordinary-prime transference and polynomial count

Source `subsec:gaussian-gowers-bridge` and `prop:v5-artin-patterns`, lines 18377–18924.

The auxiliary cutoff z for the inverse-theorem step is separate from the eventual polynomial W-trick cutoff v. The refined modulus is fixed before applying each centered nilsequence estimate. The diagonal chooses a sufficiently large cutoff first to control majorant errors, then a sufficiently large physical size, with all relevant residues and inverse-theorem tolerances included. No uniform estimate over varying ray fields is assumed.

Dodos–Kanellopoulos v4 Theorem 5.1 was directly checked. It requires majorant norm U^(2s) for target U^s, and the manuscript uses that exponent, including the full cyclic cube. The centered function is real and dominated by the ordinary prime weight. Truncation of a short initial interval is negligible by the elementary cube support count. The final typeset DK statement was not freshly compared.

I directly checked the published Tao–Ziegler statements used here: Theorem 9, Theorem 11, Corollary 3, Theorem 13, Theorem 15, and the parameter hierarchy immediately preceding Theorem 11. The manuscript uses the arbitrary-function model, with its simultaneous global/local approximation. It explicitly rescales the bounded model before invoking the bounded concatenation theorem. For the quadratic patterns the resulting local step polynomials have degree one; the source's enlarged coefficient parameter and smaller sieve exponent cover those coefficients. The required global Gowers interval and step ranges match the recorded inequalities.

The local-cube computation is handled by fixed-system linear replacement, ordinary-prime linear correlations, and a partition into wrap regions. Distinct cube vertices have nonproportional gradients. Primes dividing a large step q contribute only a total `O(1/log v)` correction since all its prime factors outside W exceed v.

For output boundaries, the source uses a weighted second moment of the ordinary majorant rather than the false bound obtained by multiplying strip cardinality by a power of log N. It separates the possible constant-shift factor and uses independent parameter copies for the square. Fixed-width strips are controlled first, then their relative widths tend to zero after the large-size limit. Negative coefficients are covered by an enlarged ambient period and zero weight for nonpositive outputs.

## 5. Ray-fiber lower bound and the final diagonal

Source `lem:v5-ray-fibres`, `prop:v5-cutoff-lower`, `subsec:v5-diagonal`, lines 18924–19110.

The unit quotient in the Gaussian ray group is dealt with at the fixed base modulus, which contains 16. Adding a new prime ℓ therefore introduces the full residue-unit group, not another quotient by four units. Its norm kernel is contained in the commutator subgroup, as witnessed by `z/conj(z)`. The residual abelian information is exactly cyclotomic. Disjointness from the base ray field follows from disjoint ramification sets, and the degree computation verifies the entire fixed field, not merely an inclusion.

At each fixed nonzero norm there are at most four forbidden residues from the adjacent norm conditions. Thus every compatible abelian fiber retains the required proportion. The denominator from the growing ray-field degree cancels fiberwise. This yields a singular-series lower bound `c(log L)^(−4k)`, with c independent of L. I independently checked this cancellation; replacing it by a generic Chebotarev density would be insufficient.

Choose L once so that the obstruction coefficient `C/(L log L)` is smaller than a fixed fraction of this lower bound. Only then fix the enlarged ray field and run its polynomial asymptotic. The slowly decreasing τ is stagewise constant. At each stage, enlarge the size threshold to control the τ-dependent error. This is compatible with `T=floor(τ√N)`, `T=o(√N)`, and the lower-range function from the polynomial theorem.

The finite ray restrictions remove all smaller forbidden primes from each individual adjacent norm. The remaining two-adic valuations follow directly by writing π's real part as `9+16A` and its imaginary part as `16B`.

## 6. Independently completed order separation

Source `v9:lem:separation`, lines 19639–19660, is required by the final source even though its primary exponent is 3 rather than the older exponent 19.

The diagonal may also enforce

`τ(N) N^(1/6)/(log N)^k → ∞`.

For every fixed positive τ this is eventually true, so adding its threshold to each stage is legitimate. The strip `w<N^(1/3)` has weighted count at most `O(N^(4/3)(log N)^k)`, negligible against `NT`. The already positive weighted count after obstruction removal therefore survives outside this strip.

For a survivor, `w² ≥ N^(2/3)` and `w²=o(N)`. Consequently all selected primes are asymptotic to u, while distinct primes differ by at least a fixed positive multiple of `N^(2/3)`. Hasse's bound places an opposite group order within `O(√N)` of its own prime. A positive multiple of another selected prime, below twice that prime, must equal it. Off the diagonal equality contradicts spacing; on the diagonal it contradicts evenness of the order and oddness of the prime.

This argument's finite arithmetic core is now proved in `OrderSeparation.lean`. It needs no explicit description of the Gaussian generator once the Hasse bound, size bound, and spacing have been supplied.

## 7. New kernel-checked CRT completion

`PrimeCRTAssembly.lean` supplies four additional theorems:

1. Individual prime nondivisibility passes to coprimality of the product of selected primes with the lcm of reduced opposite orders. The reduced order need only divide the full order; in the application it is d₊/4.
2. From the exact prime-pattern coprimalities, `gcd(M₋,L)=16`, and `16 | h₀`, the three congruences
   `h=0 mod Π^e M₋`, `h=1 mod M₊`, `h=h₀ mod L`
   are jointly soluble for every natural e.
3. Their solutions are arbitrarily large. This separates the arithmetic progression claim from the additional real-orbit density theorem, which is not asserted by the Lean result.
4. The factor 64 in the chosen index and continuity modulus kills the real component of R0 even when the component order was measured using P=2R0. Keeping h congruent to h0 therefore preserves the component of the coherent square-root charts.

The proofs use the generalized Chinese remainder theorem for the shared factor 16 and a second coprime CRT. They do not incorrectly demand pairwise coprimality of all three moduli. Set e=3 for the current source; its stronger `64 | h₀` implies the required 16-divisibility.

Both new Lean files compile with Lean 4.35.0 in the existing component environment. Their printed axiom sets contain only `propext`, `Classical.choice`, and `Quot.sound`. Logs are `order-separation-check.log` and `crt-assembly-check.log`.

## 8. What remains unclosed

- Global PP: the full analytic proof is present in the pinned manuscript and has been substantively read in this pass, with several direct parent-source checks and no new defect found. It is not fully independently formalized or reduced to an existing machine-checked library theorem.
- Global RC: the converse worker has independently verified the simultaneous-two-twist matrix argument and the explicit prep-zero witness map, conditional on the restricted converse plus the forward rank theorem. It explicitly reports that the entire restricted converse arithmetic/coefficient/height producer chain is not closed by this fresh pass. No concrete counterexample or error has been established there.
- Source assembly: the remainder is the explicit conditional all-row construction in `COMPLETENESS-ASSEMBLY.md`, the kernel-checked actual detector-chain lemma, and the source-bound finite regression/coverage certificates. Those certificates are not substitutes for PP or RC.

Thus the strongest justified combined statement here remains a source-specific completeness proof conditional on the explicitly identified global arithmetic inputs, with new unconditional local/finite sublemmas. Neither a green finite certificate nor this audit alone warrants declaring the full 318 iff theorem proved.

## Directly consulted external texts

- [Green–Tao, quantitative polynomial equidistribution, published Annals PDF](https://annals.math.princeton.edu/wp-content/uploads/annals-v175-n2-p02-p.pdf), especially Lemma 4.5.
- [Browning–Loughran, author manuscript](https://arxiv.org/pdf/1705.01999), Theorem 4.1; inequality visually checked on PDF page 17.
- [Browning–Heath-Brown, author manuscript](https://arxiv.org/pdf/2003.09593), Lemmas 2.1 and 4.1.
- [Tao–Ziegler, published polynomial-pattern paper](https://doi.org/10.1017/fmp.2017.3), Theorems 9, 11, 13, 15 and Corollary 3, with their surrounding size hypotheses.
- [Dodos–Kanellopoulos, v4 author manuscript](https://arxiv.org/pdf/1610.00487v4), Theorem 5.1.
- [Mitsui publisher record](https://doi.org/10.4099/jjm1924.26.0_1): fresh PDF retrieval did not succeed; the precise existing source comparison and unsmoothing derivation were read locally instead.
