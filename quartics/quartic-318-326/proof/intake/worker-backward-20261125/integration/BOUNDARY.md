# Actual closed-fibre intersections and adjunction on the original π model

Status: source-only. Nothing compiled, fetched, installed, or written to a repository.
First leaf `OriginalUpperActualFibreComponents318` is a guarded zero-stock replay
candidate using three official exact direct stock roots (15 sidecars);
its `replay.sh` defaults to hash-only preflight. Existing strict R15 fraction
identification is used only later. No compiler grant requested.

## Same model and actual carriers

Let (r:X\longrightarrow Y) be the proper minimal regular semistable
resolution of the actual finite R8 normalization for the same continued
proof-field factor. The composite (h:\,X\to\mathbf P^1_{mathcal O_K})
is literally the original (π=1728/j) projection, with its reciprocal (χ).
Use (s:X\to\operatorname{Spec}mathcal O_K), and any actual nongeneric
point (p), not a chosen split trait. No input changes the whole retained
section (P) from the prior R8 path. Construction of the actual semistable
model remains external in Lean (Javanpeykar 4.3.2, or Signed's exact model
driver if independently completed).

- `ActualFibreComponents`: for each vertex E of the old literal graph,
  form the *reduced induced closed subscheme of the actual fibre* using
  `IdealSheafData.vanishingIdeal`. It has the genuine residue structural arrow.
  The embedded component's kernel on X is the vanishing ideal
  of the closure of the image of its specific generic point. In any
  affine open meeting this closure the kernel is the actual generic prime.
  `idealAt_from_affine` proves that the literal germ extends it to the prime
  in the ordinary (\operatorname{Spec}\mathcal O_{X,x}) over that exact
  generic point.
- `ActualFibreIntersectionScheme`: the scheme of the sum of the two
  ideal sheaves is Cartesian and canonically sits on the actual fibre
  components. Never replace the sum by its radical. This retains all
  multiplicity and tells exactly what (E\times_X F) means.
- `ActualFibreIncidence`: for distinct E and F the actual ambient
  meeting set is finite, from sobriety and the impossibility of a
  strict chain of three generizations on an integral surface of
  coheight at most two. The argument also proves the particular
  generic point of each branch is height one wherever the two meet.
- `ActualFibreCrossingIdeal`: (mathcal O_{X,x}/(\mathfrak p_E+
  \mathfrak p_F)) is the literal uncompleted local crossing quotient,
  with both actual primes read through the strict R15 same-stalk
  construction. The quotient has Krull dimension zero and is nonzero;
  its maximal-radical statement works even if the residue chart is not
  split. Its length is 1 when the actual thin-node ideal comparison
  gives (\mathfrak p_E+\mathfrak p_F=\mathfrak m_x).
  Optional `ActualCrossingFiniteLength` gives finite length in general
  for the ordinary Noetherian stalk using Hopkins–Levitzki. Only
  `HopkinsLevitzki` and its direct missing `Noetherian.Nilpotent` are
  visibly absent from that stock cut; no fetch was attempted. The thin
  route does not need them. Neither length route uses a complete ring.
- `ActualFibreIntersectionLength`: the exact degree of a distinct
  intersection is the integer weighted sum of those local lengths:
  (\sum_x [\kappa(x):\kappa(p)]\ell(\mathcal O_{X,x}/(\mathfrak p_E+
  \mathfrak p_F))). The residue algebra is the true `s.residueFieldMap`,
  with equality (s(x)=p) derived from the literal fibre. It is not an
  arbitrary residue weight. The remaining finite-residue fact is applied
  to the exact closed point of a finite-type (\kappa(p))-curve (on
  an affine, residue is its finite-type quotient by the actual maximal
  ideal and Zariski's lemma). No split or degree-one claim. These exact
  off-diagonal integers give `offdiagonal` and `positive_at_meeting`.
- `ActualReducedComponentFibre`: actual reducedness of the one
  scheme-theoretic fibre implies its embedded kernel equals the
  intersection of all actual component ideals, also affirmatively on
  the same affine. This is stronger than an equality of closed supports.
- `ActualComponentConormal`: for the actual height-one prime ideal
  of E at x, a primitive nonzerodivisor equation gives the *true* module
  (I_E/I_E^2) over the quotient, its normal dual with the inverse
  transition (u^{-1}) when (f'=uf), and the ordinary exact Koszul
  multiplication resolution. This uses the given actual Cartier equation,
  not an unexplained canonical degree or a different field.

## Exact degree, principal-row and adjunction derivation (classical)

Work on the actual localized proper regular model (X_A) over
(A=(mathcal O_K)_p). If (q) is a uniformizer, (X_k=mathrm{div}(q))
is an effective Cartier divisor. Reducedness makes every generic
valuation of (q) along E exactly one, so (\sum_E E=mathrm{div}(q))
as Cartier divisors (using regularity and usual Cartier–Weil comparison).
The actual global ideal-sheaf intersection above verifies the reduced
support scheme, and the ordinary (q)-valuation read is the existing
strict `OriginalUpperOldAmbientVerticalUniformizer318` construction
when specialized to this same localized model.

Let `deg_k` be Euler-characteristic degree on the genuine proper
component E. Define (I(E,F)=\deg_k\mathcal O_X(F)|_E).
The diagonal is literally the degree of the normal dual from the
primitive `ActualComponentConormal` construction, not an artificial
negative sum. If (E\ne F), restriction of the Cartier inclusion is
nonzero on the integral E (F's generic differs), and its cokernel is the
actual (mathcal O_{E\times_X F}). Thus the elementary sequence
(0\to\mathcal O_E\to\mathcal O_X(F)|_E\to
\mathcal O_{E\times_X F}\otimes\mathcal O_X(F)|_E\to0)
computes the degree as the actual weighted local-length sum. The twist
does not change each finite local length. See
[Stacks 55.9.6–7](https://stacks.math.columbia.edu/tag/0C5Y) and
[Stacks 33.44](https://stacks.math.columbia.edu/tag/0AYQ).
Since the line of the principal divisor (\mathrm{div}(q)) is trivial
(with nonvanishing frame (1/q) before restriction), the sum of this
actual row is zero. Do not restrict the vanishing section (q) and
call it a trivialization. With effective horizontal part D_hor its
restriction contributes a nonnegative degree by the same length
sequence whenever (D_hor) meets E, as the generic points differ.
This gives the exact principal and horizontal predicates and the
actual intersection_formula for (D=h^*B-\mathrm{div}_\omega(dπ)).

For the canonical row, put (i:E\hookrightarrow X_A), (j:\operatorname{Spec}
k\hookrightarrow\operatorname{Spec}A), (\omega=\omega_{X_A/A}).
Proper Gorenstein relative duality gives (s^!A=\omega[1]) with the
actual smooth Ω and node-frame comparison. The strict **old local**
nodal log pieces can support this comparison; no represented global
dualizing theorem is being inferred from them.
Apply the same rank-one Koszul calculation to (i) and (j) and
compose right adjoints for the exact common map (E\to\operatorname{Spec}A).
Since E is a regular immersion of codimension one, even when E itself
has a self-node, it is Gorenstein over k, and the calculation is
[
  i^*\omega\otimes N_{E/X_A}
    \simeq \omega_{E/k}\otimes_k (\mathfrak m_A/\mathfrak m_A^2)^\vee .
]
The constant one-dimensional base-cotangent dual has degree zero
(choose q only to trivialize this base factor). The two shifts ([1])
and ([-1]) cancel on both sides. The real local computations in
`ComponentConormal` give exactly the units of the normal factor
in this equation. The identification with the represented functor is
still a geometric input in Lean. References:
[Stacks 48.15.6, Koszul right adjoint](https://stacks.math.columbia.edu/tag/0BQV),
[Stacks 109.19, relative dualizing sheaf](https://stacks.math.columbia.edu/tag/0E6N),
and [Stacks 53.5.2, RR for proper Gorenstein curves](https://stacks.math.columbia.edu/tag/0B5B).

Let (k_E=H^0(E,mathcal O_E)), (f=[k_E:k]) and
(g=\dim_{k_E}H^1(E,mathcal O_E)). Riemann–Roch and the literal
adjunction line give (\deg_k(i^*\omega)=f(2g-2)-I(E,E)).
Thus no appeal to a mistaken genus-zero-implies-P¹ argument in a
possibly nonsplit or self-nodal model: if this degree is negative,
connected reduced fibre and a noncontracted anchor make (I(E,E)<0)
and the only possible pair is (g=0, I(E,E)/f=-1). The **degree-one
conormal** over (k_E) then yields P¹ and the actual normal degree −1
([Stacks 55.11.5](https://stacks.math.columbia.edu/tag/0CA6)). This is a
first-kind exceptional curve and its contraction descends the same
normalization map ([Stacks 54.16.1](https://stacks.math.columbia.edu/tag/0C2I)),
contradicting this resolution's relative minimality. For a component
contracted by the original h, `h*O(B)|_E` has degree zero since it is
pulled back from one point; the *section* can still vanish there.
This proves that the exact `D·E` is nonpositive on the contracted
components. The existing direct-negativity block can then consume this
geometry without ample-line construction.

## Remaining native boundary

Not supplied by Lean yet: actual model existence/regularity independently,
proper coherent Euler-characteristic degree and its tensor additivity,
the represented global right-adjoint/dualizing functor and exact Cartier
transitivity, and the global geometry connecting those definitions.
The pinned tree has ideal-sheaf data, actual scheme kernels, and local
module length, but not represented arithmetic intersection/Picard
degree or scheme-duality modules. These are not replaced by integer
records. Signed's actual same-model window/round and thin-node geometry
remain distinct. No new proof or certificate for the complete 318/326
endpoint is claimed; this packet goes upstream of the existing strict
same-P χ²/finite Γ row.
