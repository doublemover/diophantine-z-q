# Independent cold review: the same selected surface as a literal modular quotient

**Verdict:** PASS at the paper/application boundary. This is not a native Lean
result. Reviewed exact author bundle manifest
484c18d0062af62cafc1db65d39fcdb0c6ba6f07e5f5447208f1126a6a820ac0,
and SAME-A-QUOTIENT-OF-THE-LITERAL-COMPACT.md
4cac387b859665b71025a06087019434733c41c0a8878fbedf86d4bfeacafaff.

1. **Same counterexample, same form.** The residue field F of one genuine
   fine-fibre mark on the literal rational counterexample has degree at most
   576. No normal closure or height-evaluation field is substituted for F.
   The full compatible geometric endomorphism algebra of the non-CM surface
   is the specified division B_210. The actual marked Atkin–Lehner isogenies
   therefore give the building-block condition, not just equality of
   unmarked isogeny classes. The [Guitart–Molina marked comparison](https://arxiv.org/pdf/0906.2559#page=4),
   [Guitart Theorem 3.3](https://arxiv.org/pdf/1102.0863#page=10), and
   [Guitart–Quer Proposition 2.3](https://doi.org/10.4153/CJM-2012-040-2)
   concern that same block and produce one primitive form before twisting.

   Projective comparison at 3 and 7 uses the same form and conjugation by
   one common normal comparison subgroup. The division valuation's
   order-two quotient and residue-unit quotients give 8 and 16, with
   pro-auxiliary kernel. Use 7 only to test residue characteristic 3.
   Off S it is the actual good unramified marked lift that removes all
   projective inertia. One common finite unit-CRT twist cancels all scalar
   inertia there, and the odd scalar wild parts on S. At 2 the determinant
   has inertia image of order at most two after taking the square root on
   the procyclic subgroup of units, so the scalar wild kernel is at most
   four and the full wild group at most 32. For a faithful finite inertia
   quotient of ramification index e, the different bound gives
   d/e <= 1-1/e+v_2(e); the upper-numbering wild integrand is at least 1/2
   up to the last nonzero break. Hence last break <= 10, Swan <= 20,
   and conductor exponent <= 22. With the same-form conductor donor this
   yields n | M, not a numerical comparison of n and M. Zero monodromy
   uses potential good reduction of the actual surface: a nonzero
   semistable torus character module would have rational dimension 1 or 2,
   impossible for a unital B_210-module.

2. **Exact determinant, not up to a quadratic sign.** At split 11 the
   rational Tate space is W plus W using defined-over-F QM matrix units.
   For every finite K/F Faltings gives semisimplicity and commutant
   M_2(Q_11), so W has scalar commutant over K. The commutation equations
   come from a finite-dimensional matrix span, so the conclusion and
   semisimplicity persist over the algebraic closure of Q_11. Thus W stays
   absolutely irreducible on every such subgroup. A nonzero polarization
   block is perfect by irreducibility, and transpose is +1 or -1 on its
   one-dimensional space. In the symmetric case its two distinct
   geometric isotropic lines would be fixed over an open subgroup,
   contradicting that irreducibility. The block is alternating, so
   det W is exactly the cyclotomic character in the stated covariant
   convention.

   Restrict the actual newform constituent to a finite normal-over-F
   comparison field. Schur and conjugation extend the comparison to
   rho_g=lambda W on G_F. Dividing the two determinants gives exactly
   lambda^2=epsilon. Its finite cyclic kernel field E contains F_epsilon
   and has degree at most two over F_epsilon, which is contained in
   F(zeta_n). In particular [E:Q] <= 1152 |im epsilon| <= 1152 phi(n).
   The nonzero map of the two full Tate modules over E descends from
   coefficient scalars by a Q_11-linear functional on a nonzero entry:
   equivariance is a system with Q_11 coefficients. Faltings Hom then
   gives a genuine map over E, onto the same geometrically simple A.
   Neither normality of F/Q nor adjoining a newform coefficient field is
   required in this degree estimate.

3. **Actual source Jacobian, over Q before extension.** The 113bc488
   comparison refers to the full original primitive signed ordinary open.
   The affine classifier identifies the canonical d=y^2 twist with the
   actual universal pointed short model and glues the normalized x/c
   invariant; it is not a comparison of geometric points alone. The
   [Conrad fine ordinary moduli theorem](https://math.stanford.edu/~conrad/papers/kmpaper.pdf#page=35)
   at M>=5 applies to this rational chart. Thus uniqueness of the normal
   proper completion over the same j gives the over-Q identification
   with the classical curve, not a twist inferred from a complex
   isomorphism. On the actual dense ordinary open, multiplication by
   M/n sends a primitive M-mark to a point of exact order n and commutes
   with the one simultaneous sign. The rational map extends, by
   properness and the DVRs of the normal source, and is finite since j
   is nonconstant. The identity norm composed with pullback equals
   multiplication by its positive degree on the target Jacobian proves
   norm surjectivity. Composing the rational newform quotient and the
   E-map above therefore gives an actual surjection from the literal
   compact's Jacobian to the selected A_E. Its connected-kernel quotient
   is over E, but no bound on the degree of its induced isogeny to A
   follows from this construction.

The nine predecessor hashes were checked against their exact source bytes:
fine fibre 86f5a70d, block application a37a6dba, global projective 098f0d3d,
one twist 85604541, older field dc4441d6, rational compact 113bc488, scalar
lift 04303810, separation d46da580, and strict cut ccf78f07. The rational
compact comparison and degree-free j=1 separation need no separate
complex-model/genus identification for this quotient. They do not build
the all-place stable Hodge/Petersson bound, the same-A directional height,
the numerical isogeny comparison, the CM source, or the final reverse
theorem. The PEL, automorphy, Tate, and moduli results remain named
classical inputs. No Lean build was run.

Signed: independent proof review, 2026-11-21 UTC.
