# Restricted rank converse for the original 318/326 quartics

The [Version 13 manuscript](../../../manuscripts/quartic_v13.tex) uses a
rank converse in the **integer-to-witness** direction of the original 318-
and 326-variable constructions. This note maps that dependency, records
the scope of the paper review, and identifies the corresponding Lean
interfaces. It is not a new proof of the converse or a claim that either
quartic already characterizes `ℤ` unconditionally in Lean.

## The exact input to the rank argument

For each of the four original prepared pole coefficients `b`, write
`sf(r)` for the positive squarefree representative of the squareclass
of a positive rational `r`. The retained preparation gives `0 < b < 17`,
a square reduced denominator, and the required local squares and
valuation depths at 2, 3, and 17. Set

```text
β = sf(17b),    θ = sf(1 − b/17).
```

The manuscript also writes the latter squareclass using
`(17b)^2(1 − b/17)`, which does not change it. The simultaneous descent
in Version 13, “Simultaneous realization from the existing restricted
converse” (lines 7787–7889), uses disjoint supports, `β ≡ 17 mod 24`,
`θ ≡ 1 mod 24`, and that each **whole** squarefree product is a local
square at primes of the other. It does not require all the individual
cross Legendre symbols to be positive.

At this pole the descent picks **one** fresh prime tuple. Restricting and
extending that tuple give `n` and `nθ`, both positive, squarefree, and
congruent to 11 modulo 12. Both descents mark the class `(β, 1)` and
give actual 2-Selmer dimension three. The case `θ = 1` is allowed.
Different poles may choose different tuples; within one pole one cannot
replace `nθ` by an independently chosen twist. All four poles still
belong to the same original preparation of the input integer, including
its labels, chart choices, and scale.

For either selected parameter `ℓ`, the actual curve is

```text
E_ℓ : y² = x(x − ℓ)(x + 3ℓ).
```

This is not the fixed CM curve used elsewhere to generate integer
indices. It has full rational 2-torsion and no CM. The finite Kummer
sequence gives `rank E_ℓ(ℚ) + dim Sha(E_ℓ)[2] = 1`. The
[alternating reduced Cassels–Tate pairing for elliptic curves
(Poonen–Stoll, §1 and §6)](https://math.mit.edu/~poonen/papers/sha.pdf)
forces the finite reduced 2-primary part to have even 2-rank. Here that
rank is therefore zero; the possible divisible part is **not** assumed
away. The full discrete `Sel_{2∞}` has `ℤ₂`-corank one on both curves.
This is the input to the restricted converse, not already a proof of
positive Mordell–Weil rank. See Version 13, lines 1157–1193.

## The paper dependency, in logical order

The particular statement used is
`corank_ℤ₂ Sel_{2∞}(E_ℓ/ℚ) = 1 ⇒ ord_{s=1} L(E_ℓ,s) = 1` for one
fixed positive squarefree `ℓ ≡ 11 mod 12`. Constants need not be uniform
as `ℓ` varies. The independently checked scope is the composition along
the retained Version 13 route below: the same curve, marked classes,
integral normalizations, and terminal comparison survive each handoff
under the cited classical inputs and the manuscript's actual bounded
source constructions. This is not independent verification of every
stronger functoriality assertion in the manuscript, nor a replacement
for those source constructions.

1. **Fix the curve and the normalizations first.**
   [Breuil–Conrad–Diamond–Taylor, Theorem A](https://virtualmath1.stanford.edu/~conrad/papers/tswfinal.pdf)
   gives modularity. Use the manuscript's actual pointed map
   `π = α q_f AJ_∞ : X₀(N) → E_ℓ`, Tate lattice and periods.
   [Dokchitser–Dokchitser, Theorem 1.8](https://arxiv.org/pdf/0906.1815v1)
   gives sign −1 from the full corank and the rational 2-isogeny.
   [Bump–Friedberg–Hoffstein](https://wstein.org/papers/bib/bump-friedberg-hoffstein-nonvanishing.pdf)
   supplies a negative reference twist with nonzero central value
   and a positive reference twist with known simple zero. The
   [Gross–Zagier height formula](https://wiki.epfl.ch/waldspurger/documents/gross-zagier.pdf)
   and [Kolyvagin's forward rank-zero and rank-one results](https://archive.mpim-bonn.mpg.de/id/eprint/325/)
   are used here on **known** analytic inputs. Fix the original positive
   integral multiplier `L`, including the cusp and torsion factors,
   before the variable companion and character families.
2. **Prove the bounds for the even source and the rough companion.**
   The fixed-form [Kato Euler-system input](https://www.numdam.org/item/AST_2004__295__117_0/)
   feeds the common integral even scalar, with old local conditions
   and same-period central calibration (E.6–E.11). The stationary
   transfer (F.2–F.3) and
   [Hoffstein–Luo](https://intlpress.com/site/pub/files/_fulltext/journals/mrl/1997/0004/0003/MRL-1997-0004-0003-a012.pdf)
   supply different parts of the argument: transfer gives the
   valuation bound, whereas nonvanishing with bounded prime support
   selects a companion. The retained local and global comparisons
   in (3.5), (4.5), (5.4) and (5.5) use the actual marked class,
   same-supported duality and trace, and uniformly bounded finite
   matrices, not an arbitrary cohomologous replacement. This uses
   [Cai–Chen–Liu, Theorem 2.15](https://archive.ymsc.tsinghua.edu.cn/pacm_download/632/12220-Heegner_points_on_modular_curves.pdf)
   for the old-conductor norm relations and arithmetic duality as in
   [Nekovář, *Selmer complexes*](https://www.numdam.org/item/AST_2006__310__1_0/).
   The [Cai–Shu–Tian height comparison](https://arxiv.org/abs/1408.1733v2)
   then transports the bound to the conductor-one genus point using
   (3.4), with the original period and multiplier conventions.
3. **Establish odd visibility before applying a known-simple bound.**
   In (O.6–O.8), a visible coefficient at an actual finite stage
   first certifies non-torsion of its point; the height comparison
   then gives the known simple zero needed for (F.4–F.6). This is not
   an application of the restricted converse to an unknown index.
   The half-integral-weight construction uses
   [Waldspurger's Shimura correspondence](https://www.imj-prg.fr/wp-content/uploads/2020/prix/waldspurger1983.pdf)
   and [Weil's operator formulas](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/weil2.pdf);
   the original forms and level operators, not just their abstract
   existence, are still required. The empty odd configuration, if
   visible, already settles the base.
4. **Keep one final field and one family.**
   In the nonempty branch choose the final negative complementary
   `k` from its separate even source, with `L(E_ℓ^k,1) ≠ 0`, and
   fix `K = ℚ(√k)`. The actual positive and negative sources produce
   (3.9) at the **same** finite stage and on the **same** labels
   `h_x`. The integral support triangle in (4.7) fixes the comparison
   units in `Λ = ℤ₂[[t]]` before localization. The common correction is
   formed after the inner limit over the completed localization at
   `(2)`, before character evaluation. Only the corrected product is
   specialized at `t=0`, since the correction itself may have a pole.
   Unrelated units in the localized ring would not preserve the central
   valuation. On nonzero addresses, (F.8) gives one upper bound `B`
   independent of the eventual binary dimension.
5. **Compare with the missing address.** At the base the proof uses
   vanishing of the actual specialized Kummer class and corank one,
   not finite `Sha`. The corrected base coordinate must also be
   regular away from the height-one prime `(2)`, as in lines 5382–5385.
   Regularity and vanishing at `t=0` alone do not determine the Laurent
   constant after the inner localization. With the determinant bound `c_det` and the
   window length `L_T(M)` fixed as in Version 13, lines 16434–16454,
   choose `M > B + 2c_det` (also `M > max(c_det,0)`), then
   `b > (L_T(M)+2)(2^M−1)`, then the graph and the finite stage.
   A nonzero address matches the tested rows and loses at most
   `2c_det` in the central comparison. It cannot have both the upper
   bound `B` and the larger valuation forced by base vanishing.
   Sign −1 and the nonzero complementary central value give the
   desired simple zero over `ℚ`.

The [pointwise 2-converse preprint cited by Version 13](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/A-pointwise-2-converse-for-elliptic-curves-with-rational-two-torsion-October-7-2026/paper.pdf)
is source provenance for this approach; it is not a Lean dependency
and is not used here in place of the selected-curve comparison.

## A shorter exit when only an actual rational point is needed

For the quartic witness it suffices to prove that `E_ℓ(ℚ)` is infinite.
The retained argument can hand off its same original Heegner point,
rather than prove analytic rank one and then invoke a second rank
conversion at the unknown base:

- In the empty branch, the nonzero finite residue in (O.7) at `D=1`
  already shows that the original conductor-one `P₁` is non-torsion.
  The genus character at `D=1` is trivial; this is the full class
  trace. Version 13 already makes `LP₁` rational.
- In the nonempty branch use the same unweighted conductor-one
  `P_{K,1}` at `h₀=1`. In the zero-base argument (lines 4515–4561),
  the implication from derivative vanishing is used to obtain torsion
  of this point, then the vanishing of the retained specialized class
  by (4.5). Starting with **torsion of this very point** instead gives
  the same base zero and the same (F.8) contradiction. This proves the
  same point is non-torsion. It does not remove the upstream uses of
  the height formula or forward rank on known twists.

For the fixed level orientation, the orbit in
[Gross–Zagier, Ch. I §3 and Ch. II §1](https://wiki.epfl.ch/waldspurger/documents/gross-zagier.pdf#page=12)
is the actual cyclic isogeny `ℂ/𝔞 → ℂ/(𝔞𝔫⁻¹)` over the Hilbert class
field, with the chosen `𝔫` supported at the oriented split primes
of the true `N`. This is not determined by a pair of singular
`j`-invariants alone. The trace is unaveraged. Complex conjugation
reverses the orientation; comparison with full Fricke permutes the
whole class orbit. Since `π` is pointed at infinity and has Fricke
eigenvalue +1, the trace satisfies
`c(P) = P + h_K π(w_N∞)`, where `h_K` is the actual class number.
The original `L` kills the cusp term; one must not discard it
merely because `π(∞)=0`. Thus `LP` is rational and non-torsion.
This argument does not reindex nontrivial weighted genus sums.

Do this separately on `E_n` and `E_{nθ}` from one pole's actual tuple.
A non-torsion point here is a **rank witness**, not necessarily the
representative of `(β,1)`. The 2-Selmer count and rational 2-torsion
force `Sha[2]=0` once there is positive rank. The marked descent
then extracts rational points in the required squareclass on those
same two curves, and the original scaling turns these into the two
point rows for that pole.

## Lean handoff and remaining work

| Repository interface | What it provides, and what it still needs |
| --- | --- |
| `ActualTwoDescentOriginalAllPlacesCardinality318.actual_simultaneous_all_places_eight`; `ActualTwoDescentActualSelmerCardinality318.actual_selmer_eight` | The same-prime paired local count and its link to actual cohomological `Sel₂`. If consuming an already selected tuple, use `ActualTwoDescentAllPlacesExactCardinality318.actual_all_places_card_eight` on its marked data; do not reselect primes. |
| `ActualTwoDescentPontryaginFreeRankOne318.actual_native_pontryagin_free_rank_one` | Produces the literal `ℤ₂`-linear free-rank-one Pontryagin dual from the actual count, quotient bounds and `ActualReducedDuality`. Constructing the actual reduced Cassels–Tate pairing is a separate formal input. |
| `OriginalRCTerminalAddress318.exists_nonzero_matching_signRows`; `OriginalRCTerminalWindow318.central_strict_loss`; `OriginalRCTerminalCertificate318.central_base_ne_zero_of_original_bounds` | Finite address and loss arithmetic for supplied rows. They do not construct the uniformly retained Heegner/dual determinant modules, the actual analytic families, their Laurent rows, or the non-torsion point. |
| `ActualSelectedPointedFrickeCusp318.pointed_fricke_translation`; `ActualSelectedIndexedFrickeTrace318.trace_killed_translates` | Algebraic consumers for the pointed Fricke relation and indexed trace. They do not construct the actual moduli point, its Artin orbit, or the map `π`. For the direct exit these and the arithmetic non-torsion source must meet at the **same** geometric trace. |
| `ActualTwoDescentMordellWeilControl318`; `ActualTwoDescentPointExtraction318.actual_realization_of_kummer`; `TwoTwistPointRealization318.Realization.certificate` | The marked-point and scaling side, for the actual two rational groups. It needs their rank witnesses, not an unmarked rational example on a different twist. |

The table names source interfaces, not a blanket kernel-check verdict
for every experiment. The principal formal rank obligation is still
a supplier on the **actual selected curves**: consume the full corank
witness and produce `Infinite (Point (ℓ : ℚ))`, either through the
restricted analytic converse plus the forward theorem, or by producing
the same non-torsion trace and its rational descent. Neither supplied
finite terminal rows nor a bare assertion about an L-value is that
supplier. Native construction of the genuine common prime-pattern
preparation for all integers is a separate forward obligation.

The exact polynomial bridges
[`Current318FinalBridge.polynomial_zero_iff_source`](../proof/318/Current318FinalBridge.lean)
and [`Current326Final.table_zero_iff_source`](../proof/progress/Current326Final.lean)
identify the published polynomial zeros with their source equations.
They do not fill these arithmetic premises or the separate
zero-to-integer direction. See [arithmetic derivations](arithmetic.md)
and [formalization obligations](../proof/components/arithmetic-obligations.md).
