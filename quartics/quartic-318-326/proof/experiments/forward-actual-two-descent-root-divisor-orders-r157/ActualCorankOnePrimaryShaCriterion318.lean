module
public import ActualCorankZeroFinitePrimarySha318
import all ActualFullSelmerCorank318
public section
noncomputable section
namespace ActualCorankOnePrimaryShaCriterion318
open ActualFullSelmerCorank318 ActualCorankZeroFinitePrimarySha318
open ActualFullPrimarySelmerLowCorank318 ActualPontryaginLowCorank318
open ActualTwoDescentActualPrimarySelmer318 ActualTwoDescentActualPrimaryCharacters318
open ActualTwoDescentActualShaPrimary318 ActualTwoDescentDyadicPrueferModel318
open ActualTwoDescentDiscreteSelmerDual318 ActualTwoDescentPontryaginPadicModule318
open ActualTwoDescentPontryaginRationalCharacters318
open ActualTwoDescentFiniteRankPrimarySelmerEquivalence318
open ActualTwoDescentActualShaRankAlternative318 ActualTwoDescentActualShaPrimaryVanishing318
open ActualTwoDescentEllipticModel318 ActualTwoDescentEllipticDoubleQuotient318
open ActualTwoDescentAllPlacesIntersection318

/-- Finiteness of actual full primary Selmer forces its native dual corank
to vanish. The direct primal classification, not a bare finite-dual
alternative, excludes the infinite Pruefer model. -/
theorem actual_corank_zero_of_finite_primary_selmer (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n) ≤ 8)
    (hS : Nat.card (allPlacesImage n hn) = 8)
    [Finite (actualPrimarySelmer n hn)] : actualFullSelmerCorank n hn = 0 := by
  rcases actual_full_primary_classification n hn hf hb hS with ⟨k, ⟨e⟩⟩ | ⟨e⟩
  · letI := actualPontryaginPadicModule n hn
    letI := finite_characters_of_cyclic_model n hn k e
    letI : Finite (Additive (ActualPontryagin n hn)) :=
      Finite.of_equiv (ActualPrimaryCharacters n hn)
        (nativeRationalCharacterEquiv n hn).symm.toEquiv
    change Module.rank ℤ_[2] (Additive (ActualPontryagin n hn)) = 0
    exact rank_zero_of_finite_charZero ℤ_[2] (Additive (ActualPontryagin n hn))
  · have h : Finite (Additive PrueferTwo) :=
      Finite.of_equiv (actualPrimarySelmer n hn) e.toEquiv
    letI : Finite PrueferTwo := h
    letI := actual_pruefer_infinite
    exact (not_finite PrueferTwo).elim

/-- In corank one, finite full 2-primary Sha is equivalent to an infinite
rational-point group. No actual reduced pairing is used or manufactured.
This identifies the still missing arithmetic implication; it does not
prove either side for a particular twist. -/
theorem actual_primary_sha_finite_iff_infinite_points_of_corank_one
    (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n) ≤ 8)
    (hS : Nat.card (allPlacesImage n hn) = 8)
    (h1 : actualFullSelmerCorank n hn = 1) :
    Finite (actualShaPrimary n hn) ↔ Infinite (Point n) := by
  constructor
  · intro hSha
    letI := hSha
    by_cases hfin : Finite (Point n)
    · letI := hfin
      letI : Finite (actualPrimarySelmer n hn) :=
        Finite.of_equiv (Additive (actualShaPrimary n hn))
          (finiteRankPrimarySelmerEquiv n hn).symm.toEquiv
      have h0 := actual_corank_zero_of_finite_primary_selmer n hn hf hb hS
      exact False.elim (one_ne_zero (h1.symm.trans h0))
    · exact not_finite_iff_infinite.mp hfin
  · intro hinf
    have htwo := (actual_sha_one_iff_infinite n hn hf hb hS).mpr hinf
    letI := actual_sha_primary_trivial_of_sha_two_one n hn htwo
    infer_instance

/-- In the corank-one branch, finiteness already forces the entire
2-primary Sha subgroup to vanish, using the actual rank alternative.
No conclusion about other primary parts of Sha is asserted. -/
theorem actual_primary_sha_finite_iff_trivial_of_corank_one
    (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n) ≤ 8)
    (hS : Nat.card (allPlacesImage n hn) = 8)
    (h1 : actualFullSelmerCorank n hn = 1) :
    Finite (actualShaPrimary n hn) ↔ Subsingleton (actualShaPrimary n hn) := by
  constructor
  · intro hSha
    have hinf := (actual_primary_sha_finite_iff_infinite_points_of_corank_one
      n hn hf hb hS h1).mp hSha
    exact actual_sha_primary_trivial_of_sha_two_one n hn
      ((actual_sha_one_iff_infinite n hn hf hb hS).mpr hinf)
  · intro htriv
    letI := htriv
    infer_instance

end ActualCorankOnePrimaryShaCriterion318
