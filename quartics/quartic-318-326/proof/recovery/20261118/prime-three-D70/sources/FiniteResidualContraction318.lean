module
public import PrimeThreeSelectedFirstUResidualCenter318
public import Mathlib.FieldTheory.Finite.Basic
public section
noncomputable section
namespace FiniteResidualContraction318
open OriginalPrimeThreeFirstOrderPoint318 OriginalPrimeThreeCotangentIndependence318
open OriginalPrimeThreeLocalizedCotangent318 PrimeThreeSelectedFirstUResidualCenter318
attribute [local instance] OriginalPrimeThreeFirstURatioChart318.chartAlgebra
attribute [local instance] OriginalPrimeThreeFirstULocalBaseChange318.pointBaseAlgebra
attribute [local instance] OriginalPrimeThreeFirstULocalBaseChange318.chartRightAlgebra

/-- A map to a finite field cannot kill fewer elements than another
field-valued point if it inverts the complement of that point's kernel.
We compare kernels only, not the two maps or their residue automorphisms. -/
theorem ker_eq_of_preserves_nonzero {A F E : Type*} [CommRing A] [Field F]
    [Fintype F] [Field E] (r : A →+* E) (g : A →+* F)
    (h : ∀ x, r x ≠ 0 → g x ≠ 0) : RingHom.ker g = RingHom.ker r := by
  classical
  ext x
  change g x = 0 ↔ r x = 0
  constructor
  · intro hx
    by_contra hr
    exact h x hr hx
  · intro hr
    by_contra hx
    have hn : Fintype.card F - 1 ≠ 0 := (Nat.sub_pos_of_lt (Fintype.one_lt_card : 1 < Fintype.card F)).ne'
    have hgood : r (x ^ (Fintype.card F - 1) - 1) ≠ 0 := by
      simp [map_sub, map_pow, hr, zero_pow hn]
    apply h _ hgood
    rw [map_sub, map_pow, map_one, FiniteField.pow_card_sub_one_eq_one _ hx, sub_self]

/-- Every finite-residue-valued specialization through this literal point
localization contracts to the chosen prime of the arithmetic chart. -/
theorem contraction_point (g : PointRing →+* K) :
    RingHom.ker (g.comp (algebraMap Closure PointRing)) = pointIdeal := by
  letI : Fintype K := Fintype.ofEquiv (ZMod 3 × ZMod 3)
    (QuadraticAlgebra.equivProd (2 : ZMod 3) 0).symm
  apply ker_eq_of_preserves_nonzero normalizedPoint _
  intro x hx
  have hmem : x ∈ pointIdeal.primeCompl := fun h => hx (RingHom.mem_ker.mp h)
  have hunit := IsLocalization.map_units PointRing (⟨x, hmem⟩ : pointIdeal.primeCompl)
  exact (hunit.map g).ne_zero

/-- In particular the actual residual first-U point of the second center
lies over the selected closed point before localizing the arithmetic chart. -/
theorem actual_residual_contraction :
    RingHom.ker ((localResidualPoint.comp (algebraMap PointRing LocalU)).comp
      (algebraMap Closure PointRing)) = pointIdeal :=
  contraction_point _

end FiniteResidualContraction318
