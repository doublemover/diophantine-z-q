module
public import VaryingPointAffineChartCover318
public import VaryingAllPointIdealSeparation318
public section
noncomputable section
namespace VaryingAllPointLocalFreeIdeals318
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
open VaryingPointAffineChartCover318
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
variable (x : VaryingParameterPoint318.Point R A ι S) (i : index R A ι S x)
local notation "T" => ring R A ι S x i
local notation "f" => coefficient R A ι S x i
/-- Actual full-ideal localization on every member of the ENTIRE cover
is free of the intended rank. This proves local freeness of arbitrary
parameter points rather than adding it as a premise or range definition. -/
lemma free_extended_ideal : Nonempty (Module.Basis ι T ((T ⊗[R] A) ⧸
    Ideal.map (VaryingNormalizedIdealBaseChange318.sourceMap R A S T f).toRingHom
      (VaryingParameterPointIdeal318.ideal R A ι S x))) := by
  have h := VaryingPointChartFreeness318.free R A ι T
    (VaryingParameterPoint318.map R A ι S T f x) (word R A ι S x i)
    (chartMap R A ι S x i) (chart_square R A ι S x i)
  rw [VaryingPointIdealNaturality318.ideal_map] at h
  exact h
@[expose] def localIdeal : VaryingFreeIdealClassifyingMap318.IdealData R A ι T :=
  ⟨Ideal.map (VaryingNormalizedIdealBaseChange318.sourceMap R A S T f).toRingHom
    (VaryingParameterPointIdeal318.ideal R A ι S x),free_extended_ideal R A ι S x i⟩
/-- Local classification recovers the ORIGINAL arbitrary point on every
actual coefficient chart. No global freeness assumption is needed. -/
lemma classify_local : VaryingParameterPoint318.ofIdeal R A ι T (localIdeal R A ι S x i)=
    VaryingParameterPoint318.map R A ι S T f x := by
  apply VaryingAllPointIdealSeparation318.ideal_injective R A ι T
  rw [VaryingClassifiedIdealRecovery318.ideal_ofIdeal,VaryingPointIdealNaturality318.ideal_map]
  rfl
end VaryingAllPointLocalFreeIdeals318
