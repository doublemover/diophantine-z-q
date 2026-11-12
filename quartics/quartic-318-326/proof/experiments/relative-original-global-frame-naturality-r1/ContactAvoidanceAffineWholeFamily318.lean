module
public import ContactBoundedAvoidanceAffineCover318
public import ContactLinearOpenChartRange318
public import ContactRelativeLinearOpenChart318
public import OriginalClosedFamilyCoefficient318
public import ClosedImmersionOpenLift318
public section
noncomputable section
namespace ContactAvoidanceAffineWholeFamily318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactProjectiveDegreeData318
open scoped TensorProduct
variable (S : CommRingCat.{0}) [Algebra ℚ S] (c : Fin 4 → ℚˣ) (N : ℕ)
  (D : BoundedDegree S c N) (a : ContactBoundedAvoidanceAffineCover318.index S c N D)
local notation "T" => ContactBoundedAvoidanceAffineCover318.ring S c N D a
local notation "φ" => ContactBoundedAvoidanceAffineCover318.coefficient S c N D a
local notation "j" => ContactBoundedAvoidanceAffineCover318.chart S c N D a
local notation "i" => ContactProjectiveQuotientGluing318.into S c D.val.datum
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
local notation "π" => ContactProjectiveQuotientGluing318.projection S c D.val.datum
local notation "l" => ContactOriginalLinearOpenChart318.linearForm (j.val : ℚ)
local notation "hl" => ContactOriginalLinearOpenChart318.linearForm_homogeneous (j.val : ℚ)
abbrev sourceRing := ContactOriginalLinearOpenChart318.ring c l hl
abbrev family := OriginalClosedFamilyCoefficient318.family (CommRingCat.of ℚ) S T φ p i
abbrev into := OriginalClosedFamilyCoefficient318.into (CommRingCat.of ℚ) S T φ p i
abbrev toFamily := OriginalClosedFamilyCoefficient318.toFamily (CommRingCat.of ℚ) S T φ p i
abbrev projection := OriginalClosedFamilyCoefficient318.projection (CommRingCat.of ℚ) S T φ p i
instance finite : IsFinite (projection S c N D a) := inferInstance
instance flat : Flat (projection S c N D a) := inferInstance
instance presentation : LocallyOfFinitePresentation (projection S c N D a) := inferInstance
lemma cartesian : IsPullback (toFamily S c N D a) (projection S c N D a) π
    (Spec.map (CommRingCat.ofHom φ.toRingHom)) :=
  OriginalClosedFamilyCoefficient318.cartesian (CommRingCat.of ℚ) S T φ p i
/-- The entire local family lies in the selected actual original affine
source chart. This follows from the proved avoidance locus, not a new
hypothesis on a fixed finite/infinity restriction. -/
lemma supported : Set.range (into S c N D a) ⊆
    Set.range (ContactRelativeLinearOpenChart318.into T c l hl) := by
  change Set.range (into S c N D a) ⊆ (ContactRelativeLinearOpenChart318.into T c l hl).opensRange
  rw [RelativeOriginalAffineChart318.range,ContactLinearOpenChartRange318.range]
  rintro _ ⟨z,rfl⟩
  have hz := (FiniteFamilyAvoidanceOpen318.mem_locus π
    (ContactBoundedDivisorAvoidance318.toLine S c N D)
    (ContactBoundedDivisorAvoidance318.sourceOpen N j) _).mp
      (ContactBoundedAvoidanceAffineCover318.in_avoidance S c N D a (projection S c N D a z))
      (toFamily S c N D a z)
      (congrArg (fun f => f z) (cartesian S c N D a).w)
  have he : into S c N D a ≫ pullback.fst p (RelativeOriginalAffineChart318.baseMap (CommRingCat.of ℚ) T) ≫
      ContactProjectiveModel318.modelMap c=
        toFamily S c N D a ≫ ContactBoundedDivisorAvoidance318.toLine S c N D := by
    rw [← RelativeCoefficientChange318.familyMap_original (CommRingCat.of ℚ) S T φ p,
      ← Category.assoc,OriginalClosedFamilyCoefficient318.into_square]
    simp only [ContactBoundedDivisorAvoidance318.toLine,Category.assoc]
  change (into S c N D a ≫ pullback.fst p (RelativeOriginalAffineChart318.baseMap (CommRingCat.of ℚ) T) ≫
    ContactProjectiveModel318.modelMap c) z ∈ _
  rw [he]
  exact hz
/-- Actual closed embedding of the WHOLE finite family in the literal
coefficient tensor affine source. -/
@[expose] def affineInto : family S c N D a ⟶ Spec (CommRingCat.of (T ⊗[ℚ] sourceRing S c N D a)) :=
  IsOpenImmersion.lift (ContactRelativeLinearOpenChart318.into T c l hl)
    (into S c N D a) (supported S c N D a)
instance affine_closed : IsClosedImmersion (affineInto S c N D a) :=
  ClosedImmersionOpenLift318.closed _ _ _
@[reassoc] lemma affine_into : affineInto S c N D a ≫ ContactRelativeLinearOpenChart318.into T c l hl=
    into S c N D a := IsOpenImmersion.lift_fac _ _ _
@[reassoc] lemma affine_projection : affineInto S c N D a ≫
    VaryingSourceCoefficientPullback318.projection ℚ (sourceRing S c N D a) T=
      projection S c N D a := by
  rw [← ContactRelativeLinearOpenChart318.over_test,← Category.assoc,affine_into]
  rfl
end ContactAvoidanceAffineWholeFamily318
