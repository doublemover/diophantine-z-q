module
public import ContactBoundedDivisorAvoidance318
public import ContactLinearOpenChartRange318
public import FiniteFamilyAvoidanceUniversal318
public section
noncomputable section
namespace ContactBoundedAvoidanceFamily318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactProjectiveDegreeData318
variable (S : CommRingCat.{0}) [Algebra ℚ S] (c : Fin 4 → ℚˣ) (N : ℕ)
  (D : BoundedDegree S c N) (j : Fin (N+1))
local notation "Z" => ContactProjectiveQuotientGluing318.family S c D.val.datum
local notation "p" => ContactProjectiveQuotientGluing318.projection S c D.val.datum
local notation "i" => ContactProjectiveQuotientGluing318.into S c D.val.datum
local notation "Ω" => ContactBoundedDivisorAvoidance318.locus S c N D j
local notation "l" => ContactOriginalLinearOpenChart318.linearForm (j.val : ℚ)
local notation "h" => ContactOriginalLinearOpenChart318.linearForm_homogeneous (j.val : ℚ)
local notation "A" => ContactOriginalLinearOpenChart318.ring c l h
local notation "a" => ContactOriginalLinearOpenChart318.affineInto c l h
abbrev family := pullback p Ω.ι
abbrev projection : family S c N D j ⟶ Ω.toScheme := pullback.snd p Ω.ι
abbrev toFamily : family S c N D j ⟶ Z := pullback.fst p Ω.ι
@[expose] def original : family S c N D j ⟶ ContactProjectiveModel318.model c :=
  toFamily S c N D j ≫ i ≫ pullback.fst (ContactIntrinsicDifferentials318.structureMap c)
    (RelativeOriginalAffineChart318.baseMap (CommRingCat.of ℚ) S)
lemma supported : Set.range (original S c N D j) ⊆ Set.range a := by
  change Set.range (original S c N D j) ⊆ a.opensRange
  rw [ContactLinearOpenChartRange318.range]
  rintro _ ⟨z,rfl⟩
  exact FiniteFamilyAvoidanceUniversal318.supported p
    (ContactBoundedDivisorAvoidance318.toLine S c N D)
    (ContactBoundedDivisorAvoidance318.sourceOpen N j) z
/-- The ENTIRE actual restricted original divisor, not just selected
points or a chart restriction, factors through this affine source chart. -/
@[expose] def toAffineSource : family S c N D j ⟶ Spec A :=
  IsOpenImmersion.lift a (original S c N D j) (supported S c N D j)
@[reassoc] lemma source_into : toAffineSource S c N D j ≫ a=original S c N D j :=
  IsOpenImmersion.lift_fac _ _ _
lemma cartesian : IsPullback (toFamily S c N D j) (projection S c N D j) p Ω.ι :=
  IsPullback.of_hasPullback _ _
instance finite : IsFinite (projection S c N D j) := inferInstance
instance flat : Flat (projection S c N D j) := inferInstance
/-- Exact coefficient equation on the SAME original affine source ring. -/
@[reassoc] lemma source_over : toAffineSource S c N D j ≫
    Spec.map (CommRingCat.ofHom (algebraMap ℚ A))=
      projection S c N D j ≫ Ω.ι ≫ RelativeOriginalAffineChart318.baseMap (CommRingCat.of ℚ) S := by
  rw [← ContactOriginalLinearOpenChart318.affine_over,← Category.assoc,source_into]
  change (toFamily S c N D j ≫ i ≫ pullback.fst (ContactIntrinsicDifferentials318.structureMap c)
    (RelativeOriginalAffineChart318.baseMap (CommRingCat.of ℚ) S)) ≫ _=_
  rw [Category.assoc,Category.assoc,pullback.condition]
  rw [← Category.assoc i
    (pullback.snd (ContactIntrinsicDifferentials318.structureMap c)
      (RelativeOriginalAffineChart318.baseMap (CommRingCat.of ℚ) S))
    (RelativeOriginalAffineChart318.baseMap (CommRingCat.of ℚ) S)]
  change toFamily S c N D j ≫ p ≫ RelativeOriginalAffineChart318.baseMap (CommRingCat.of ℚ) S=_
  rw [← Category.assoc,pullback.condition,Category.assoc]
end ContactBoundedAvoidanceFamily318
