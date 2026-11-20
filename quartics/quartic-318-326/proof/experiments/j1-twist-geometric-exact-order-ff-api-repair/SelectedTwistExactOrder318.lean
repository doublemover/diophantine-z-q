module
public import SelectedTwistMarkOverCover318
public import SelectedCoefficientZeroTest318
public import SelectedLiteralMarkedScaling318
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import all LiteralSchemePointGroup318
public section
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassGluing318
open SelectedPrimitiveAffineSign318 SelectedPrimitiveFixedX318 SelectedPrimitiveTwistPoint318
open SelectedAffineMarkCoefficient318 SelectedTwistMarkOverCover318 SelectedSignedMultiplication318
open SelectedCompletedMultiplication318 SelectedLiteralTorsionKernel318 SelectedPrimitiveOpen318
open LiteralSchemePointOperations318

namespace SelectedTwistExactOrder318
variable (n : ℕ) (I : Ideal (D n))
local notation "R" => SelectedPrimitiveAffineSign318.R n
local notation "Q" => D n ⧸ I
variable (τ : Q →ₐ[R] Q) (hτ : τ.comp (q n I) = (q n I).comp (sign n))
local notation "F" => fixed n I τ
variable (hY : IsUnit (ybar n I))
local notation "Y" => hY.unit
local notation "C" => algebraMap R Q (A n)
local notation "D₀" => algebraMap R Q (B n)
local notation "A₁" => twistA n I τ hτ hY
local notation "B₁" => twistB n I τ hτ hY
local notation "A₂" => algebraMap F Q A₁
local notation "B₂" => algebraMap F Q B₁
local notation "g" => OpenJAffineScheme318.discriminant_unit n
local notation "gQ" => CompletedAdditionCoefficient318.mapped_discriminant (S:=Q) (A n) (B n) g
local notation "gF" => disc_unit n I τ hτ hY
local notation "hA" => (over_original_chart n I τ hτ hY).1
local notation "hB" => (over_original_chart n I τ hτ hY).2.1
local notation "Q₀" => point (A n) (B n) (q n I)
local notation "Q₁" => sourcePoint n I
local notation "Q₂" => changedTwistPoint n I τ hτ hY
local notation "P" => twistPoint n I τ hτ hY
local notation "b" => Spec.algebraMap F Q

/-- Every actual zero test of the same primitive point after passage
through the cover coincides with that of the canonical twist. This holds
on arbitrary Scheme tests of the cover and for each lower order too. -/
theorem cover_zero_test {T : Scheme} (z : T ⟶ Spec (CommRingCat.of Q)) (k : ℕ) :
    Killed gF k (z ≫ b ≫ P) ↔ Killed g k (z ≫ Q₀) := by
  have hs : Killed (CompletedAdditionCoefficient318.mapped_discriminant (S:=Q) A₁ B₁ gF)
      k (z ≫ Q₂) ↔ Killed gQ k (z ≫ Q₁) := by
    simpa only [Category.assoc,same_point] using
      (SelectedCompletedMultiplication318.kills_iff A₂ B₂ C D₀ Y hA hB gQ k (z ≫ Q₁))
  have h₁ : Killed gQ k (z ≫ Q₁) ↔ Killed g k (z ≫ Q₀) := by
    simpa only [Category.assoc,literal_source_base] using
      (SelectedCoefficientZeroTest318.zero_test_iff (A n) (B n) g k (z ≫ Q₁))
  have h₂ : Killed (CompletedAdditionCoefficient318.mapped_discriminant (S:=Q) A₁ B₁ gF)
      k (z ≫ Q₂) ↔ Killed gF k (z ≫ b ≫ P) := by
    simpa only [Category.assoc,cover_twist_base] using
      (SelectedCoefficientZeroTest318.zero_test_iff A₁ B₁ gF k (z ≫ Q₂))
  exact h₂.symm.trans (hs.trans h₁)

variable (m : ℕ) [IsFinite (kernelProjection n m)] [Etale (kernelProjection n m)]
variable (hm : 1 < m)
variable (e : PrimitiveScheme n m ≅ Spec (CommRingCat.of Q))
variable (he : intoAffine n m hm =
  e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))

include he in
private theorem tautological :
    Q₀ = (e.inv ≫ inclusionOpen n m) ≫ inclusion n m := by
  have h : e.inv ≫ intoAffine n m hm = Spec.map (CommRingCat.ofHom (q n I).toRingHom) := by
    rw [he,e.inv_hom_id_assoc] <;> rfl
  rw [point,←h,Category.assoc,intoAffine_chart,←Category.assoc] <;> rfl

include he in
/-- The full [m] vanishing descends as equality of actual Scheme maps
through the proved faithfully flat, hence schematically dominant, cover. -/
theorem killed [Nontrivial F] : Killed gF m P := by
  let z := e.inv ≫ inclusionOpen n m
  have hq : Killed g m Q₀ := by
    rw [tautological n I m hm e he]
    exact (SelectedLiteralMarkedScaling318.literal_test n m (z ≫ kernelProjection n m)
      (pointOf n m z)).mpr (pointOf_killed n m z)
  have hc : Killed gF m (b ≫ P) := by
    have h := (cover_zero_test n I τ hτ hY (𝟙 _) m).mpr (by simpa only [Category.id_comp] using hq)
    simpa only [Category.id_comp] using h
  letI : Module.FaithfullyFlat F Q := SelectedOrdinateTorsor318.faithfully_flat n I τ hτ hY
  have hi : Function.Injective (algebraMap F Q) := FaithfulSMul.algebraMap_injective F Q
  letI : IsSchemeTheoreticallyDominant b :=
    SpecSchematicDensity318.spec_of_injective (CommRingCat.ofHom (algebraMap F Q)) hi
  letI := CubicClosedImmersion318.structure_proper A₁ B₁
  apply SchematicEqualityExtension318.ext (structureMap A₁ B₁) ?_ b
  · simp only [Category.assoc,mul_base,infinity_section,Category.comp_id]
  · simpa only [Killed,Category.assoc] using hc

include he in
/-- All proper positive lower tests fail on a genuine field specialization
of the cover. This is fiberwise, not a claim about an arbitrary one
global order on a disconnected test. -/
theorem exact_on_field_of_cover {K : Type} [Field K]
    (z : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of Q)) :
    ExactTests gF m (z ≫ b ≫ P) := by
  let t := (z ≫ e.inv) ≫ inclusionOpen n m
  have ht : t default ∈ primitive n m := by
    change ((z ≫ e.inv) ≫ inclusionOpen n m) default ∈ primitive n m
    rw [Scheme.Hom.comp_apply,←Scheme.Opens.range_ι]
    exact ⟨(z ≫ e.inv) default,rfl⟩
  have hm₀ : 0 < m := Nat.lt_trans (by decide : 0 < 1) hm
  have ho : addOrderOf (pointOf n m t) = m :=
    (primitive_iff_order n m t default hm₀).mp ht
  have hh := (SelectedLiteralMarkedScaling318.literal_tests_order n m hm₀
    (t ≫ kernelProjection n m) (pointOf n m t)).mpr ho
  have heq : (pointOf n m t).val = z ≫ Q₀ := by
    change ((z ≫ e.inv) ≫ inclusionOpen n m) ≫ inclusion n m = _
    rw [tautological n I m hm e he]
    simp only [Category.assoc]
  rw [heq] at hh
  exact ⟨(cover_zero_test n I τ hτ hY z m).mpr hh.1,
    fun k hk hkm hz => hh.2 k hk hkm ((cover_zero_test n I τ hτ hY z k).mp hz)⟩

end SelectedTwistExactOrder318

#print axioms SelectedTwistExactOrder318.killed
#print axioms SelectedTwistExactOrder318.exact_on_field_of_cover
