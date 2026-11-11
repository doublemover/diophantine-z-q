module
public import PrincipalQuotientComplexPoint318
public import FourRootDerivativeIdealClosed318
public section
noncomputable section
namespace FourRootZeroSchemeSupport318
open AlgebraicGeometry CategoryTheory
open scoped BigOperators
open FourRootGluedDerivativeIdeal318 FourRootDerivativeZeroIdeals318
open FourRootNormalizedPointCharts318 FourRootCompletedSchemePoints318
/-- Exact image comparison from the actual open preimage square. -/
lemma image_square {A B C D : Type*} (i : A → B) (j : C → D)
    (q : A → C) (f : B → D) (hj : Function.Injective j)
    (hw : ∀ a, f (i a) = j (q a))
    (hp : ∀ b, f b ∈ Set.range j → b ∈ Set.range i) (c : C) :
    j c ∈ Set.range f ↔ c ∈ Set.range q := by
  constructor
  · rintro ⟨b,hb⟩
    obtain ⟨a,rfl⟩ := hp b ⟨c,hb.symm⟩
    exact ⟨a,hj ((hw a).symm.trans hb)⟩
  · rintro ⟨a,rfl⟩
    exact ⟨i a,hw a⟩
variable (b : Fin 4 → ℂ)
lemma finite_image (p : FinitePoints b) :
    (finitePoint b p).val default ∈ Set.range (into b) ↔
      (FourRootActualResidueInertia318.finiteEvaluation b p) (finiteGenerator b) = 0 := by
  change FourRootGluedScheme318.finiteChart b
    ((Spec.map (CommRingCat.ofHom
      (FourRootActualResidueInertia318.finiteEvaluation b p).toRingHom)) default) ∈ _ ↔ _
  rw [image_square (FourRootGluedDerivativeIdeal318.finiteChart b) (FourRootGluedScheme318.finiteChart b)
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (finiteIdeal b)))) (into b)
    (FourRootGluedScheme318.finiteChart b).isOpenEmbedding.injective
    (fun a => congrArg (fun f : finiteZero b ⟶ FourRootGluedScheme318.scheme b => f a)
      (finiteChart_into b))
    (fun z hz => by
      change z ∈ (FourRootGluedDerivativeIdeal318.finiteChart b).opensRange
      rw [←FourRootDerivativeIdealClosed318.finite_preimage]
      exact hz)]
  exact PrincipalQuotientComplexPoint318.image_iff _ _
lemma infinity_image (p : InfinityPoints b) :
    (infinityPoint b p).val default ∈ Set.range (into b) ↔
      (FourRootActualResidueInertia318.infinityEvaluation b p) (infinityGenerator b) = 0 := by
  change FourRootGluedScheme318.infinityChart b
    ((Spec.map (CommRingCat.ofHom
      (FourRootActualResidueInertia318.infinityEvaluation b p).toRingHom)) default) ∈ _ ↔ _
  rw [image_square (FourRootGluedDerivativeIdeal318.infinityChart b) (FourRootGluedScheme318.infinityChart b)
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (infinityIdeal b)))) (into b)
    (FourRootGluedScheme318.infinityChart b).isOpenEmbedding.injective
    (fun a => congrArg (fun f : infinityZero b ⟶ FourRootGluedScheme318.scheme b => f a)
      (infinityChart_into b))
    (fun z hz => by
      change z ∈ (FourRootGluedDerivativeIdeal318.infinityChart b).opensRange
      rw [←FourRootDerivativeIdealClosed318.infinity_preimage]
      exact hz)]
  exact PrincipalQuotientComplexPoint318.image_iff _ _
lemma finite_generator_value (p : FinitePoints b) :
    (FourRootActualResidueInertia318.finiteEvaluation b p) (finiteGenerator b) =
      ∏ i : Fin 4, p.val.2 i := by
  simp [finiteGenerator,FourRootActualResidueInertia318.finiteEvaluation,
    FourRootAffineCoordinateRing318.pointEquiv]
lemma infinity_generator_value (p : InfinityPoints b) :
    (FourRootActualResidueInertia318.infinityEvaluation b p) (infinityGenerator b) =
      p.val.1 * ∏ i : Fin 4, p.val.2 i := by
  simp [infinityGenerator,FourRootActualResidueInertia318.infinityEvaluation,
    FourRootInfinityCoordinateRing318.pointEquiv]
/-- Exact whole finite support, not merely a selected sign fiber. -/
theorem finite_support (p : FinitePoints b) :
    (finitePoint b p).val default ∈ Set.range (into b) ↔ ∃ i, p.val.1 = b i := by
  classical
  rw [finite_image,finite_generator_value,Finset.prod_eq_zero_iff]
  simp only [Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,hi⟩
    refine ⟨i,sub_eq_zero.mp ?_⟩
    rw [←p.property i,hi,zero_pow (by decide : 2 ≠ 0)]
  · rintro ⟨i,hi⟩
    have hs : p.val.2 i ^ 2 = 0 := by rw [p.property i,hi,sub_self]
    exact ⟨i,pow_eq_zero hs⟩
/-- All eight actual normalized infinity centers belong to the zero scheme. -/
theorem infinity_center (s : InfinitySigns) :
    (infinityPoint b (center b s)).val default ∈ Set.range (into b) := by
  rw [infinity_image,infinity_generator_value]
  exact zero_mul _
end FourRootZeroSchemeSupport318
