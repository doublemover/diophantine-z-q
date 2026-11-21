module
public import SelectedGeneralizedProjectiveMap318
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public section
noncomputable section
open MvPolynomial HomogeneousLocalization AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open SelectedGeneralizedAffineInfinity318 SelectedGeneralizedProjectiveOverlap318
open SelectedGeneralizedLocalizedOverlap318 SelectedGeneralizedGluedCarrier318
open SelectedGeneralizedProjectiveMap318
attribute [local instance] MvPolynomial.gradedAlgebra

namespace SelectedGeneralizedProjectiveChartPullbacks318

universe u
variable {R : Type u} [CommRing R]
local notation "P" => MvPolynomial (Fin 3) R
local notation "G" => ProjectivePlane318.grading R
abbrev PlaneChart (R : Type*) [CommRing R] := Spec (CommRingCat.of (MvPolynomial (Fin 2) R))

@[expose] def closedZ (d : Rˣ) : Finite d ⟶ PlaneChart R :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range (finiteEquations d)))))

@[expose] def closedY (d : Rˣ) : Infinity d ⟶ PlaneChart R :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range (equations d)))))

instance closedZ_closed (d : Rˣ) : IsClosedImmersion (closedZ d) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
instance closedY_closed (d : Rˣ) : IsClosedImmersion (closedY d) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

theorem finiteMap_factor (d : Rˣ) : finiteMap d = closedZ d ≫ ProjectiveAtlas318.chart R 2 := by
  unfold finiteMap closedZ finiteHom ProjectiveAtlas318.chart
  rw [← Spec.map_comp_assoc] <;> rfl

theorem infinityMap_factor (d : Rˣ) : infinityMap d = closedY d ≫ ProjectiveAtlas318.chart R 1 := by
  unfold infinityMap closedY infinityHom ProjectiveAtlas318.chart
  rw [← Spec.map_comp_assoc] <;> rfl

theorem embedding_over_base (d : Rˣ) :
    embedding d ≫ ProjectivePlane318.structureMap R = overBase d := by
  apply pushout.hom_ext
  · change jZ d ≫ (embedding d ≫ _) = jZ d ≫ overBase d
    rw [← Category.assoc,finite_embedding,finiteMap_factor,Category.assoc,
      ProjectiveAtlas318.chart_over_base,jZ_over]
    unfold closedZ Spec.algebraMap
    rw [← Spec.map_comp] <;> rfl
  · change jY d ≫ (embedding d ≫ _) = jY d ≫ overBase d
    rw [← Category.assoc,infinity_embedding,infinityMap_factor,Category.assoc,
      ProjectiveAtlas318.chart_over_base,jY_over]
    unfold closedY Spec.algebraMap
    rw [← Spec.map_comp] <;> rfl

section Eval
variable {S : Type u} [CommRing S] [Algebra R S]
theorem chartEval_preimage (φ : P →ₐ[R] S) (i : Fin 3) (hi : φ (X i)=1)
    (q : P) {k : ℕ} (hq : q ∈ G k) (hk : 0<k) :
    (Spec.map (CommRingCat.ofHom (ProjectiveEvaluation318.chartEval φ i (hi ▸ isUnit_one)).toRingHom) ≫
      Proj.awayι G (X i) (isHomogeneous_X R i) (by decide)) ⁻¹ᵁ Proj.basicOpen G q =
      PrimeSpectrum.basicOpen (φ q) := by
  rw [Scheme.Hom.comp_preimage]
  erw [Proj.awayι_preimage_basicOpen (𝒜 := ProjectivePlane318.grading R)
    (isHomogeneous_X R i) (by decide) hq hk]
  rw [SpecMap_preimage_basicOpen]
  congr 1
  change ProjectiveEvaluation318.evaluate φ.toRingHom (X i) _
    (Away.mk G (isHomogeneous_X R i) k (q^1) _) = φ q
  rw [ProjectiveEvaluation318.evaluate_mk _ _ _ _ _ _ _ 1 (by simp [hi])]
  simp
end Eval

@[expose] def finiteCoords (d : Rˣ) : P →ₐ[R] FiniteChart d := aeval ![x d,y d,1]
@[expose] def infinityCoords (d : Rˣ) : P →ₐ[R] Chart d := aeval ![parameter d,1,ordinate d]
theorem finite_Z (d : Rˣ) : finiteCoords d (X 2)=1 := by simp [finiteCoords]
theorem infinity_Y (d : Rˣ) : infinityCoords d (X 1)=1 := by simp [infinityCoords]

theorem finiteHom_eval (d : Rˣ) : finiteHom d =
    ProjectiveEvaluation318.chartEval (finiteCoords d) 2 ((finite_Z d) ▸ isUnit_one) := by
  apply ProjectiveAtlas318.chart_hom_ext R 2
  intro i
  rw [ProjectiveEvaluation318.chartEval_X _ _ _ _ 1 (by simp [finite_Z])]
  fin_cases i
  · simp [finiteCoords,show (2:Fin 3).succAbove (0:Fin 2)=0 from rfl]
  · simp [finiteCoords,show (2:Fin 3).succAbove (1:Fin 2)=1 from rfl]

theorem infinityHom_eval (d : Rˣ) : infinityHom d =
    ProjectiveEvaluation318.chartEval (infinityCoords d) 1 ((infinity_Y d) ▸ isUnit_one) := by
  apply ProjectiveAtlas318.chart_hom_ext R 1
  intro i
  rw [ProjectiveEvaluation318.chartEval_X _ _ _ _ 1 (by simp [infinity_Y])]
  fin_cases i <;> simp [infinityCoords]

theorem finiteMap_preimage (d : Rˣ) (q : P) {k : ℕ} (hq : q ∈ G k) (hk : 0<k) :
    finiteMap d ⁻¹ᵁ Proj.basicOpen G q = PrimeSpectrum.basicOpen (finiteCoords d q) := by
  unfold finiteMap
  rw [finiteHom_eval]
  exact chartEval_preimage _ _ (finite_Z d) q hq hk

theorem infinityMap_preimage (d : Rˣ) (q : P) {k : ℕ} (hq : q ∈ G k) (hk : 0<k) :
    infinityMap d ⁻¹ᵁ Proj.basicOpen G q = PrimeSpectrum.basicOpen (infinityCoords d q) := by
  unfold infinityMap
  rw [infinityHom_eval]
  exact chartEval_preimage _ _ (infinity_Y d) q hq hk

theorem intoY_range (d : Rˣ) :
    (intoY d).opensRange = PrimeSpectrum.basicOpen (ordinate d) :=
  Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of (Chart d)) (ordinate d)

theorem intoZ_range (d : Rˣ) :
    (intoZ d).opensRange = PrimeSpectrum.basicOpen (y d) := by
  unfold intoZ
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  exact Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of (FiniteChart d)) (y d)

theorem embedding_preimage_Z (d : Rˣ) :
    embedding d ⁻¹ᵁ Proj.basicOpen G (X 2) = (jZ d).opensRange := by
  ext p
  constructor
  · intro hp
    rcases charts_cover d p with ⟨a,rfl⟩ | ⟨b,rfl⟩
    · exact ⟨a,rfl⟩
    · have hpb : b ∈ infinityMap d ⁻¹ᵁ Proj.basicOpen G (X 2) := by
        change (infinityMap d) b ∈ Proj.basicOpen G (X 2)
        change (embedding d) (jY d b) ∈ Proj.basicOpen G (X 2) at hp
        simpa only [← Scheme.Hom.comp_apply,infinity_embedding] using hp
      have hO : (infinityMap d) ⁻¹ᵁ Proj.basicOpen G (X 2) =
          (PrimeSpectrum.basicOpen (ordinate d) : (Infinity d).Opens) := by
        rw [infinityMap_preimage d _ (isHomogeneous_X R 2) (by decide)]
        simp [infinityCoords]
      have hb : b ∈ (PrimeSpectrum.basicOpen (ordinate d) : (Infinity d).Opens) :=
        (iff_of_eq (congrArg (fun U : (Infinity d).Opens => b ∈ U) hO)).mp hpb
      rw [← intoY_range d] at hb
      obtain ⟨c,hc⟩ := hb
      refine ⟨intoZ d c,?_⟩
      rw [← hc,← Scheme.Hom.comp_apply,← Scheme.Hom.comp_apply]
      exact congrArg (fun f : Intersection d ⟶ Carrier d => f c)
        (pushout.condition (f := intoZ d) (g := intoY d))
  · rintro ⟨a,rfl⟩
    change (embedding d) (jZ d a) ∈ Proj.basicOpen G (X 2)
    rw [← Scheme.Hom.comp_apply,finite_embedding]
    have h : a ∈ finiteMap d ⁻¹ᵁ Proj.basicOpen G (X 2) := by
      rw [finiteMap_preimage d _ (isHomogeneous_X R 2) (by decide),finite_Z]
      simp <;> trivial
    exact h

theorem embedding_preimage_Y (d : Rˣ) :
    embedding d ⁻¹ᵁ Proj.basicOpen G (X 1) = (jY d).opensRange := by
  ext p
  constructor
  · intro hp
    rcases charts_cover d p with ⟨a,rfl⟩ | ⟨b,rfl⟩
    · have hpa : a ∈ finiteMap d ⁻¹ᵁ Proj.basicOpen G (X 1) := by
        change (finiteMap d) a ∈ Proj.basicOpen G (X 1)
        change (embedding d) (jZ d a) ∈ Proj.basicOpen G (X 1) at hp
        simpa only [← Scheme.Hom.comp_apply,finite_embedding] using hp
      have hO : (finiteMap d) ⁻¹ᵁ Proj.basicOpen G (X 1) =
          (PrimeSpectrum.basicOpen (y d) : (Finite d).Opens) := by
        rw [finiteMap_preimage d _ (isHomogeneous_X R 1) (by decide)]
        simp [finiteCoords]
      have ha : a ∈ (PrimeSpectrum.basicOpen (y d) : (Finite d).Opens) :=
        (iff_of_eq (congrArg (fun U : (Finite d).Opens => a ∈ U) hO)).mp hpa
      rw [← intoZ_range d] at ha
      obtain ⟨c,hc⟩ := ha
      refine ⟨intoY d c,?_⟩
      rw [← hc,← Scheme.Hom.comp_apply,← Scheme.Hom.comp_apply]
      exact congrArg (fun f : Intersection d ⟶ Carrier d => f c)
        (pushout.condition (f := intoZ d) (g := intoY d)).symm
    · exact ⟨b,rfl⟩
  · rintro ⟨b,rfl⟩
    change (embedding d) (jY d b) ∈ Proj.basicOpen G (X 1)
    rw [← Scheme.Hom.comp_apply,infinity_embedding]
    have h : b ∈ infinityMap d ⁻¹ᵁ Proj.basicOpen G (X 1) := by
      rw [infinityMap_preimage d _ (isHomogeneous_X R 1) (by decide),infinity_Y]
      simp <;> trivial
    exact h

theorem finite_pullback (d : Rˣ) :
    IsPullback (closedZ d) (jZ d) (ProjectiveAtlas318.chart R 2) (embedding d) := by
  apply IsOpenImmersion.isPullback
  · rw [finite_embedding,finiteMap_factor]
  · rw [ProjectiveAtlas318.chart_range,embedding_preimage_Z]

theorem infinity_pullback (d : Rˣ) :
    IsPullback (closedY d) (jY d) (ProjectiveAtlas318.chart R 1) (embedding d) := by
  apply IsOpenImmersion.isPullback
  · rw [infinity_embedding,infinityMap_factor]
  · rw [ProjectiveAtlas318.chart_range,embedding_preimage_Y]

end SelectedGeneralizedProjectiveChartPullbacks318

#print axioms SelectedGeneralizedProjectiveChartPullbacks318.finite_pullback
#print axioms SelectedGeneralizedProjectiveChartPullbacks318.infinity_pullback
