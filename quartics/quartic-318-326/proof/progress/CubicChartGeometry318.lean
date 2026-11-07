module
public import CubicProjectiveMap318
import all WeierstrassGluing318
public section
noncomputable section
namespace CubicChartGeometry318
open MvPolynomial HomogeneousLocalization AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open WeierstrassOverlap318 CubicProjectiveMap318
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R]
local notation "P" => MvPolynomial (Fin 3) R
local notation "G" => ProjectivePlane318.grading R

@[expose] def infinityEmbedding (A B : R) : InfinitySmooth318.scheme A B ⟶
    Spec (CommRingCat.of (MvPolynomial (Fin 2) R)) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range (InfinityChart318.equations A B)))))
instance infinityEmbedding_closed (A B : R) : IsClosedImmersion (infinityEmbedding A B) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

lemma finiteMap_eq (A B : R) : finiteMap A B=
    ShortAffineScheme318.embedding A B ≫ ProjectiveAtlas318.chart R 2 := by
  unfold finiteMap finiteHom ShortAffineScheme318.embedding ProjectiveAtlas318.chart
  rw [←Spec.map_comp_assoc]
  rfl
lemma infinityMap_eq (A B : R) : infinityMap A B=
    infinityEmbedding A B ≫ ProjectiveAtlas318.chart R 1 := by
  unfold infinityMap infinityHom infinityEmbedding ProjectiveAtlas318.chart
  rw [←Spec.map_comp_assoc]
  rfl

theorem embedding_over_base (A B : R) : embedding A B ≫ ProjectivePlane318.structureMap R=
    WeierstrassGluing318.structureMap A B := by
  apply pushout.hom_ext
  · change WeierstrassGluing318.finiteChart A B ≫ (embedding A B ≫ _)=_
    rw [←Category.assoc,finite_embedding,finiteMap_eq,Category.assoc,
      ProjectiveAtlas318.chart_over_base,ShortAffineScheme318.embedding_over_base]
    exact (WeierstrassGluing318.finiteChart_structure A B).symm
  · change WeierstrassGluing318.infinityChart A B ≫ (embedding A B ≫ _)=_
    rw [←Category.assoc,infinity_embedding,infinityMap_eq,Category.assoc,
      ProjectiveAtlas318.chart_over_base]
    change _=WeierstrassGluing318.infinityChart A B ≫ WeierstrassGluing318.structureMap A B
    rw [WeierstrassGluing318.infinityChart_structure]
    unfold infinityEmbedding InfinitySmooth318.structureMap
    rw [←Spec.map_comp]
    rfl

section Eval
variable {S : Type u} [CommRing S] [Algebra R S]
lemma chartEval_preimage (φ : P →ₐ[R] S) (j : Fin 3) (hj : φ (X j)=1)
    (q : P) {d : ℕ} (hq : q ∈ G d) (hd : 0<d) :
    (Spec.map (CommRingCat.ofHom (ProjectiveEvaluation318.chartEval φ j (hj ▸ isUnit_one)).toRingHom) ≫
      Proj.awayι G (X j) (isHomogeneous_X R j) (by omega)) ⁻¹ᵁ Proj.basicOpen G q=
        PrimeSpectrum.basicOpen (φ q) := by
  rw [Scheme.Hom.comp_preimage,Proj.awayι_preimage_basicOpen _ _ _ hq hd,
    SpecMap_preimage_basicOpen]
  congr 1
  change ProjectiveEvaluation318.evaluate φ.toRingHom (X j) _
    (Away.isLocalizationElem (isHomogeneous_X R j) hq)=φ q
  change ProjectiveEvaluation318.evaluate φ.toRingHom (X j) _
    (Away.mk G (isHomogeneous_X R j) d (q^1) _)=φ q
  rw [ProjectiveEvaluation318.evaluate_mk _ _ _ _ _ _ _ 1 (by simp [hj])]
  simp
end Eval

@[expose] def finiteCoordinates (A B : R) : P →ₐ[R] Affine A B :=
  aeval ![ShortAffineJacobian318.x A B,ShortAffineJacobian318.y A B,1]
@[expose] def infinityCoordinates (A B : R) : P →ₐ[R] Infinity A B :=
  aeval ![InfinityChart318.x A B,1,InfinityChart318.z A B]
lemma finite_Z (A B : R) : finiteCoordinates A B (X 2)=1 := by simp [finiteCoordinates]
lemma infinity_Y (A B : R) : infinityCoordinates A B (X 1)=1 := by simp [infinityCoordinates]
lemma finiteHom_eval (A B : R) : finiteHom A B=
    ProjectiveEvaluation318.chartEval (finiteCoordinates A B) 2 ((finite_Z A B) ▸ isUnit_one) := by
  apply ProjectiveAtlas318.chart_hom_ext R 2
  intro i
  rw [ProjectiveEvaluation318.chartEval_X _ _ _ _ 1 (by simp [finite_Z])]
  fin_cases i
  · simp [finiteCoordinates,show (2:Fin 3).succAbove (0:Fin 2)=0 from rfl]
  · simp [finiteCoordinates,show (2:Fin 3).succAbove (1:Fin 2)=1 from rfl]
lemma infinityHom_eval (A B : R) : infinityHom A B=
    ProjectiveEvaluation318.chartEval (infinityCoordinates A B) 1 ((infinity_Y A B) ▸ isUnit_one) := by
  apply ProjectiveAtlas318.chart_hom_ext R 1
  intro i
  rw [ProjectiveEvaluation318.chartEval_X _ _ _ _ 1 (by simp [infinity_Y])]
  fin_cases i <;> simp [infinityCoordinates]

lemma finiteMap_preimage (A B : R) (q : P) {d : ℕ} (hq : q ∈ G d) (hd : 0<d) :
    finiteMap A B ⁻¹ᵁ Proj.basicOpen G q=PrimeSpectrum.basicOpen (finiteCoordinates A B q) := by
  unfold finiteMap
  rw [finiteHom_eval]
  exact chartEval_preimage _ _ (finite_Z A B) q hq hd
lemma infinityMap_preimage (A B : R) (q : P) {d : ℕ} (hq : q ∈ G d) (hd : 0<d) :
    infinityMap A B ⁻¹ᵁ Proj.basicOpen G q=PrimeSpectrum.basicOpen (infinityCoordinates A B q) := by
  unfold infinityMap
  rw [infinityHom_eval]
  exact chartEval_preimage _ _ (infinity_Y A B) q hq hd

lemma intoInfinity_range (A B : R) : (WeierstrassGluing318.intoInfinity A B).opensRange=
    PrimeSpectrum.basicOpen (InfinityChart318.z A B) := by
  exact Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of (Infinity A B)) (InfinityChart318.z A B)
lemma intoAffine_range (A B : R) : (WeierstrassGluing318.intoAffine A B).opensRange=
    PrimeSpectrum.basicOpen (ShortAffineJacobian318.y A B) := by
  unfold WeierstrassGluing318.intoAffine
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  exact Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of (Affine A B)) (ShortAffineJacobian318.y A B)

lemma embedding_preimage_Z (A B : R) : embedding A B ⁻¹ᵁ Proj.basicOpen G (X 2)=
    (WeierstrassGluing318.finiteChart A B).opensRange := by
  ext p
  constructor
  · intro hp
    rcases WeierstrassGluing318.charts_cover A B p with ⟨a,rfl⟩ | ⟨b,rfl⟩
    · exact ⟨a,rfl⟩
    · have hb : b ∈ PrimeSpectrum.basicOpen (InfinityChart318.z A B) := by
        have hp' : b ∈ infinityMap A B ⁻¹ᵁ Proj.basicOpen G (X 2) := by
          change (infinityMap A B) b ∈ Proj.basicOpen G (X 2)
          change (embedding A B) (WeierstrassGluing318.infinityChart A B b) ∈ Proj.basicOpen G (X 2) at hp
          simpa only [←Scheme.Hom.comp_apply,infinity_embedding] using hp
        simpa [infinityMap_preimage A B _ (isHomogeneous_X R 2) (by omega),infinityCoordinates] using hp'
      rw [←intoInfinity_range A B] at hb
      obtain ⟨c,hc⟩ := hb
      refine ⟨WeierstrassGluing318.intoAffine A B c,?_⟩
      rw [←hc,←Scheme.Hom.comp_apply,←Scheme.Hom.comp_apply]
      exact congrArg (fun f : WeierstrassGluing318.overlap A B ⟶ _ => f c)
        (pushout.condition (f := WeierstrassGluing318.intoAffine A B) (g := WeierstrassGluing318.intoInfinity A B))
  · rintro ⟨a,rfl⟩
    change (embedding A B) (WeierstrassGluing318.finiteChart A B a) ∈ Proj.basicOpen G (X 2)
    rw [←Scheme.Hom.comp_apply,finite_embedding]
    have : a ∈ finiteMap A B ⁻¹ᵁ Proj.basicOpen G (X 2) := by
      rw [finiteMap_preimage A B _ (isHomogeneous_X R 2) (by omega),finite_Z]
      simp
    exact this

lemma embedding_preimage_Y (A B : R) : embedding A B ⁻¹ᵁ Proj.basicOpen G (X 1)=
    (WeierstrassGluing318.infinityChart A B).opensRange := by
  ext p
  constructor
  · intro hp
    rcases WeierstrassGluing318.charts_cover A B p with ⟨a,rfl⟩ | ⟨b,rfl⟩
    · have ha : a ∈ PrimeSpectrum.basicOpen (ShortAffineJacobian318.y A B) := by
        have hp' : a ∈ finiteMap A B ⁻¹ᵁ Proj.basicOpen G (X 1) := by
          change (finiteMap A B) a ∈ Proj.basicOpen G (X 1)
          change (embedding A B) (WeierstrassGluing318.finiteChart A B a) ∈ Proj.basicOpen G (X 1) at hp
          simpa only [←Scheme.Hom.comp_apply,finite_embedding] using hp
        simpa [finiteMap_preimage A B _ (isHomogeneous_X R 1) (by omega),finiteCoordinates] using hp'
      rw [←intoAffine_range A B] at ha
      obtain ⟨c,hc⟩ := ha
      refine ⟨WeierstrassGluing318.intoInfinity A B c,?_⟩
      rw [←hc,←Scheme.Hom.comp_apply,←Scheme.Hom.comp_apply]
      exact congrArg (fun f : WeierstrassGluing318.overlap A B ⟶ _ => f c)
        (pushout.condition (f := WeierstrassGluing318.intoAffine A B) (g := WeierstrassGluing318.intoInfinity A B)).symm
    · exact ⟨b,rfl⟩
  · rintro ⟨b,rfl⟩
    change (embedding A B) (WeierstrassGluing318.infinityChart A B b) ∈ Proj.basicOpen G (X 1)
    rw [←Scheme.Hom.comp_apply,infinity_embedding]
    have : b ∈ infinityMap A B ⁻¹ᵁ Proj.basicOpen G (X 1) := by
      rw [infinityMap_preimage A B _ (isHomogeneous_X R 1) (by omega),infinity_Y]
      simp
    exact this

/-- The actual finite cubic chart is the scheme-theoretic inverse image of D(Z). -/
theorem finite_pullback (A B : R) : IsPullback (ShortAffineScheme318.embedding A B)
    (WeierstrassGluing318.finiteChart A B) (ProjectiveAtlas318.chart R 2) (embedding A B) := by
  apply IsOpenImmersion.isPullback
  · rw [finite_embedding,finiteMap_eq]
  · rw [ProjectiveAtlas318.chart_range,embedding_preimage_Z]
/-- The actual infinity cubic chart is the scheme-theoretic inverse image of D(Y). -/
theorem infinity_pullback (A B : R) : IsPullback (infinityEmbedding A B)
    (WeierstrassGluing318.infinityChart A B) (ProjectiveAtlas318.chart R 1) (embedding A B) := by
  apply IsOpenImmersion.isPullback
  · rw [infinity_embedding,infinityMap_eq]
  · rw [ProjectiveAtlas318.chart_range,embedding_preimage_Y]

end CubicChartGeometry318
