module
public import CubicChartGeometry318
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
import all WeierstrassGluing318
public section
noncomputable section
namespace CubicClosedImmersion318
open MvPolynomial HomogeneousLocalization AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CubicProjectiveMap318 CubicChartGeometry318
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R]
local notation "Poly" => MvPolynomial (Fin 3) R
local notation "G" => ProjectivePlane318.grading R

lemma restrict_closed_of_pullback {X Y U V : Scheme} (f : X ⟶ Y) (iX : U ⟶ X) (iY : V ⟶ Y)
    (f' : U ⟶ V) [IsOpenImmersion iY] [IsClosedImmersion f']
    (h : IsPullback f' iX iY f) : IsClosedImmersion (f ∣_ iY.opensRange) := by
  apply (MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion (morphismRestrictOpensRange f iY)).mpr
  rw [←h.flip.isoPullback_inv_snd]
  infer_instance

lemma restrict_Z_closed (A B : R) : IsClosedImmersion (embedding A B ∣_ Proj.basicOpen G (X 2)) := by
  rw [←ProjectiveAtlas318.chart_range R 2]
  have := ShortAffineScheme318.embedding_closed A B
  exact restrict_closed_of_pullback _ _ _ _ (finite_pullback A B)
lemma restrict_Y_closed (A B : R) : IsClosedImmersion (embedding A B ∣_ Proj.basicOpen G (X 1)) := by
  rw [←ProjectiveAtlas318.chart_range R 1]
  exact restrict_closed_of_pullback _ _ _ _ (infinity_pullback A B)

local instance : MorphismProperty.RespectsRight (@IsPreimmersion) (@IsOpenImmersion) where
  postcomp g hg f hf := by
    letI := hg
    letI := hf
    infer_instance

theorem embedding_preimmersion (A B : R) : IsPreimmersion (embedding A B) := by
  let U : Bool → (ProjectivePlane318.scheme R).Opens :=
    fun b => if b then Proj.basicOpen G (X 2) else Proj.basicOpen G (X 1)
  apply IsZariskiLocalAtTarget.of_range_subset_iSup (P := @IsPreimmersion) U
  · rintro _ ⟨p,rfl⟩
    rcases WeierstrassGluing318.charts_cover A B p with ⟨a,rfl⟩ | ⟨b,rfl⟩
    · apply (le_iSup U true)
      change WeierstrassGluing318.finiteChart A B a ∈ embedding A B ⁻¹ᵁ Proj.basicOpen G (X 2)
      rw [embedding_preimage_Z]
      exact ⟨a,rfl⟩
    · apply (le_iSup U false)
      change WeierstrassGluing318.infinityChart A B b ∈ embedding A B ⁻¹ᵁ Proj.basicOpen G (X 1)
      rw [embedding_preimage_Y]
      exact ⟨b,rfl⟩
  · intro b
    cases b
    · have := restrict_Y_closed A B
      exact inferInstanceAs (IsPreimmersion (embedding A B ∣_ Proj.basicOpen G (X 1)))
    · have := restrict_Z_closed A B
      exact inferInstanceAs (IsPreimmersion (embedding A B ∣_ Proj.basicOpen G (X 2)))

/-- The literal homogeneous Weierstrass cubic in the actual ambient Proj. -/
@[expose] def equation (A B : R) : Poly :=
  X 1^2*X 2-X 0^3-C A*X 0*X 2^2-C B*X 2^3
lemma equation_homogeneous (A B : R) : equation A B ∈ G 3 := by
  exact (((isHomogeneous_X R 1).pow 2 |>.mul (isHomogeneous_X R 2)).sub
    ((isHomogeneous_X R 0).pow 3)).sub
      (((isHomogeneous_C (Fin 3) A).mul (isHomogeneous_X R 0)).mul ((isHomogeneous_X R 2).pow 2)) |>.sub
        ((isHomogeneous_C (Fin 3) B).mul ((isHomogeneous_X R 2).pow 3))

lemma finite_equation_zero (A B : R) : finiteCoordinates A B (equation A B)=0 := by
  simp only [finiteCoordinates,equation,map_sub,map_mul,map_pow,aeval_X,aeval_C]
  simpa using ShortAffineJacobian318.relation A B
lemma infinity_equation_zero (A B : R) : infinityCoordinates A B (equation A B)=0 := by
  simp only [infinityCoordinates,equation,map_sub,map_mul,map_pow,aeval_X,aeval_C]
  simpa using InfinityChart318.relation A B

lemma image_equation (A B : R) (p : WeierstrassGluing318.scheme A B) :
    equation A B ∈ ((embedding A B) p).asHomogeneousIdeal := by
  rw [←not_not (a := equation A B ∈ ((embedding A B) p).asHomogeneousIdeal)]
  change ¬ (embedding A B) p ∈ Proj.basicOpen G (equation A B)
  rcases WeierstrassGluing318.charts_cover A B p with ⟨a,rfl⟩ | ⟨b,rfl⟩
  · rw [←Scheme.Hom.comp_apply,finite_embedding]
    change a ∉ finiteMap A B ⁻¹ᵁ Proj.basicOpen G (equation A B)
    rw [finiteMap_preimage _ _ _ (equation_homogeneous A B) (by omega),finite_equation_zero]
    simp
  · rw [←Scheme.Hom.comp_apply,infinity_embedding]
    change b ∉ infinityMap A B ⁻¹ᵁ Proj.basicOpen G (equation A B)
    rw [infinityMap_preimage _ _ _ (equation_homogeneous A B) (by omega),infinity_equation_zero]
    simp

@[expose] def dehomogenize (j : Fin 3) : Poly →ₐ[R] MvPolynomial (Fin 2) R :=
  (renameEquiv R (finSuccAboveEquiv j).symm).toAlgHom.comp
    (ProjectiveChart318.dehomogenize R (Fin 3) j)
lemma atlas_preimage (j : Fin 3) (q : Poly) {d : ℕ} (hq : q ∈ G d) (hd : 0<d) :
    ProjectiveAtlas318.chart R j ⁻¹ᵁ Proj.basicOpen G q=PrimeSpectrum.basicOpen (dehomogenize j q) := by
  unfold ProjectiveAtlas318.chart
  rw [Scheme.Hom.comp_preimage,Proj.awayι_preimage_basicOpen _ _ _ hq hd,SpecMap_preimage_basicOpen]
  congr 1
  change (ProjectiveAtlas318.chartEquiv R j) (Away.mk G (isHomogeneous_X R j) d (q^1) _)=_
  change (renameEquiv R (finSuccAboveEquiv j).symm)
    (ProjectiveChart318.fromChart R (Fin 3) j (Away.mk G (isHomogeneous_X R j) d (q^1) _))=_
  rw [ProjectiveChart318.fromChart_mk]
  simp [dehomogenize]

lemma dehomogenize_Z (A B : R) : dehomogenize 2 (equation A B)=ShortAffineJacobian318.equation A B := by
  simp [dehomogenize,equation,ProjectiveChart318.dehomogenize,ShortAffineJacobian318.equation]
  rfl
lemma dehomogenize_Y (A B : R) : dehomogenize 1 (equation A B)=InfinityChart318.equation A B := by
  simp [dehomogenize,equation,ProjectiveChart318.dehomogenize,InfinityChart318.equation]
  rfl

lemma equation_chart_cover (A B : R) (p : ProjectivePlane318.scheme R)
    (hp : equation A B ∈ p.asHomogeneousIdeal) :
    p ∈ Proj.basicOpen G (X 2) ∨ p ∈ Proj.basicOpen G (X 1) := by
  by_contra h
  have hz : X (2:Fin 3) ∈ p.asHomogeneousIdeal := by
    by_contra hn
    exact h (Or.inl hn)
  have hy : X (1:Fin 3) ∈ p.asHomogeneousIdeal := by
    by_contra hn
    exact h (Or.inr hn)
  have hxpow : X (0:Fin 3)^3 ∈ p.asHomogeneousIdeal.toIdeal := by
    have hh := p.asHomogeneousIdeal.toIdeal.sub_mem
      (p.asHomogeneousIdeal.toIdeal.mul_mem_left
        (X 1^2-C A*X 0*X 2-C B*X 2^2) hz) hp
    convert hh using 1
    simp only [equation]
    ring
  have hx : X (0:Fin 3) ∈ p.asHomogeneousIdeal := p.isPrime.mem_of_pow_mem 3 hxpow
  have ht : p ∈ (⊤ : (ProjectivePlane318.scheme R).Opens) := trivial
  rw [←ProjectiveAtlas318.standard_opens_cover R,TopologicalSpace.Opens.mem_iSup] at ht
  obtain ⟨j,hj⟩ := ht
  fin_cases j
  · exact hj hx
  · exact hj hy
  · exact hj hz

lemma quotient_range {T : Type u} [CommRing T] (f : T) (p : PrimeSpectrum T) (hp : f ∈ p.asIdeal) :
    p ∈ Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span ({f}:Set T))))) := by
  change p ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span ({f}:Set T))))
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,Ideal.mk_ker]
  exact (Ideal.span_singleton_le_iff_mem p.asIdeal).mpr hp

lemma finite_embedding_range (A B : R) (p : PrimeSpectrum (MvPolynomial (Fin 2) R))
    (hp : ShortAffineJacobian318.equation A B ∈ p.asIdeal) :
    p ∈ Set.range (ShortAffineScheme318.embedding A B) := by
  have hI : Ideal.span (Set.range (ShortAffineJacobian318.equations A B))=
      Ideal.span ({ShortAffineJacobian318.equation A B}:Set (MvPolynomial (Fin 2) R)) := by
    congr 1
    ext q
    constructor
    · rintro ⟨i,rfl⟩
      rfl
    · intro hq
      exact ⟨(),hq.symm⟩
  change p ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk _))
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,Ideal.mk_ker,hI]
  exact (Ideal.span_singleton_le_iff_mem p.asIdeal).mpr hp
lemma infinity_embedding_range (A B : R) (p : PrimeSpectrum (MvPolynomial (Fin 2) R))
    (hp : InfinityChart318.equation A B ∈ p.asIdeal) :
    p ∈ Set.range (infinityEmbedding A B) := by
  have hI : Ideal.span (Set.range (InfinityChart318.equations A B))=
      Ideal.span ({InfinityChart318.equation A B}:Set (MvPolynomial (Fin 2) R)) := by
    congr 1
    ext q
    constructor
    · rintro ⟨i,rfl⟩
      rfl
    · intro hq
      exact ⟨(),hq.symm⟩
  change p ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk _))
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,Ideal.mk_ker,hI]
  exact (Ideal.span_singleton_le_iff_mem p.asIdeal).mpr hp

/-- Every point of the homogeneous cubic is on one of our two actual quotient charts. -/
theorem equation_in_image (A B : R) (p : ProjectivePlane318.scheme R)
    (hp : equation A B ∈ p.asHomogeneousIdeal) : p ∈ Set.range (embedding A B) := by
  rcases equation_chart_cover A B p hp with hz | hy
  · rw [←ProjectiveAtlas318.chart_range R 2] at hz
    obtain ⟨q,rfl⟩ := hz
    have hq : ShortAffineJacobian318.equation A B ∈ q.asIdeal := by
      have hn : q ∉ ProjectiveAtlas318.chart R 2 ⁻¹ᵁ Proj.basicOpen G (equation A B) := by
        exact not_not.mpr hp
      rw [atlas_preimage _ _ (equation_homogeneous A B) (by omega),dehomogenize_Z] at hn
      exact not_not.mp hn
    obtain ⟨a,ha⟩ := finite_embedding_range A B q hq
    refine ⟨WeierstrassGluing318.finiteChart A B a,?_⟩
    rw [←Scheme.Hom.comp_apply,finite_embedding,finiteMap_eq,Scheme.Hom.comp_apply,ha]
    rfl
  · rw [←ProjectiveAtlas318.chart_range R 1] at hy
    obtain ⟨q,rfl⟩ := hy
    have hq : InfinityChart318.equation A B ∈ q.asIdeal := by
      have hn : q ∉ ProjectiveAtlas318.chart R 1 ⁻¹ᵁ Proj.basicOpen G (equation A B) := by
        exact not_not.mpr hp
      rw [atlas_preimage _ _ (equation_homogeneous A B) (by omega),dehomogenize_Y] at hn
      exact not_not.mp hn
    obtain ⟨b,hb⟩ := infinity_embedding_range A B q hq
    refine ⟨WeierstrassGluing318.infinityChart A B b,?_⟩
    rw [←Scheme.Hom.comp_apply,infinity_embedding,infinityMap_eq,Scheme.Hom.comp_apply,hb]

/-- Exact closed support, with no missing X-chart point. -/
theorem embedding_range (A B : R) : Set.range (embedding A B)=ProjectiveSpectrum.zeroLocus G {equation A B} := by
  ext p
  constructor
  · rintro ⟨a,rfl⟩
    exact Set.singleton_subset_iff.mpr (image_equation A B a)
  · intro hp
    exact equation_in_image A B p (Set.singleton_subset_iff.mp hp)

/-- The actual glued Weierstrass cubic is a closed subscheme of the actual proper Proj plane. -/
theorem embedding_closed (A B : R) : IsClosedImmersion (embedding A B) := by
  have := embedding_preimmersion A B
  apply IsClosedImmersion.of_isPreimmersion
  rw [embedding_range]
  exact ProjectiveSpectrum.isClosed_zeroLocus G _

/-- Properness of the actual two-chart cubic over its original base ring. -/
theorem structure_proper (A B : R) : IsProper (WeierstrassGluing318.structureMap A B) := by
  rw [←embedding_over_base]
  have := embedding_closed A B
  have := ProjectivePlane318.structure_proper R
  infer_instance

/-- The literal open-j family is genuinely proper, not merely a glued smooth affine object. -/
theorem literal_proper (N : ℕ) : IsProper (WeierstrassGluing318.literalStructureMap N) :=
  structure_proper _ _

/-- The original infinity section is now a genuine closed immersion. -/
theorem infinity_closed (A B : R) : IsClosedImmersion (WeierstrassGluing318.infinity A B) := by
  have := structure_proper A B
  have : IsClosedImmersion (WeierstrassGluing318.infinity A B ≫ WeierstrassGluing318.structureMap A B) := by
    rw [WeierstrassGluing318.infinity_section]
    infer_instance
  exact IsClosedImmersion.of_comp (WeierstrassGluing318.infinity A B) (WeierstrassGluing318.structureMap A B)

theorem structure_separated (A B : R) : IsSeparated (WeierstrassGluing318.structureMap A B) := by
  have := structure_proper A B
  infer_instance

end CubicClosedImmersion318
