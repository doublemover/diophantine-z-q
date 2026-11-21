module
public import SelectedGeneralizedProjectiveChartPullbacks318
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public section
noncomputable section
open MvPolynomial HomogeneousLocalization AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open SelectedGeneralizedAffineInfinity318 SelectedGeneralizedProjectiveOverlap318
open SelectedGeneralizedGluedCarrier318 SelectedGeneralizedProjectiveMap318
open SelectedGeneralizedHomogeneousProjective318 SelectedGeneralizedProjectiveChartPullbacks318
attribute [local instance] MvPolynomial.gradedAlgebra

namespace SelectedGeneralizedProjectiveProper318

universe u
variable {R : Type u} [CommRing R]
local notation "G" => ProjectivePlane318.grading R

theorem restrict_closed {X Y U V : Scheme} (f : X ⟶ Y) (iX : U ⟶ X) (iY : V ⟶ Y)
    (f' : U ⟶ V) [IsOpenImmersion iY] [IsClosedImmersion f']
    (h : IsPullback f' iX iY f) : IsClosedImmersion (f ∣_ iY.opensRange) := by
  apply (MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion (morphismRestrictOpensRange f iY)).mpr
  rw [← h.flip.isoPullback_inv_snd]
  infer_instance

local instance : MorphismProperty.RespectsRight (@IsPreimmersion) (@IsOpenImmersion) where
  postcomp g hg f hf := by
    letI := hg
    letI := hf
    infer_instance

/-- On both standard opens, the very same glued map is the quotient
closed immersion. Thus it is a preimmersion with no additional gluing
of ideals assumed. -/
theorem embedding_preimmersion (d : Rˣ) : IsPreimmersion (embedding d) := by
  let U : Bool → (ProjectivePlane318.scheme R).Opens :=
    fun b => if b then Proj.basicOpen G (X 2) else Proj.basicOpen G (X 1)
  apply IsZariskiLocalAtTarget.of_range_subset_iSup (P := @IsPreimmersion) U
  · rintro _ ⟨p,rfl⟩
    rcases charts_cover d p with ⟨a,rfl⟩ | ⟨b,rfl⟩
    · apply (le_iSup U true)
      change jZ d a ∈ embedding d ⁻¹ᵁ Proj.basicOpen G (X 2)
      rw [embedding_preimage_Z]
      exact ⟨a,rfl⟩
    · apply (le_iSup U false)
      change jY d b ∈ embedding d ⁻¹ᵁ Proj.basicOpen G (X 1)
      rw [embedding_preimage_Y]
      exact ⟨b,rfl⟩
  · intro b
    cases b
    · change IsPreimmersion (embedding d ∣_ Proj.basicOpen G (X 1))
      rw [← ProjectiveAtlas318.chart_range R 1]
      have := restrict_closed _ _ _ _ (infinity_pullback d)
      infer_instance
    · change IsPreimmersion (embedding d ∣_ Proj.basicOpen G (X 2))
      rw [← ProjectiveAtlas318.chart_range R 2]
      have := restrict_closed _ _ _ _ (finite_pullback d)
      infer_instance

theorem finite_equation_zero (d : Rˣ) : finiteCoords d (homogeneousEquation d) = 0 := by
  simp only [finiteCoords,homogeneousEquation,map_add,map_sub,map_mul,map_pow,
    aeval_X,aeval_C,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons,one_pow,mul_one]
  simpa only [finiteValue,map_mul] using SelectedGeneralizedAffineJacobianCover318.finite_relation d

theorem infinity_equation_zero (d : Rˣ) : infinityCoords d (homogeneousEquation d) = 0 := by
  have h : Ideal.Quotient.mk (Ideal.span (Set.range (equations d))) (equation d) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨(),rfl⟩)
  simp only [equation,map_add,map_sub,map_mul,map_pow] at h
  simp only [infinityCoords,homogeneousEquation,map_add,map_sub,map_mul,map_pow,
    aeval_X,aeval_C,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    one_pow,one_mul,mul_one]
  exact h

theorem image_mem_equation (d : Rˣ) (p : Carrier d) :
    homogeneousEquation d ∈ ((embedding d) p).asHomogeneousIdeal := by
  rw [← not_not (a := homogeneousEquation d ∈ ((embedding d) p).asHomogeneousIdeal)]
  change ¬ (embedding d) p ∈ Proj.basicOpen G (homogeneousEquation d)
  rcases charts_cover d p with ⟨a,rfl⟩ | ⟨b,rfl⟩
  · rw [← Scheme.Hom.comp_apply,finite_embedding]
    change a ∉ finiteMap d ⁻¹ᵁ Proj.basicOpen G (homogeneousEquation d)
    rw [finiteMap_preimage _ _ (isHomogeneous d) (by decide),finite_equation_zero]
    simp <;> intro h <;> exact h
  · rw [← Scheme.Hom.comp_apply,infinity_embedding]
    change b ∉ infinityMap d ⁻¹ᵁ Proj.basicOpen G (homogeneousEquation d)
    rw [infinityMap_preimage _ _ (isHomogeneous d) (by decide),infinity_equation_zero]
    simp <;> intro h <;> exact h

theorem atlas_preimage (i : Fin 3) (q : MvPolynomial (Fin 3) R) {k : ℕ} (hq : q ∈ G k) (hk : 0<k) :
    ProjectiveAtlas318.chart R i ⁻¹ᵁ Proj.basicOpen G q =
      PrimeSpectrum.basicOpen (dehomogenize i q) := by
  unfold ProjectiveAtlas318.chart
  rw [Scheme.Hom.comp_preimage]
  erw [Proj.awayι_preimage_basicOpen (𝒜 := ProjectivePlane318.grading R)
    (isHomogeneous_X R i) (by decide) hq hk]
  rw [SpecMap_preimage_basicOpen]
  congr 1
  change (ProjectiveAtlas318.chartEquiv R i) (Away.mk G (isHomogeneous_X R i) k (q^1) _) = _
  change (renameEquiv R (finSuccAboveEquiv i).symm)
    (ProjectiveChart318.fromChart R (Fin 3) i (Away.mk G (isHomogeneous_X R i) k (q^1) _)) = _
  have hq1 : q^1 ∈ G (k • (1:ℕ)) := by
    simpa only [pow_one,nsmul_eq_mul,Nat.cast_id,mul_one] using hq
  exact (congrArg (renameEquiv R (finSuccAboveEquiv i).symm)
    (ProjectiveChart318.fromChart_mk R (Fin 3) i k (q^1) hq1)).trans (by simp [dehomogenize])

theorem quotient_range {T : Type u} [CommRing T] (f : T) (p : PrimeSpectrum T)
    (hp : f ∈ p.asIdeal) :
    p ∈ Set.range (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (Ideal.span (Set.range (fun _ : Unit => f)))))) := by
  change p ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk _))
  rw [_root_.range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,Ideal.mk_ker]
  apply Ideal.span_le.2
  rintro _ ⟨_,rfl⟩
  exact hp

theorem equation_in_image (d : Rˣ) (p : ProjectivePlane318.scheme R)
    (hp : homogeneousEquation d ∈ p.asHomogeneousIdeal) : p ∈ Set.range (embedding d) := by
  rcases actual_support_cover d p hp with hz | hy
  · rw [← ProjectiveAtlas318.chart_range R 2] at hz
    obtain ⟨q,rfl⟩ := hz
    have hq : finiteEquation d ∈ q.asIdeal := by
      have hn : q ∉ ProjectiveAtlas318.chart R 2 ⁻¹ᵁ Proj.basicOpen G (homogeneousEquation d) :=
        not_not.mpr hp
      rw [atlas_preimage _ _ (isHomogeneous d) (by decide),chart_Z] at hn
      exact not_not.mp hn
    have hr : ∃ a : Finite d, closedZ d a = q := quotient_range _ _ hq
    obtain ⟨a,ha⟩ := hr
    have hE : jZ d ≫ embedding d = closedZ d ≫ ProjectiveAtlas318.chart R 2 :=
      (finite_embedding d).trans (finiteMap_factor d)
    refine ⟨jZ d a,?_⟩
    have hp := congrArg (fun f : Finite d ⟶ ProjectivePlane318.scheme R => f a) hE
    simpa only [Scheme.Hom.comp_apply,ha] using hp
  · rw [← ProjectiveAtlas318.chart_range R 1] at hy
    obtain ⟨q,rfl⟩ := hy
    have hq : equation d ∈ q.asIdeal := by
      have hn : q ∉ ProjectiveAtlas318.chart R 1 ⁻¹ᵁ Proj.basicOpen G (homogeneousEquation d) :=
        not_not.mpr hp
      rw [atlas_preimage _ _ (isHomogeneous d) (by decide),chart_Y] at hn
      exact not_not.mp hn
    have hr : ∃ a : Infinity d, closedY d a = q := quotient_range _ _ hq
    obtain ⟨a,ha⟩ := hr
    have hE : jY d ≫ embedding d = closedY d ≫ ProjectiveAtlas318.chart R 1 :=
      (infinity_embedding d).trans (infinityMap_factor d)
    refine ⟨jY d a,?_⟩
    have hp := congrArg (fun f : Infinity d ⟶ ProjectivePlane318.scheme R => f a) hE
    simpa only [Scheme.Hom.comp_apply,ha] using hp

/-- Literal closed support, including all points in every residue
characteristic. No third independent affine model is inserted. -/
theorem embedding_range (d : Rˣ) :
    Set.range (embedding d) = ProjectiveSpectrum.zeroLocus G {homogeneousEquation d} := by
  ext p
  constructor
  · rintro ⟨a,rfl⟩
    exact Set.singleton_subset_iff.mpr (image_mem_equation d a)
  · intro hp
    exact equation_in_image d p (Set.singleton_subset_iff.mp hp)

theorem embedding_closed (d : Rˣ) : IsClosedImmersion (embedding d) := by
  have := embedding_preimmersion d
  apply IsClosedImmersion.of_isPreimmersion
  rw [embedding_range]
  exact ProjectiveSpectrum.isClosed_zeroLocus G _

/-- Properness on the very same generalized carrier used by the
identity jets and the arithmetic class over the original base. -/
theorem overBase_proper (d : Rˣ) : IsProper (overBase d) := by
  rw [← embedding_over_base d]
  have := embedding_closed d
  infer_instance

end SelectedGeneralizedProjectiveProper318

#print axioms SelectedGeneralizedProjectiveProper318.embedding_closed
#print axioms SelectedGeneralizedProjectiveProper318.overBase_proper
