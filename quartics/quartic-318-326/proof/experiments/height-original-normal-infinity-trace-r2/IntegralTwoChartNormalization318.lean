module
public import IntegralReciprocalNormalClosures318
public import ContactGlobalProper318
public import NormalChart318
public section
noncomputable section
namespace IntegralTwoChartNormalization318
open Polynomial CategoryTheory AlgebraicGeometry IntegralReciprocalBase318
open IntegralReciprocalNormalClosures318
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : Type u) [CommRing R] [IsDomain R] [CharZero R]
  [IsNoetherianRing R] [IsIntegrallyClosed R[X]]
  (a : Fin 4 → R) (N : R) (B : Type u) [CommRing B] [IsDomain B]
  [Algebra (FiniteBase R a N) B] [Module.Finite (FiniteBase R a N) B]
  [Algebra.Etale (FiniteBase R a N) B]

@[expose] def baseOpen : Spec (CommRingCat.of (FiniteBase R a N)) ⟶ ProjectiveJLine318.scheme R :=
  Spec.map (CommRingCat.ofHom (algebraMap R[X] (FiniteBase R a N))) ≫ JLineAtlas318.chart R 1
instance baseOpen_open : IsOpenImmersion (baseOpen R a N) := by
  unfold baseOpen
  infer_instance
@[expose] def coverMap : Spec (CommRingCat.of B) ⟶ ProjectiveJLine318.scheme R :=
  Spec.map (CommRingCat.ofHom (algebraMap (FiniteBase R a N) B)) ≫ baseOpen R a N

theorem coverMap_properties : LocallyOfFiniteType (coverMap R a N B) ∧
    LocallyQuasiFinite (coverMap R a N B) ∧ IsSeparated (coverMap R a N B) ∧
    QuasiCompact (coverMap R a N B) := by
  letI : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap (FiniteBase R a N) B))) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  unfold coverMap baseOpen
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
instance coverMap_quasiCompact : QuasiCompact (coverMap R a N B) :=
  (coverMap_properties R a N B).2.2.2
instance coverMap_separated : IsSeparated (coverMap R a N B) :=
  (coverMap_properties R a N B).2.2.1

theorem finite_factor : coverMap R a N B =
    Spec.map (CommRingCat.ofHom (finitePolynomialMap R a N B)) ≫ JLineAtlas318.chart R 1 := by
  unfold coverMap baseOpen finitePolynomialMap
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

theorem baseOpen_at_infinity : baseOpen R a N =
    Spec.map (CommRingCat.ofHom (reciprocalPolynomial R a N)) ≫ JLineAtlas318.chart R 0 := by
  have he : (Polynomial.aeval (↑(tUnit R a N) : FiniteBase R a N)).toRingHom =
      algebraMap R[X] (FiniteBase R a N) := by
    apply Polynomial.ringHom_ext
    · intro r
      simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Polynomial.aeval_C]
      exact IsScalarTower.algebraMap_apply R R[X] (FiniteBase R a N) r
    · simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Polynomial.aeval_X]
        using tUnit_coe R a N
  have e := JLineOverlap318.unit_chart_overlap (R := R) (tUnit R a N)
  rw [he] at e
  exact e

theorem reciprocal_factor : coverMap R a N B =
    Spec.map (CommRingCat.ofHom (reciprocalPolynomialMap R a N B)) ≫ JLineAtlas318.chart R 0 := by
  have he : reciprocalPolynomialMap R a N B =
      (algebraMap (FiniteBase R a N) B).comp (reciprocalPolynomial R a N) := by
    ext p
    change algebraMap (FiniteBase R a N) B
      (backward R a N (algebraMap R[X] (ReciprocalBase R a N) p)) = _
    rw [backward_map]
    rfl
  rw [he, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  exact congrArg (fun g => Spec.map (CommRingCat.ofHom
    (algebraMap (FiniteBase R a N) B)) ≫ g) (baseOpen_at_infinity R a N)

abbrev model : Scheme := (coverMap R a N B).normalization
@[expose] def sourceOpen : Spec (CommRingCat.of B) ⟶ model R a N B :=
  (coverMap R a N B).toNormalization
@[expose] def modelMap : model R a N B ⟶ ProjectiveJLine318.scheme R :=
  (coverMap R a N B).fromNormalization
@[expose] def structureMap : model R a N B ⟶ Spec (CommRingCat.of R) :=
  modelMap R a N B ≫ ProjectiveJLine318.structureMap R

theorem sourceOpen_open : IsOpenImmersion (sourceOpen R a N B) := by
  letI : LocallyOfFiniteType (coverMap R a N B) := (coverMap_properties R a N B).1
  letI : LocallyQuasiFinite (coverMap R a N B) := (coverMap_properties R a N B).2.1
  exact inferInstanceAs (IsOpenImmersion (coverMap R a N B).toNormalization)
theorem sourceOpen_dense : IsDominant (sourceOpen R a N B) := by
  change IsDominant (coverMap R a N B).toNormalization
  infer_instance
theorem factorization : sourceOpen R a N B ≫ modelMap R a N B = coverMap R a N B :=
  (coverMap R a N B).toNormalization_fromNormalization
theorem model_integral : IsIntegral (model R a N B) := by
  letI : IsIntegral (Spec (CommRingCat.of B)) := inferInstance
  infer_instance

@[expose] def targetCover (j : Fin 2) : (ProjectiveJLine318.scheme R).affineOpens :=
  ⟨JLineAtlas318.chart R j ''ᵁ ⊤, by
    rw [Scheme.Hom.image_top_eq_opensRange]
    exact isAffineOpen_opensRange _⟩
theorem targetCover_covers : (⨆ j, (targetCover R j).1) = ⊤ := by
  simpa only [targetCover, Scheme.Hom.image_top_eq_opensRange, JLineAtlas318.chart_range]
    using JLineAtlas318.standard_opens_cover R

/-- Finiteness is proved on both genuine normalization charts. Inverting N
in the source open does not remove vertical points from the resulting model. -/
theorem normalization_finite (hN : N ≠ 0) : IsFinite (modelMap R a N B) := by
  apply GlobalNormalization318.finite_of_affine_pieces
    (coverMap R a N B) (targetCover R) (targetCover_covers R)
  intro i
  fin_cases i
  · exact ContactGlobalProper318.finite_sections_of_factor
      (CommRingCat.ofHom (reciprocalPolynomialMap R a N B)) (JLineAtlas318.chart R 0)
      (coverMap R a N B) (reciprocal_factor R a N B)
      (by exact (reciprocal_normal_closure R a N B hN).1)
  · exact ContactGlobalProper318.finite_sections_of_factor
      (CommRingCat.ofHom (finitePolynomialMap R a N B)) (JLineAtlas318.chart R 1)
      (coverMap R a N B) (finite_factor R a N B)
      (by exact (finite_normal_closure R a N B hN).1)
theorem proper_model (hN : N ≠ 0) : IsProper (structureMap R a N B) := by
  letI := normalization_finite R a N B hN
  unfold structureMap
  infer_instance

@[expose] def chartRing (j : Fin 2) : CommRingCat :=
  Γ(model R a N B, modelMap R a N B ⁻¹ᵁ (targetCover R j).1)
theorem chart_properties (hN : N ≠ 0) (j : Fin 2) :
    IsDomain (chartRing R a N B j) ∧ IsIntegrallyClosed (chartRing R a N B j) ∧
    IsNoetherianRing (chartRing R a N B j) := by
  fin_cases j
  · exact NormalChart318.properties_of_factor
      (CommRingCat.ofHom (reciprocalPolynomialMap R a N B)) (JLineAtlas318.chart R 0)
      (coverMap R a N B) (reciprocal_factor R a N B)
      (by exact (reciprocal_normal_closure R a N B hN).2)
  · exact NormalChart318.properties_of_factor
      (CommRingCat.ofHom (finitePolynomialMap R a N B)) (JLineAtlas318.chart R 1)
      (coverMap R a N B) (finite_factor R a N B)
      (by exact (finite_normal_closure R a N B hN).2)
@[expose] def sourceCover (j : Fin 2) : (model R a N B).affineOpens :=
  ⟨modelMap R a N B ⁻¹ᵁ (targetCover R j).1, (targetCover R j).2.preimage _⟩
theorem sourceCover_covers : (⨆ j, (sourceCover R a N B j).1) = ⊤ :=
  Scheme.Hom.iSup_preimage_eq_top _ (targetCover_covers R)
theorem noetherian_model (hN : N ≠ 0) : AlgebraicGeometry.IsNoetherian (model R a N B) := by
  apply (isNoetherian_iff_of_finite_iSup_eq_top (sourceCover_covers R a N B)).mpr
  intro j
  exact (chart_properties R a N B hN j).2.2

theorem normal_stalk (hN : N ≠ 0) (x : model R a N B) :
    IsIntegrallyClosed ((model R a N B).presheaf.stalk x) := by
  have hx : x ∈ (⨆ j, (sourceCover R a N B j).1) := by
    rw [sourceCover_covers]
    trivial
  obtain ⟨j,hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  let U := sourceCover R a N B j
  letI : IsDomain Γ(model R a N B,U) := (chart_properties R a N B hN j).1
  letI : IsIntegrallyClosed Γ(model R a N B,U) := (chart_properties R a N B hN j).2.1
  letI := (model R a N B).presheaf.algebra_section_stalk ⟨x,hj⟩
  letI := U.2.isLocalization_stalk ⟨x,hj⟩
  exact isIntegrallyClosed_of_isLocalization _ (U.2.primeIdealOf ⟨x,hj⟩).asIdeal.primeCompl
    (U.2.primeIdealOf ⟨x,hj⟩).asIdeal.primeCompl_le_nonZeroDivisors
end IntegralTwoChartNormalization318
