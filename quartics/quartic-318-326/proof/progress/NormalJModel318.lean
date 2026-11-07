module
public import NormalChart318
public section
noncomputable section
namespace NormalJModel318
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ) (B:Type) [CommRing B] [IsDomain B]
  [Algebra (OpenJModel318.Base N) B] [Module.Finite (OpenJModel318.Base N) B]
  [Algebra.Etale (OpenJModel318.Base N) B]

@[expose] def chartRing (j:Fin 2) : CommRingCat :=
  Γ((OpenJProjectiveMap318.coverMap N B).normalization,
    (OpenJProjectiveMap318.coverMap N B).fromNormalization⁻¹ᵁ
      (ProperOpenJNormalization318.targetCover j).1)

/-- These are the actual affine rings of the actual proper normalization,
not separately chosen integral orders. -/
theorem chart_properties (hN:N≠0) (j:Fin 2) :
    IsDomain (chartRing N B j) ∧ IsIntegrallyClosed (chartRing N B j) ∧
      IsNoetherianRing (chartRing N B j) := by
  fin_cases j
  · exact NormalChart318.properties_of_factor
      (CommRingCat.ofHom (ReciprocalCover318.polynomialMap N B)) (JLineAtlas318.chart ℤ 0)
      (OpenJProjectiveMap318.coverMap N B) (ReciprocalProjective318.coverMap_infinity N B)
      (by exact (ReciprocalCover318.finite_normal_model N B hN).2)
  · apply NormalChart318.properties_of_factor
      (CommRingCat.ofHom (ProperOpenJNormalization318.finitePolynomial N B))
      (JLineAtlas318.chart ℤ 1) (OpenJProjectiveMap318.coverMap N B)
      (ProperOpenJNormalization318.finite_factor N B)
    letI:=(ProperOpenJNormalization318.finitePolynomial N B).toAlgebra
    letI:IsScalarTower (Polynomial ℤ) (OpenJModel318.Base N) B:=
      IsScalarTower.of_algebraMap_eq (fun _=>rfl)
    exact (OpenJNormalModel318.actual_finite_normal_model N B hN).2

@[expose] def sourceCover (j:Fin 2) :
    (OpenJProjectiveMap318.coverMap N B).normalization.affineOpens :=
  ⟨(OpenJProjectiveMap318.coverMap N B).fromNormalization⁻¹ᵁ
      (ProperOpenJNormalization318.targetCover j).1,
    (ProperOpenJNormalization318.targetCover j).2.preimage _⟩

theorem sourceCover_covers : (⨆j,(sourceCover N B j).1)=⊤ :=
  Scheme.Hom.iSup_preimage_eq_top _ ProperOpenJNormalization318.targetCover_covers

/-- The constructed proper integral model is an actual Noetherian scheme. -/
theorem noetherian_model (hN:N≠0) :
    AlgebraicGeometry.IsNoetherian (OpenJProjectiveMap318.coverMap N B).normalization := by
  apply (isNoetherian_iff_of_finite_iSup_eq_top (sourceCover_covers N B)).mpr
  intro j
  exact (chart_properties N B hN j).2.2

/-- Normality holds at every actual scheme stalk, not just in abstract chart orders. -/
theorem normal_stalk (hN:N≠0) (x:(OpenJProjectiveMap318.coverMap N B).normalization) :
    IsIntegrallyClosed ((OpenJProjectiveMap318.coverMap N B).normalization.presheaf.stalk x) := by
  have hx : x∈(⨆j,(sourceCover N B j).1) := by rw [sourceCover_covers]; trivial
  obtain ⟨j,hj⟩:=TopologicalSpace.Opens.mem_iSup.mp hx
  let U:=sourceCover N B j
  letI:IsDomain Γ((OpenJProjectiveMap318.coverMap N B).normalization,U):=
    (chart_properties N B hN j).1
  letI:IsIntegrallyClosed Γ((OpenJProjectiveMap318.coverMap N B).normalization,U):=
    (chart_properties N B hN j).2.1
  letI:=(OpenJProjectiveMap318.coverMap N B).normalization.presheaf.algebra_section_stalk ⟨x,hj⟩
  letI:=U.2.isLocalization_stalk ⟨x,hj⟩
  exact isIntegrallyClosed_of_isLocalization _ (U.2.primeIdealOf ⟨x,hj⟩).asIdeal.primeCompl
    (U.2.primeIdealOf ⟨x,hj⟩).asIdeal.primeCompl_le_nonZeroDivisors

theorem noetherian_stalk (hN:N≠0) (x:(OpenJProjectiveMap318.coverMap N B).normalization) :
    IsNoetherianRing ((OpenJProjectiveMap318.coverMap N B).normalization.presheaf.stalk x) := by
  letI:=noetherian_model N B hN
  infer_instance

end NormalJModel318
