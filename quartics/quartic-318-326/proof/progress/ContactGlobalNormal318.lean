module
public import ContactGlobalProper318
public import NormalChart318
public section
noncomputable section
namespace ContactGlobalNormal318
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open ContactKummerOrder318
variable (c:Fin 4→ℚˣ)
local instance sourceDomain : IsDomain (OpenOrder c):=ContactKummerOpenDomain318.open_domain c
local instance sourceFinite : Module.Finite OpenBase (OpenOrder c):=(open_finite_free_etale c).1
local instance sourceEtale : Algebra.Etale OpenBase (OpenOrder c):=(open_finite_free_etale c).2.2

@[expose] def chartRing (j:Fin 2) : CommRingCat :=
  Γ((ContactProjectiveModel318.coverMap c).normalization,
    (ContactProjectiveModel318.coverMap c).fromNormalization⁻¹ᵁ
      (ContactGlobalProper318.targetCover j).1)

/-- These are the actual affine rings of the actual proper normalization,
not separately chosen integral orders. -/
theorem chart_properties (j:Fin 2) :
    IsDomain (chartRing c j) ∧ IsIntegrallyClosed (chartRing c j) ∧
      IsNoetherianRing (chartRing c j) := by
  fin_cases j
  · exact NormalChart318.properties_of_factor
      (CommRingCat.ofHom (ContactReciprocalCover318.polynomialMap (OpenOrder c))) (JLineAtlas318.chart ℚ 0)
      (ContactProjectiveModel318.coverMap c) (ContactGlobalProper318.reciprocal_factor c)
      (by exact (ContactReciprocalCover318.finite_normal_model (OpenOrder c)).2)
  · apply NormalChart318.properties_of_factor
      (CommRingCat.ofHom (ContactGlobalProper318.finitePolynomial c))
      (JLineAtlas318.chart ℚ 1) (ContactProjectiveModel318.coverMap c)
      (ContactGlobalProper318.finite_factor c)
    exact (ContactReciprocalCover318.original_finite_normal_model (OpenOrder c)).2

@[expose] def sourceCover (j:Fin 2) :
    (ContactProjectiveModel318.coverMap c).normalization.affineOpens :=
  ⟨(ContactProjectiveModel318.coverMap c).fromNormalization⁻¹ᵁ
      (ContactGlobalProper318.targetCover j).1,
    (ContactGlobalProper318.targetCover j).2.preimage _⟩

theorem sourceCover_covers : (⨆j,(sourceCover c j).1)=⊤ :=
  Scheme.Hom.iSup_preimage_eq_top _ ContactGlobalProper318.targetCover_covers

/-- The constructed proper integral model is an actual Noetherian scheme. -/
theorem noetherian_model :
    AlgebraicGeometry.IsNoetherian (ContactProjectiveModel318.coverMap c).normalization := by
  apply (isNoetherian_iff_of_finite_iSup_eq_top (sourceCover_covers c)).mpr
  intro j
  exact (chart_properties c j).2.2

/-- Normality holds at every actual scheme stalk, not just in abstract chart orders. -/
theorem normal_stalk (x:(ContactProjectiveModel318.coverMap c).normalization) :
    IsIntegrallyClosed ((ContactProjectiveModel318.coverMap c).normalization.presheaf.stalk x) := by
  have hx : x∈(⨆j,(sourceCover c j).1) := by rw [sourceCover_covers]; trivial
  obtain ⟨j,hj⟩:=TopologicalSpace.Opens.mem_iSup.mp hx
  let U:=sourceCover c j
  letI:IsDomain Γ((ContactProjectiveModel318.coverMap c).normalization,U):=
    (chart_properties c j).1
  letI:IsIntegrallyClosed Γ((ContactProjectiveModel318.coverMap c).normalization,U):=
    (chart_properties c j).2.1
  letI:=(ContactProjectiveModel318.coverMap c).normalization.presheaf.algebra_section_stalk ⟨x,hj⟩
  letI:=U.2.isLocalization_stalk ⟨x,hj⟩
  exact isIntegrallyClosed_of_isLocalization _ (U.2.primeIdealOf ⟨x,hj⟩).asIdeal.primeCompl
    (U.2.primeIdealOf ⟨x,hj⟩).asIdeal.primeCompl_le_nonZeroDivisors

theorem noetherian_stalk (x:(ContactProjectiveModel318.coverMap c).normalization) :
    IsNoetherianRing ((ContactProjectiveModel318.coverMap c).normalization.presheaf.stalk x) := by
  letI:=noetherian_model c
  infer_instance

end ContactGlobalNormal318
