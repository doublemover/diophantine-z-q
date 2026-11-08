module
public import ContactGlobalNormal318
public import Mathlib.RingTheory.RegularLocalRing.Defs
public section
noncomputable section
namespace ContactGlobalRegular318
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

/-- A normal Noetherian integral closure over a Dedekind base has dimension
at most one by integrality; all its local rings are therefore regular. -/
theorem closure_regular {A B:Type*} [CommRing A] [IsDedekindDomain A]
    [CommRing B] [IsDomain B] [Algebra A B]
    [IsNoetherianRing (integralClosure A B)]
    [IsIntegrallyClosed (integralClosure A B)] : IsRegularRing (integralClosure A B) := by
  let : Ring.DimensionLEOne (integralClosure A B):=
    Ring.DimensionLEOne.of_isIntegral A (integralClosure A B)
  let : IsDedekindDomain (integralClosure A B):=
    { (inferInstance : IsDomain (integralClosure A B)), ‹IsNoetherianRing (integralClosure A B)›,
      ‹Ring.DimensionLEOne (integralClosure A B)›,
      ‹IsIntegrallyClosed (integralClosure A B)› with }
  infer_instance

theorem regular_sections_of_factor {A B:CommRingCat} [IsDedekindDomain A] [IsDomain B]
    {Y:Scheme} (φ:A⟶B) (j:Spec A⟶Y) [IsOpenImmersion j]
    (f:Spec B⟶Y) [QuasiCompact f] [QuasiSeparated f]
    (hf:f=Spec.map φ≫j)
    (hn:letI:=φ.hom.toAlgebra;
      IsIntegrallyClosed (integralClosure A B) ∧ IsNoetherianRing (integralClosure A B)) :
    IsRegularRing Γ(f.normalization,f.fromNormalization⁻¹ᵁ(j ''ᵁ ⊤)) := by
  subst f
  letI:=φ.hom.toAlgebra
  letI:=hn.1
  letI:=hn.2
  letI:=closure_regular (A:=A) (B:=B)
  exact IsRegularRing.of_ringEquiv (NormalChart318.sectionsEquiv φ j).symm

open ContactKummerOrder318
variable (c:Fin 4→ℚˣ)
local instance sourceDomain : IsDomain (OpenOrder c):=ContactKummerOpenDomain318.open_domain c
local instance sourceFinite : Module.Finite OpenBase (OpenOrder c):=(open_finite_free_etale c).1
local instance sourceEtale : Algebra.Etale OpenBase (OpenOrder c):=(open_finite_free_etale c).2.2

theorem regular_chart (j:Fin 2) : IsRegularRing (ContactGlobalNormal318.chartRing c j) := by
  fin_cases j
  · exact regular_sections_of_factor
      (CommRingCat.ofHom (ContactReciprocalCover318.polynomialMap (OpenOrder c))) (JLineAtlas318.chart ℚ 0)
      (ContactProjectiveModel318.coverMap c) (ContactGlobalProper318.reciprocal_factor c)
      (by exact (ContactReciprocalCover318.finite_normal_model (OpenOrder c)).2)
  · apply regular_sections_of_factor
      (CommRingCat.ofHom (ContactGlobalProper318.finitePolynomial c))
      (JLineAtlas318.chart ℚ 1) (ContactProjectiveModel318.coverMap c)
      (ContactGlobalProper318.finite_factor c)
    exact (ContactReciprocalCover318.original_finite_normal_model (OpenOrder c)).2

/-- Every actual stalk of the constructed proper contact model is regular,
including the generic point; no height-one premise is supplied. -/
theorem regular_stalk (x:(ContactProjectiveModel318.coverMap c).normalization) :
    IsRegularLocalRing ((ContactProjectiveModel318.coverMap c).normalization.presheaf.stalk x) := by
  have hx:x∈(⨆j,(ContactGlobalNormal318.sourceCover c j).1) := by
    rw [ContactGlobalNormal318.sourceCover_covers];trivial
  obtain ⟨j,hj⟩:=TopologicalSpace.Opens.mem_iSup.mp hx
  let U:=ContactGlobalNormal318.sourceCover c j
  letI:IsRegularRing Γ((ContactProjectiveModel318.coverMap c).normalization,U):=regular_chart c j
  letI:=(ContactProjectiveModel318.coverMap c).normalization.presheaf.algebra_section_stalk ⟨x,hj⟩
  letI:=U.2.isLocalization_stalk ⟨x,hj⟩
  let p:Ideal Γ((ContactProjectiveModel318.coverMap c).normalization,U):=
    (U.2.primeIdealOf ⟨x,hj⟩).asIdeal
  letI:p.IsPrime:=(U.2.primeIdealOf ⟨x,hj⟩).isPrime
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p)
      ((ContactProjectiveModel318.coverMap c).normalization.presheaf.stalk x)).toRingEquiv
end ContactGlobalRegular318
