module
public import PointedComponent318
public import OpenJComponent318
public section
noncomputable section
namespace ComponentPointFactor318
open CategoryTheory AlgebraicGeometry
open scoped nonZeroDivisors
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {B Ω:Type u} [CommRing B] [Field Ω] (β:B→+*Ω) (e:B) (hβ:β e=1)

@[expose] def pointLift : Localization.Away e→+*Ω :=
  IsLocalization.Away.lift e (g:=β) (by rw [hβ];exact isUnit_one)

theorem pointLift_comp : (pointLift β e hβ).comp (algebraMap B (Localization.Away e))=β := by
  ext b
  exact IsLocalization.Away.lift_eq (S:=Localization.Away e) (g:=β) e (by rw [hβ];exact isUnit_one) b

theorem pointLift_unique (φ:Localization.Away e→+*Ω)
    (hφ:φ.comp (algebraMap B (Localization.Away e))=β) : φ=pointLift β e hβ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers e)
  exact hφ.trans (pointLift_comp β e hβ).symm

/-- The actual field-valued Scheme point factors through the actual component. -/
theorem scheme_point_factor :
    Spec.map (CommRingCat.ofHom (pointLift β e hβ)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away e)))=
        Spec.map (CommRingCat.ofHom β) := by
  rw [←Spec.map_comp]
  exact congrArg (fun f=>Spec.map (CommRingCat.ofHom f)) (pointLift_comp β e hβ)
end ComponentPointFactor318

namespace PointedOpenJ318
open CategoryTheory AlgebraicGeometry
open scoped nonZeroDivisors
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
variable (N:ℕ) (B Ω:Type) [CommRing B] [Field Ω]
  [Algebra (OpenJModel318.Base N) B] [Module.Finite (OpenJModel318.Base N) B]
  [Algebra.Etale (OpenJModel318.Base N) B]

theorem exists_component (hN:N≠0) (β:B→+*Ω) :
    ∃e:B, IsIdempotentElem e ∧ β e=1 ∧ IsDomain (Localization.Away e) ∧
      Module.Finite (OpenJModel318.Base N) (Localization.Away e) ∧
      Algebra.Etale (OpenJModel318.Base N) (Localization.Away e) := by
  have hd:=OpenJNormalModel318.denominator_ne_zero N hN
  letI:IsDomain (OpenJModel318.Base N):=IsLocalization.Away.isDomain _ hd
  letI:IsIntegrallyClosed (OpenJModel318.Base N):=
    isIntegrallyClosed_of_isLocalization _ (Submonoid.powers (OpenJModel318.denominator N))
      (by rintro x ⟨n,rfl⟩;exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n hd))
  exact PointedComponent318.exists_component_through (OpenJModel318.Base N) B
    (FractionRing (OpenJModel318.Base N)) Ω β

/-- The same component through the given point has the constructed proper
flat surjective integral model; no component choice is supplied. -/
theorem exists_pointed_model (hN:N≠0) (β:B→+*Ω) :
    ∃e:B, IsIdempotentElem e ∧ β e=1 ∧
      ∃(hD:IsDomain (Localization.Away e))
        (hF:Module.Finite (OpenJModel318.Base N) (Localization.Away e))
        (hE:Algebra.Etale (OpenJModel318.Base N) (Localization.Away e)),
      letI:=hD; letI:=hF; letI:=hE;
      IsIntegral (OpenJProjectiveMap318.coverMap N (Localization.Away e)).normalization ∧
      IsProper (ArithmeticJModel318.structureMap N (Localization.Away e)) ∧
      Flat (ArithmeticJModel318.structureMap N (Localization.Away e)) ∧
      Surjective (ArithmeticJModel318.structureMap N (Localization.Away e)) := by
  obtain ⟨e,he,hβ,hD,hF,hE⟩:=exists_component N B Ω hN β
  refine ⟨e,he,hβ,hD,hF,hE,?_⟩
  letI:=hD;letI:=hF;letI:=hE
  exact ⟨inferInstance,ArithmeticJModel318.proper_flat_surjective N (Localization.Away e) hN⟩
end PointedOpenJ318
