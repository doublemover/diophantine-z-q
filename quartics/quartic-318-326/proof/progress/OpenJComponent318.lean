module
public import EtaleDomainComponent318
public import ArithmeticJModel318
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public section
noncomputable section
namespace OpenJComponent318
open CategoryTheory AlgebraicGeometry
open scoped nonZeroDivisors
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
variable (N:ℕ) (B:Type) [CommRing B] [Nontrivial B]
  [Algebra (OpenJModel318.Base N) B] [Module.Finite (OpenJModel318.Base N) B]
  [Algebra.Etale (OpenJModel318.Base N) B]

/-- The selected localization is an actual open and closed subscheme of the
original cover, not only an abstract domain algebra. -/
theorem component_open_closed (e:B) (he:IsIdempotentElem e) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away e)))) ∧
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away e)))) :=
  ⟨IsOpenImmersion.of_isLocalization e,
    IsClosedImmersion.spec_of_surjective _
      (IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem e he)⟩

/-- The literal open-j cover need not have a supplied domain structure:
an actual finite-etale domain component is constructed. -/
theorem exists_component (hN:N≠0) :
    ∃e:B, IsIdempotentElem e ∧ IsDomain (Localization.Away e) ∧
      Module.Finite (OpenJModel318.Base N) (Localization.Away e) ∧
      Algebra.Etale (OpenJModel318.Base N) (Localization.Away e) := by
  have hd:=OpenJNormalModel318.denominator_ne_zero N hN
  letI:IsDomain (OpenJModel318.Base N):=IsLocalization.Away.isDomain _ hd
  letI:IsIntegrallyClosed (OpenJModel318.Base N):=
    isIntegrallyClosed_of_isLocalization _ (Submonoid.powers (OpenJModel318.denominator N))
      (by rintro x ⟨n,rfl⟩;exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n hd))
  exact EtaleDomainComponent318.exists_domain_component (OpenJModel318.Base N) B
    (FractionRing (OpenJModel318.Base N))

/-- The chosen component has its genuine proper flat surjective integral
model. Only the nonzero finite-etale cover remains as source input. -/
theorem exists_component_model (hN:N≠0) :
    ∃e:B, IsIdempotentElem e ∧
      ∃(hD:IsDomain (Localization.Away e))
        (hF:Module.Finite (OpenJModel318.Base N) (Localization.Away e))
        (hE:Algebra.Etale (OpenJModel318.Base N) (Localization.Away e)),
      letI:=hD; letI:=hF; letI:=hE;
      IsIntegral (OpenJProjectiveMap318.coverMap N (Localization.Away e)).normalization ∧
      IsProper (ArithmeticJModel318.structureMap N (Localization.Away e)) ∧
      Flat (ArithmeticJModel318.structureMap N (Localization.Away e)) ∧
      Surjective (ArithmeticJModel318.structureMap N (Localization.Away e)) := by
  obtain ⟨e,he,hD,hF,hE⟩:=exists_component N B hN
  refine ⟨e,he,hD,hF,hE,?_⟩
  letI:=hD;letI:=hF;letI:=hE
  exact ⟨inferInstance,ArithmeticJModel318.proper_flat_surjective N (Localization.Away e) hN⟩
end OpenJComponent318
