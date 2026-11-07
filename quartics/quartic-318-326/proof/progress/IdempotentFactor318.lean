module
public import GenericIdempotent318
public section
noncomputable section
namespace IdempotentFactor318
open Algebra
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {B:Type u} [CommRing B] {I:Type u} [DecidableEq I]
  (L:I→Type u) [∀i,Field (L i)]
  (φ:B→+*∀i,L i) (i:I) (e:B)
  (he:IsIdempotentElem e) (hφe:φ e=Pi.single i 1)

@[expose] def factor : Localization.Away e →+* L i :=
  IsLocalization.Away.lift e (g:=(Pi.evalRingHom L i).comp φ) (by
    have h:(Pi.evalRingHom L i).comp φ e=1:=by simp [hφe]
    rw [h];exact isUnit_one)

theorem factor_coeff (b:B) : factor L φ i e hφe (algebraMap B (Localization.Away e) b)=φ b i :=
  IsLocalization.Away.lift_eq e _ b

include he in
/-- Localizing the descended primitive idempotent embeds in its actual
chosen generic field factor. -/
theorem factor_injective (hφ:Function.Injective φ) :
    Function.Injective (factor L φ i e hφe) := by
  intro x y hxy
  obtain ⟨b,rfl⟩:=IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem e he x
  obtain ⟨c,rfl⟩:=IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem e he y
  rw [factor_coeff,factor_coeff] at hxy
  have hbc:e*b=e*c := hφ (by
    ext j
    by_cases hji:j=i
    · subst j;simpa [map_mul,hφe] using hxy
    · simp [map_mul,hφe,hji])
  have hl:=congrArg (algebraMap B (Localization.Away e)) hbc
  simp only [map_mul] at hl
  exact (IsLocalization.Away.algebraMap_isUnit e).mul_left_cancel hl

include i he hφe in
theorem component_domain (hφ:Function.Injective φ) : IsDomain (Localization.Away e) :=
  Function.Injective.isDomain (factor L φ i e hφe) (factor_injective L φ i e he hφe hφ)

section Base
variable (R:Type u) [CommRing R] [Algebra R B] [Module.Finite R B] [Algebra.Etale R B]

include he in
/-- The actual selected component is still finite over the original base. -/
theorem component_finite : Module.Finite R (Localization.Away e) := by
  letI:Module.Finite B (Localization.Away e):=
    Module.Finite.of_surjective (Algebra.linearMap B (Localization.Away e))
      (IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem e he)
  exact Module.Finite.trans B (Localization.Away e)

/-- Its etaleness is supplied by the actual idempotent localization map. -/
theorem component_etale : Algebra.Etale R (Localization.Away e) := by
  infer_instance
end Base
end IdempotentFactor318
