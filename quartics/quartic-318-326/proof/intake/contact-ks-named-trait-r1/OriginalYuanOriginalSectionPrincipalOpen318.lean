module

public import OriginalYuanMarkedSectionEvaluation318
public import OriginalActualStalkSpreadDenominators318
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic.FinCases

@[expose] public section
noncomputable section

namespace OriginalYuanOriginalSectionPrincipalOpen318

open scoped nonZeroDivisors
open OriginalYuanMarkedSectionEvaluation318
open OriginalActualStalkSpreadDenominators318

variable {A K E : Type*} [CommRing A] [IsDomain A] [Field K] [Field E]
  [Algebra A K] [IsFractionRing A K]
variable (eval : A→+*E)

abbrev p := RingHom.ker eval
local instance : (p eval).IsPrime := RingHom.ker_isPrime eval
abbrev Stalk := Localization.AtPrime (p eval)

theorem point_unit (s : (p eval).primeCompl) : IsUnit (eval (s:A)) :=
  isUnit_iff_ne_zero.mpr (fun h=>s.property ((RingHom.mem_ker).2 h))

def pointRead : Stalk eval→+*E :=
  IsLocalization.lift (M:=(p eval).primeCompl) (g:=eval) (point_unit eval)

def structuralRead : Stalk eval→+*K :=
  IsLocalization.lift (M:=(p eval).primeCompl) (g:=algebraMap A K) (fun s=>
    isUnit_iff_ne_zero.mpr
      (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K:=K)
        ((p eval).primeCompl_le_nonZeroDivisors s.property)))

theorem structural_read_injective : Function.Injective (structuralRead (K:=K) eval) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq (p eval).primeCompl
    (structuralRead (K:=K) eval)).2
  intro a b
  change _ = _ ↔
    structuralRead (K:=K) eval (algebraMap A (Stalk eval) a) =
    structuralRead (K:=K) eval (algebraMap A (Stalk eval) b)
  rw [structuralRead,IsLocalization.lift_eq,IsLocalization.lift_eq]
  exact (IsLocalization.injective (Stalk eval) (p eval).primeCompl_le_nonZeroDivisors).eq_iff.trans
    (IsFractionRing.injective A K).eq_iff.symm

theorem restriction_keeps_point (π : A) (hπ : π∈(p eval).primeCompl) :
    (pointRead eval).comp (toStalk (p eval) π hπ).toRingHom =
      IsLocalization.Away.lift π (g:=eval) (point_unit eval ⟨π,hπ⟩) := by
  apply IsLocalization.ringHom_ext (.powers π)
  ext a
  change pointRead eval ((toStalk (p eval) π hπ) (algebraMap A _ a)) =
    IsLocalization.Away.lift π (g:=eval) (point_unit eval ⟨π,hπ⟩) (algebraMap A _ a)
  rw [AlgHom.commutes,pointRead,IsLocalization.lift_eq,IsLocalization.Away.lift_eq]

/-- Produce one actual principal neighbourhood of the same E-mark
and the whole, denominator-cleared old pair there. The generic
functions T and dT live in the displayed structural stalk. No
homomorphism K→E is ever requested. -/
theorem source_to_named_principal_open (T dT : Stalk eval) (s : Fin 2→A)
    (wholeNum : P (structuralRead (K:=K) eval T)*algebraMap A K (s 0)=
      (2765952000:K)^2*(structuralRead (K:=K) eval dT)^2)
    (wholeRatio : algebraMap A K (s 1)=
      structuralRead (K:=K) eval T*algebraMap A K (s 0)) :
    ∃ (π : A) (hπ : π∈(p eval).primeCompl) (tLoc dLoc : Localization.Away π),
      (IsLocalization.Away.lift π (g:=eval) (point_unit eval ⟨π,hπ⟩) tLoc=
        pointRead eval T) ∧
      (IsLocalization.Away.lift π (g:=eval) (point_unit eval ⟨π,hπ⟩) dLoc=
        pointRead eval dT) ∧
      (P tLoc*algebraMap A (Localization.Away π) (s 0)=(2765952000:Localization.Away π)^2*dLoc^2) ∧
      (algebraMap A (Localization.Away π) (s 1)=tLoc*algebraMap A (Localization.Away π) (s 0)) := by
  obtain ⟨π,hπ,f,hf⟩ := actual_finite_denominators (Q:=Stalk eval) (p eval)
    (![T,dT] : Fin 2→Stalk eval)
  let into := toStalk (p eval) π hπ
  have eT : into (f 0)=T := hf 0
  have ed : into (f 1)=dT := hf 1
  have inj : Function.Injective (structuralRead (K:=K) eval ∘ into) :=
    (structural_read_injective (K:=K) eval).comp (toStalk_injective (p eval) π hπ)
  have eval_restrict (z : Localization.Away π) :
      IsLocalization.Away.lift π (g:=eval) (point_unit eval ⟨π,hπ⟩) z=
        pointRead eval (into z) :=
    (RingHom.congr_fun (restriction_keeps_point eval π hπ) z).symm
  refine ⟨π,hπ,f 0,f 1,?_,?_,?_,?_⟩
  · rw [eval_restrict,eT]
  · rw [eval_restrict,ed]
  · apply inj
    change structuralRead (K:=K) eval (into _) = structuralRead (K:=K) eval (into _)
    simpa only [map_mul,map_pow,map_ofNat,maps_P,AlgHom.commutes,into,structuralRead,
      IsLocalization.lift_eq,hf] using wholeNum
  · apply inj
    change structuralRead (K:=K) eval (into _) = structuralRead (K:=K) eval (into _)
    simpa only [map_mul,AlgHom.commutes,into,structuralRead,IsLocalization.lift_eq,hf] using wholeRatio

end OriginalYuanOriginalSectionPrincipalOpen318
