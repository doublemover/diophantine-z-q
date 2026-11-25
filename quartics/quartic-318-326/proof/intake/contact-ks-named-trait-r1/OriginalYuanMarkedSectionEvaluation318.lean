module

public import OriginalMarkedTraitAffineSectionPull318
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Tactic.FinCases

@[expose] public section
noncomputable section

namespace OriginalYuanMarkedSectionEvaluation318

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
open OriginalMarkedTraitAffineSectionPull318

universe u

def P {R : Type*} [CommRing R] (t : R) : R := t*(t-32)*(t-76832)*(t+343)

lemma maps_P {R S : Type*} [CommRing R] [CommRing S] (f : R→+*S) (t : R) :
    f (P t)=P (f t) := by simp only [P,map_mul,map_add,map_sub,map_ofNat]

variable {V E : Type u} [CommRing V] [IsLocalRing V] [Field E]
variable {Y : Scheme.{u}} (U : Y.Opens) (hU : IsAffineOpen U)
variable (m : Spec (CommRingCat.of V) ⟶ Y)
variable (closed : m (IsLocalRing.closedPoint V)∈U)
variable (tau : V→+*E)
variable (π : chartRing U)
variable (good : IsUnit (genericEval U hU m closed tau π))

/-- Freeze the true localisation map's full dependent types before
coercing it to an evaluation function. -/
def markedLocalization : (Localization.Away π) →+* E :=
  @OriginalMarkedTraitAffineSectionPull318.liftEval V E _ _ _ Y U hU m closed tau π good

/-- Checked outside the dependent ChartRing/Localization context:
it exposes the generic function of the exact already-typed ring hom. -/
def markedRingFunction {S K : Type u} [CommRing S] [CommRing K] (f : S→+*K) : S→K :=
  fun a => f a

/-- The coefficient of the relative \(dT\) in the chosen original
dualizing frame, still carried through the same fine-point ring
hom. This never evaluates a function field into E. -/
def dGeneric : Localization.Away π → E :=
  @markedRingFunction (Localization.Away π) E _ _
    (@markedLocalization V E _ _ _ Y U hU m closed tau π good)

variable (sections : Fin 2→chartRing U) (tLoc dLoc : Localization.Away π)
variable (t : E)
variable (readT : dGeneric U hU m closed tau π good tLoc=t)
variable (noncontact : P t≠0)

-- Denominator-cleared original section identities on the literal principal
-- open, before reading the marked coefficients. No localized unit in V.
variable (firstIdentity : P tLoc*(algebraMap (chartRing U) (Localization.Away π) (sections 0))=
  (2765952000:(Localization.Away π))^2*dLoc^2)
variable (secondIdentity : algebraMap (chartRing U) (Localization.Away π) (sections 1)=
  tLoc*algebraMap (chartRing U) (Localization.Away π) (sections 0))

abbrev readCoeff (i : Fin 2) : E := tau (eval U hU m closed (sections i))

include readT firstIdentity in
theorem true_evaluated_numerator :
    P t*(readCoeff U hU m closed tau sections 0)=
      (2765952000:E)^2*(dGeneric U hU m closed tau π good dLoc)^2 := by
  let f : (Localization.Away π) →+* E :=
    @markedLocalization V E _ _ _ Y U hU m closed tau π good
  have ht : f tLoc = t := readT
  have hs : f (algebraMap (chartRing U) (Localization.Away π) (sections 0)) =
      readCoeff U hU m closed tau sections 0 :=
    @liftEval_read V E _ _ _ Y U hU m closed tau π good (sections 0)
  have h := congrArg (fun x : (Localization.Away π) => f x) firstIdentity
  simpa only [map_mul,maps_P,map_pow,map_ofNat,ht,hs] using h

include readT secondIdentity in
theorem true_evaluated_ratio :
    readCoeff U hU m closed tau sections 1=t*(readCoeff U hU m closed tau sections 0) := by
  let f : (Localization.Away π) →+* E :=
    @markedLocalization V E _ _ _ Y U hU m closed tau π good
  have ht : f tLoc = t := readT
  have hs (i : Fin 2) : f (algebraMap (chartRing U) (Localization.Away π) (sections i)) =
      readCoeff U hU m closed tau sections i :=
    @liftEval_read V E _ _ _ Y U hU m closed tau π good (sections i)
  have h := congrArg (fun x : (Localization.Away π) => f x) secondIdentity
  simpa only [map_mul,hs,ht] using h

variable (b : E)
variable (frameRead : b*(dGeneric U hU m closed tau π good dLoc)^2=P t)

include readT noncontact firstIdentity secondIdentity frameRead in
/-- Put the two actually evaluated integral coefficients in the
fixed Q-frame. Here b is the coordinate of the carried primitive
dualizing-square frame relative to Q, not a free rescaling of
the sections. -/
theorem actual_original_Q_pair (i : Fin 2) :
    (readCoeff U hU m closed tau sections i)*b =
      ![(2765952000:E)^2,t*(2765952000:E)^2] i := by
  have h0 : readCoeff U hU m closed tau sections 0*b=(2765952000:E)^2 := by
    apply mul_left_cancel₀ noncontact
    calc
      _ = (P t*readCoeff U hU m closed tau sections 0)*b := (mul_assoc _ _ _).symm
      _ = ((2765952000:E)^2*(dGeneric U hU m closed tau π good dLoc)^2)*b := by
        rw [true_evaluated_numerator U hU m closed tau π good sections tLoc dLoc t readT firstIdentity]
      _ = (b*(dGeneric U hU m closed tau π good dLoc)^2)*(2765952000:E)^2 := by ac_rfl
      _ = _ := by rw [frameRead]
  fin_cases i
  · exact h0
  · change readCoeff U hU m closed tau sections 1*b=t*(2765952000:E)^2
    rw [true_evaluated_ratio U hU m closed tau π good sections tLoc t readT secondIdentity,
      mul_assoc,h0]

end OriginalYuanMarkedSectionEvaluation318
