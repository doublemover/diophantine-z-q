module

public import OriginalYuanMarkedSectionEvaluation318
public import OriginalYuanAtPlaceFiniteProducer318

@[expose] public section
noncomputable section

namespace OriginalYuanActualFiniteSectionPayment318

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
open NumberField SectionHeight318
open OriginalMarkedTraitAffineSectionPull318
open OriginalYuanMarkedSectionEvaluation318 OriginalYuanPulledExactKSImage318
open OriginalYuanAtPlaceFiniteProducer318 OriginalExactLocalKSUnit318
open OriginalRetainedComplexZeroByPasting318 (specOf)

universe u

variable {E : Type u} [Field E] [NumberField E] (w : FinitePlace E)
local notation "V" => localRing w

/-- The v1.1 ring is a localization **inside** E rather than a
canonical Localization.AtPrime type. Use its actual local-ring proof. -/
instance actualHeldLocalRing : IsLocalRing V := by
  let P := (FinitePlace.maximalIdeal w).asIdeal
  letI : IsLocalization.AtPrime V P :=
    Localization.subalgebra.isLocalization_subalgebra E P.primeCompl
      P.primeCompl_le_nonZeroDivisors
  exact IsLocalization.AtPrime.isLocalRing V P

variable {Y : Scheme.{u}} (U : Y.Opens) (hU : IsAffineOpen U)
variable (centre : Spec (CommRingCat.of V) ⟶ Y)
variable (closed : centre (IsLocalRing.closedPoint V)∈U)
local notation "A" => chartRing U

/-- The scalars are obtained from the exact pulled model, not
from a separately postulated R-algebra map. -/
def actualScalar : Algebra A V := (eval U hU centre closed).toAlgebra

local instance : Algebra A V := actualScalar w U hU centre closed

abbrev toHeldField : V→+*E := (localRing w).val.toRingHom

variable (retained : Spec (CommRingCat.of E) ⟶ Y)
variable (onOldMark : specOf (toHeldField w) ≫ centre=retained)

include onOldMark in
theorem generic_section_factor_is_held :
    specOf (genericEval U hU centre closed (toHeldField w)) ≫ hU.fromSpec=retained :=
  realizes_old_mark U hU centre closed (toHeldField w) retained onOldMark

variable {N : Type u} [AddCommGroup N] [Module A N]
variable (λ₂ : N) (b : E)
variable (δ : (V⊗[A]N) ≃ₗ[V]coeffLine (R:=V) b)
variable (λ_read : (δ ((1:V)⊗ₜ[A]λ₂):E)=b)

def pullSection (s : A) : V⊗[A]N := (1:V)⊗ₜ[A](s • λ₂)

include λ_read in
theorem tensor_is_actual_scalar_times_frame (s : A) :
    (δ (pullSection w U hU centre closed λ₂ s):E)=
      toHeldField w (eval U hU centre closed s)*b := by
  have h : pullSection w U hU centre closed λ₂ s=
      (eval U hU centre closed s) • ((1:V)⊗ₜ[A]λ₂) := by
    unfold pullSection
    rw [TensorProduct.tmul_smul]
    change ((eval U hU centre closed s)*1) ⊗ₜ[A] λ₂ = _
    simp only [mul_one,TensorProduct.smul_tmul',smul_eq_mul]
  rw [h,map_smul]
  change toHeldField w (eval U hU centre closed s)*
    (δ ((1:V)⊗ₜ[A]λ₂):E)=_
  rw [λ_read]

variable (π : A)
variable (good : IsUnit (genericEval U hU centre closed (toHeldField w) π))
local notation "A₁" => Localization.Away π
variable (sections : Fin 2→A) (tLoc dLoc : A₁)
variable (t : E)
variable (readT : liftEval U hU centre closed (toHeldField w) π good tLoc=t)
variable (noncontact : P t≠0)
variable (firstIdentity : P tLoc*(algebraMap A A₁ (sections 0))=
  (2765952000:A₁)^2*dLoc^2)
variable (secondIdentity : algebraMap A A₁ (sections 1)=
  tLoc*algebraMap A A₁ (sections 0))
variable (coframe : b*(dGeneric U hU centre closed (toHeldField w) π good dLoc)^2=P t)

include λ_read readT noncontact firstIdentity secondIdentity coframe in
/-- Genuine same-model payment in the exact unchanged v1.1 Q
frame. Numerator and ratio are evaluated as functions on the
same original marked affine using the actual scheme arrow. -/
theorem literal_pair_paid (C : FrameNorms E) (hb : b≠0)
    (normRead : C.finiteNorm w=(w b)⁻¹) (i : Fin 2) :
    w (![(2765952000:E)^2,t*(2765952000:E)^2] i)*C.finiteNorm w≤1 := by
  apply exact_place_paid_pair w C b hb normRead δ
    (fun j=>pullSection w U hU centre closed λ₂ (sections j)) t
  intro j
  rw [tensor_is_actual_scalar_times_frame w U hU centre closed λ₂ b δ λ_read]
  exact actual_original_Q_pair U hU centre closed (toHeldField w) π good sections
    tLoc dLoc t readT noncontact firstIdentity secondIdentity b coframe j

end OriginalYuanActualFiniteSectionPayment318
