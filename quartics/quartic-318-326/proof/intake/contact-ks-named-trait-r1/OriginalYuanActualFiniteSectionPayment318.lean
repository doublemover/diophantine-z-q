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

/-- The v1.1 ring is a localization **inside** E rather than a
canonical Localization.AtPrime type. Use its actual local-ring proof. -/
instance actualHeldLocalRing : IsLocalRing (localRing w) := by
  let P := (FinitePlace.maximalIdeal w).asIdeal
  letI : IsLocalization.AtPrime (localRing w) P :=
    Localization.subalgebra.isLocalization_subalgebra E P.primeCompl
      P.primeCompl_le_nonZeroDivisors
  exact IsLocalization.AtPrime.isLocalRing (localRing w) P

/-- Freeze the ordinary Scheme closed-point application before
specialising V to the dependent actual local subalgebra of E. -/
def imageOfClosed {D : Type u} [CommRing D] [IsLocalRing D] {Y : Scheme.{u}}
    (c : Spec (CommRingCat.of D) ⟶ Y) : Y :=
  c (IsLocalRing.closedPoint D)

variable {Y : Scheme.{u}} (U : Y.Opens) (hU : IsAffineOpen U)
variable (centre : Spec (CommRingCat.of (localRing w)) ⟶ Y)
variable (closed : @imageOfClosed (localRing w) _ _ Y centre∈U)

def evaluation : chartRing U→+* (localRing w) :=
  @OriginalMarkedTraitAffineSectionPull318.eval (localRing w) _ _ Y U hU centre closed

/-- The scalars are obtained from the exact pulled model, not
from a separately postulated R-algebra map. -/
def actualScalar : Algebra (chartRing U) (localRing w) :=
  (@evaluation E _ _ w Y U hU centre closed).toAlgebra

abbrev toHeldField : (localRing w)→+*E := (localRing w).val.toRingHom

def sameGenericMap : chartRing U→+*E :=
  @OriginalMarkedTraitAffineSectionPull318.genericEval (localRing w) E _ _ _ Y
    U hU centre closed (toHeldField w)

variable (retained : Spec (CommRingCat.of E) ⟶ Y)
variable (onOldMark : specOf (toHeldField w) ≫ centre=retained)

include onOldMark in
theorem generic_section_factor_is_held :
    specOf (@sameGenericMap E _ _ w Y U hU centre closed) ≫ hU.fromSpec=retained :=
  @realizes_old_mark (localRing w) E _ _ _ Y U hU centre closed (toHeldField w) retained onOldMark

variable {N : Type u} [AddCommGroup N] [Module (chartRing U) N]

/-- The module on the actual marked centre. The algebra is stored in
the concrete tensor, not sought as a global instance with an
unrecoverable centre. -/
abbrev ActualTensor (M : Type u) [AddCommGroup M] [Module (chartRing U) M] : Type u :=
  letI : Algebra (chartRing U) (localRing w) := actualScalar w U hU centre closed
  (localRing w) ⊗[chartRing U] M

instance actualTensorModule : Module (localRing w) (ActualTensor w U hU centre closed N) := by
  letI : Algebra (chartRing U) (localRing w) := actualScalar w U hU centre closed
  exact inferInstanceAs (Module (localRing w) ((localRing w) ⊗[chartRing U] N))

variable (frame : N) (b : E)
variable (δ : ActualTensor w U hU centre closed N ≃ₗ[(localRing w)] coeffLine (R:=(localRing w)) b)

def pullFrame : ActualTensor w U hU centre closed N := by
  letI : Algebra (chartRing U) (localRing w) := actualScalar w U hU centre closed
  exact (1:(localRing w)) ⊗ₜ[chartRing U] frame

def pullSection (s : chartRing U) : ActualTensor w U hU centre closed N := by
  letI : Algebra (chartRing U) (localRing w) := actualScalar w U hU centre closed
  exact (1:(localRing w)) ⊗ₜ[chartRing U] (s • frame)

variable (frame_read : (δ (pullFrame w U hU centre closed frame):E)=b)

include frame_read in
theorem tensor_is_actual_scalar_times_frame (s : chartRing U) :
    (δ (pullSection w U hU centre closed frame s):E)=
      toHeldField w ((@evaluation E _ _ w Y U hU centre closed) s)*b := by
  letI : Algebra (chartRing U) (localRing w) := actualScalar w U hU centre closed
  have h : pullSection w U hU centre closed frame s=
      ((@evaluation E _ _ w Y U hU centre closed) s) • pullFrame w U hU centre closed frame := by
    unfold pullSection pullFrame
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    change (((@evaluation E _ _ w Y U hU centre closed) s)*1) ⊗ₜ[chartRing U] frame = _
    simp only [mul_one,TensorProduct.smul_tmul',smul_eq_mul]
  rw [h,map_smul]
  change toHeldField w ((@evaluation E _ _ w Y U hU centre closed) s)*
    (δ (pullFrame w U hU centre closed frame):E)=_
  rw [frame_read]

variable (π : (chartRing U))
variable (good : IsUnit (@sameGenericMap E _ _ w Y U hU centre closed π))
variable (sections : Fin 2→(chartRing U)) (tLoc dLoc : (Localization.Away π))
variable (t : E)
variable (readT : dGeneric U hU centre closed (toHeldField w) π good tLoc=t)
variable (noncontact : P t≠0)
variable (firstIdentity : P tLoc*(algebraMap (chartRing U) (Localization.Away π) (sections 0))=
  (2765952000:(Localization.Away π))^2*dLoc^2)
variable (secondIdentity : algebraMap (chartRing U) (Localization.Away π) (sections 1)=
  tLoc*algebraMap (chartRing U) (Localization.Away π) (sections 0))
variable (coframe : b*(dGeneric U hU centre closed (toHeldField w) π good dLoc)^2=P t)

include frame_read readT noncontact firstIdentity secondIdentity coframe in
/-- Genuine same-model payment in the exact unchanged v1.1 Q
frame. Numerator and ratio are evaluated as functions on the
same original marked affine using the actual scheme arrow. -/
theorem literal_pair_paid (C : FrameNorms E) (hb : b≠0)
    (normRead : C.finiteNorm w=(w b)⁻¹) (i : Fin 2) :
    w (![(2765952000:E)^2,t*(2765952000:E)^2] i)*C.finiteNorm w≤1 := by
  letI : Algebra (chartRing U) (localRing w) := actualScalar w U hU centre closed
  apply exact_place_paid_pair w C b hb normRead δ
    (fun j=>pullSection w U hU centre closed frame (sections j)) t
  intro j
  rw [tensor_is_actual_scalar_times_frame w U hU centre closed frame b δ frame_read]
  exact actual_original_Q_pair U hU centre closed (toHeldField w) π good sections
    tLoc dLoc t readT noncontact firstIdentity secondIdentity b coframe j

end OriginalYuanActualFiniteSectionPayment318
