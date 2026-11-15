module
public import PELThreeTorsionOrderAction318
public section
noncomputable section
namespace PELLevelThreeCoordinates318
open PELOrderReductionThree318 PELPrincipalOrderCoordinates318
set_option maxHeartbeats 1200000
abbrev V := Fin 4 → F3

/-- Inverse of the literal original order-basis reduction, not quaternion
coordinates mistaken for integral order coordinates. -/
@[expose] def reductionCoordinates : Reduction ≃+ V where
  toFun x := ![x.re-x.imJ,x.imI+x.imK,-x.imJ,x.imK]
  invFun a := ⟨a 0-a 2,a 1-a 3,-a 2,a 3⟩
  left_inv x := by ext <;> simp
  right_inv a := by ext i; fin_cases i <;> simp
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring

@[expose] def quotientCoordinates : QuotientOrder ≃+ V :=
  quotientEquiv.toAddEquiv.trans reductionCoordinates

theorem original_coordinates (a : Coordinates) :
    quotientCoordinates (moduloThree.mk' (coordinatesEquiv a))=fun i => (a i:F3) := by
  change reductionCoordinates (quotientEquiv (moduloThree.mk' (coordinatesEquiv a)))=_
  rw [quotientEquiv_mk,reduction_coordinates]
  ext i
  fin_cases i <;> simp [reductionCoordinates,reduceCoordinates]

/-- The literal positive-oriented Riemann Gram, reduced modulo3. -/
@[expose] def orientedForm (a b : V) : F3 :=
  2*a 0*b 1+a 0*b 3-2*a 1*b 0-a 1*b 2+a 2*b 1-a 3*b 0

theorem original_form (a b : Coordinates) :
    orientedForm (fun i => (a i:F3)) (fun i => (b i:F3))=
      (-(integralForm a b):ℤ) := by
  simp only [orientedForm,integralForm]
  push_cast
  ring

theorem form_alternating (a : V) : orientedForm a a=0 := by unfold orientedForm; ring

theorem form_add_left (a b c : V) :
    orientedForm (a+b) c=orientedForm a c+orientedForm b c := by
  simp only [orientedForm,Pi.add_apply]
  ring

theorem form_add_right (a b c : V) :
    orientedForm a (b+c)=orientedForm a b+orientedForm a c := by
  simp only [orientedForm,Pi.add_apply]
  ring

theorem form_nondegenerate (a : V) (ha : ∀ b, orientedForm a b=0) : a=0 := by
  have h0 : a 0=0 := by simpa [orientedForm] using ha ![0,0,0,1]
  have h1 : a 1=0 := by simpa [orientedForm] using ha ![0,0,1,0]
  have h2 : a 2=0 := by simpa [orientedForm,h0] using ha ![0,1,0,0]
  have h3 : a 3=0 := by simpa [orientedForm,h1] using ha ![1,0,0,0]
  ext i
  fin_cases i <;> assumption
end PELLevelThreeCoordinates318
