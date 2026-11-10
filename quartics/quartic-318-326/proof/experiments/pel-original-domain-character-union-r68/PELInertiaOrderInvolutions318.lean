module
public import PELInertiaNormalizerData318
public section
noncomputable section
namespace PELInertiaOrderInvolutions318
open PELQuaternionAlgebra318 PELPrincipalOrderCoordinates318 PELQuaternionDivision318
open PELInertiaNormalizerData318 PELOrderReductionThree318
set_option maxHeartbeats 1800000
@[expose] def conjugation (i : Fin 5) (a : Coordinates) : Coordinates :=
  ![![(1)*a 0+(-126)*a 1+(7)*a 2+(-84)*a 3,(83)*a 1+(-4)*a 2+(56)*a 3,(252)*a 1+(-13)*a 2+(168)*a 3,(-105)*a 1+(5)*a 2+(-71)*a 3],![(1)*a 0+(1)*a 2,(4)*a 1+(3)*a 3,(-1)*a 2,(-5)*a 1+(-4)*a 3],![(1)*a 0+(-210)*a 1+(15)*a 2+(-126)*a 3,(74)*a 1+(-5)*a 2+(45)*a 3,(420)*a 1+(-29)*a 2+(252)*a 3,(-75)*a 1+(5)*a 2+(-46)*a 3],![(1)*a 0+(-336)*a 1+(22)*a 2+(-210)*a 3,(143)*a 1+(-9)*a 2+(90)*a 3,(672)*a 1+(-43)*a 2+(420)*a 3,(-160)*a 1+(10)*a 2+(-101)*a 3],![(1)*a 0+(1)*a 2,(1)*a 1+(1)*a 3,(-1)*a 2,(-1)*a 3]] i

theorem conjugation_involutive (i : Fin 5) (a : Coordinates) :
    conjugation i (conjugation i a)=a := by
  fin_cases i <;> ext j <;> fin_cases j <;> simp [conjugation] <;> ring

theorem conjugation_add (i : Fin 5) (a b : Coordinates) :
    conjugation i (a+b)=conjugation i a+conjugation i b := by
  fin_cases i <;> ext j <;> fin_cases j <;> simp [conjugation] <;> ring

theorem conjugation_product (i : Fin 5) (a b : Coordinates) :
    conjugation i (product a b)=product (conjugation i a) (conjugation i b) := by
  fin_cases i <;> ext j <;> fin_cases j <;> simp [conjugation,product] <;> ring

theorem actual_conjugation (i : Fin 5) (a : Coordinates) :
    embed (conjugation i a)=element i*embed a*reciprocal (element i) := by
  fin_cases i <;> ext <;>
    norm_num [conjugation,element,coefficients,embed,reciprocal,reducedNorm] <;>
    push_cast <;> ring

@[expose] def orderInvolution (i : Fin 5) : order ≃+* order where
  toFun x := coordinatesEquiv (conjugation i (coordinatesEquiv.symm x))
  invFun x := coordinatesEquiv (conjugation i (coordinatesEquiv.symm x))
  left_inv x := by simp only [AddEquiv.symm_apply_apply,conjugation_involutive,AddEquiv.apply_symm_apply]
  right_inv x := by simp only [AddEquiv.symm_apply_apply,conjugation_involutive,AddEquiv.apply_symm_apply]
  map_add' x y := by simp only [map_add,conjugation_add]
  map_mul' x y := by
    obtain ⟨a,rfl⟩ := coordinatesEquiv.surjective x
    obtain ⟨b,rfl⟩ := coordinatesEquiv.surjective y
    rw [← coordinates_mul]
    simp only [AddEquiv.symm_apply_apply,conjugation_product,coordinates_mul]

theorem orderInvolution_value (i : Fin 5) (x : order) :
    (orderInvolution i x:B)=element i*(x:B)*reciprocal (element i) := by
  obtain ⟨a,rfl⟩ := coordinatesEquiv.surjective x
  change embed (conjugation i (coordinatesEquiv.symm (coordinatesEquiv a)))=
    element i*embed a*reciprocal (element i)
  rw [AddEquiv.symm_apply_apply]
  exact actual_conjugation i a

theorem orderInvolution_square (i : Fin 5) (x : order) :
    orderInvolution i (orderInvolution i x)=x := (orderInvolution i).left_inv x

theorem normalizes_order (i : Fin 5) (x : B) (hx : x∈order) :
    element i*x*reciprocal (element i)∈order := by
  obtain ⟨a,rfl⟩ := hx
  exact ⟨conjugation i a,actual_conjugation i a⟩
end PELInertiaOrderInvolutions318
