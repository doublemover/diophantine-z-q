module
public import PELPrimeNormalizerData318
public section
noncomputable section
namespace PELPrimeOrderConjugation318
open PELQuaternionAlgebra318 PELPrincipalOrderCoordinates318 PELQuaternionDivision318
open PELPrimeNormalizerData318 PELOrderReductionThree318
set_option maxHeartbeats 1600000
/-- Exact integral matrices for conjugation by the four specified rational units. -/
@[expose] def forward (i : Fin 4) (a : Coordinates) : Coordinates := ![
  ![(1)*a 0+(294)*a 1+(-21)*a 2+(168)*a 3,(353)*a 1+(-26)*a 2+(200)*a 3,(-588)*a 1+(43)*a 2+(-336)*a 3,(-475)*a 1+(35)*a 2+(-269)*a 3],
  ![(1)*a 0+(210)*a 1+(-14)*a 2+(126)*a 3,(214)*a 1+(-15)*a 2+(127)*a 3,(-420)*a 1+(29)*a 2+(-252)*a 3,(-285)*a 1+(20)*a 2+(-169)*a 3],
  ![(1)*a 0,(4)*a 1+(1)*a 3,(1)*a 2,(-5)*a 1+(-1)*a 3],
  ![(1)*a 0+(126)*a 1+(-6)*a 2+(84)*a 3,(533)*a 1+(-29)*a 2+(351)*a 3,(-252)*a 1+(13)*a 2+(-168)*a 3,(-735)*a 1+(40)*a 2+(-484)*a 3]] i
@[expose] def backward (i : Fin 4) (a : Coordinates) : Coordinates := ![
  ![(1)*a 0+(-714)*a 1+(-21)*a 2+(-504)*a 3,(193)*a 1+(6)*a 2+(136)*a 3,(1428)*a 1+(43)*a 2+(1008)*a 3,(-155)*a 1+(-5)*a 2+(-109)*a 3],
  ![(1)*a 0+(-420)*a 1+(-14)*a 2+(-294)*a 3,(139)*a 1+(5)*a 2+(97)*a 3,(840)*a 1+(29)*a 2+(588)*a 3,(-135)*a 1+(-5)*a 2+(-94)*a 3],
  ![(1)*a 0,(-1)*a 1+(-1)*a 3,(1)*a 2,(5)*a 1+(4)*a 3],
  ![(1)*a 0+(-756)*a 1+(-6)*a 2+(-546)*a 3,(428)*a 1+(4)*a 2+(309)*a 3,(1512)*a 1+(13)*a 2+(1092)*a 3,(-525)*a 1+(-5)*a 2+(-379)*a 3]] i

theorem forward_backward (i : Fin 4) (a : Coordinates) : forward i (backward i a)=a := by
  fin_cases i <;> ext j <;> fin_cases j <;> simp [forward,backward] <;> ring

theorem backward_forward (i : Fin 4) (a : Coordinates) : backward i (forward i a)=a := by
  fin_cases i <;> ext j <;> fin_cases j <;> simp [forward,backward] <;> ring

theorem forward_add (i : Fin 4) (a b : Coordinates) : forward i (a+b)=forward i a+forward i b := by
  fin_cases i <;> ext j <;> fin_cases j <;> simp [forward] <;> ring

theorem forward_product (i : Fin 4) (a b : Coordinates) :
    forward i (product a b)=product (forward i a) (forward i b) := by
  fin_cases i <;> ext j <;> fin_cases j <;> simp [forward,product] <;> ring

/-- Entire original order elements, not just generator membership, are
identified with the actual rational inner conjugation. -/
theorem actual_forward (i : Fin 4) (a : Coordinates) :
    embed (forward i a)=element i*embed a*reciprocal (element i) := by
  fin_cases i <;> ext <;>
    norm_num [forward,element,coefficients,embed,reciprocal,reducedNorm] <;> push_cast <;> ring

theorem actual_backward (i : Fin 4) (a : Coordinates) :
    embed (backward i a)=reciprocal (element i)*embed a*element i := by
  fin_cases i <;> ext <;>
    norm_num [backward,element,coefficients,embed,reciprocal,reducedNorm] <;> push_cast <;> ring

@[expose] def orderEquiv (i : Fin 4) : order ≃+* order where
  toFun x := coordinatesEquiv (forward i (coordinatesEquiv.symm x))
  invFun x := coordinatesEquiv (backward i (coordinatesEquiv.symm x))
  left_inv x := by simp only [AddEquiv.symm_apply_apply,backward_forward,AddEquiv.apply_symm_apply]
  right_inv x := by simp only [AddEquiv.symm_apply_apply,forward_backward,AddEquiv.apply_symm_apply]
  map_add' x y := by simp only [map_add,forward_add]
  map_mul' x y := by
    obtain ⟨a,rfl⟩ := coordinatesEquiv.surjective x
    obtain ⟨b,rfl⟩ := coordinatesEquiv.surjective y
    rw [← coordinates_mul a b]
    simp only [AddEquiv.symm_apply_apply]
    rw [forward_product i a b,coordinates_mul (forward i a) (forward i b)]

theorem orderEquiv_value (i : Fin 4) (x : order) :
    (orderEquiv i x:B)=element i*(x:B)*reciprocal (element i) := by
  obtain ⟨a,rfl⟩ := coordinatesEquiv.surjective x
  change embed (forward i (coordinatesEquiv.symm (coordinatesEquiv a)))=
    element i*embed a*reciprocal (element i)
  rw [AddEquiv.symm_apply_apply]
  exact actual_forward i a

/-- Both directions of actual integral-order normalization are constructed.
This does not identify a nonunit normalizer with a polarized-surface isomorphism. -/
theorem normalizes_order (i : Fin 4) (x : B) (hx : x∈order) :
    element i*x*reciprocal (element i)∈order ∧
      reciprocal (element i)*x*element i∈order := by
  obtain ⟨a,rfl⟩ := hx
  exact ⟨⟨forward i a,actual_forward i a⟩,⟨backward i a,actual_backward i a⟩⟩
end PELPrimeOrderConjugation318
