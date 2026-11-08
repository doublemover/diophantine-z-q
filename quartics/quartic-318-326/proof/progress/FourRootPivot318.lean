module
public import ThreeRootOrder318
public section
noncomputable section
namespace FourRootPivot318
open QuadraticPresentation318 FourRootOrder318
open scoped TensorProduct
variable {R:Type*} [CommRing R] (a:Fin 4→R)
@[expose] def indices : Fin 4→Fin 4→Fin 4 :=
  ![![0,1,2,3],![1,0,2,3],![2,3,0,1],![3,2,0,1]]
theorem indices_injective (i:Fin 4) : Function.Injective (indices i) := by
  fin_cases i <;> decide
@[simp] theorem indices_zero (i:Fin 4) : indices i 0=i := by
  fin_cases i <;> rfl

@[expose] def swapFirst : Order a≃ₐ[R]Order ![a 1,a 0,a 2,a 3] :=
  Algebra.TensorProduct.congr (Algebra.TensorProduct.comm R (RootRing (a 0)) (RootRing (a 1)))
    (AlgEquiv.refl : RootRing (a 2)⊗[R]RootRing (a 3)≃ₐ[R]_)

@[expose] def swapPairs : Order a≃ₐ[R]Order ![a 2,a 3,a 0,a 1] :=
  Algebra.TensorProduct.comm R (Pair01 a) (Pair23 a)

/-- Every chosen root is moved to the first slot by actual tensor-algebra
isomorphisms, not an equality of dimensions or an unproved symmetry. -/
@[expose] def pivot (i:Fin 4) : Order a≃ₐ[R]Order (fun j=>a (indices i j)) :=
  Fin.cases (AlgEquiv.refl)
    (Fin.cases (swapFirst a)
      (Fin.cases (swapPairs a)
        (Fin.cases ((swapPairs a).trans (swapFirst ![a 2,a 3,a 0,a 1])) (fun j=>Fin.elim0 j)))) i

@[expose] def regroup (i:Fin 4) : Order a≃ₐ[R]
    RootRing (a (indices i 0))⊗[R]ThreeRootOrder318.Order (fun j=>a (indices i j.succ)) :=
  (pivot a i).trans (ThreeRootOrder318.fourRootRegroup _)
end FourRootPivot318
