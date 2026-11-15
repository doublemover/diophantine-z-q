module
public import PELPrimeLatticeResidues318
public section
noncomputable section
namespace PELPrimeLatticeCokernel318
open PELQuaternionAlgebra318 PELPrincipalOrderCoordinates318 PELPrimeNormalizerData318
open PELPrimeRightLattice318 PELPrimeLatticeResidues318
set_option maxHeartbeats 1000000

/-- The literal right-ideal lattice quotient of the original order. -/
abbrev Cokernel (i : Fin 4) := order ⧸ (rightMultiply i).range

@[expose] def quotientEquiv (i : Fin 4) : Cokernel i ≃+ (Fin 2 → ZMod (prime i)) :=
  (QuotientAddGroup.quotientAddEquivOfEq (kernel_eq_range i).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (orderResidue i) (orderResidue_surjective i))

noncomputable instance cokernelFintype (i : Fin 4) : Fintype (Cokernel i) :=
  Fintype.ofEquiv (Fin 2 → ZMod (prime i)) (quotientEquiv i).symm.toEquiv

/-- Exact lattice index p² for each actual prime normalizer. This proves
neither an algebraic isogeny nor a kernel degree without the period-map join. -/
theorem cokernel_card (i : Fin 4) : Fintype.card (Cokernel i)=(prime i)^2 := by
  rw [Fintype.card_congr (quotientEquiv i).toEquiv]
  simp

theorem literal_indices :
    Fintype.card (Cokernel 0)=4 ∧ Fintype.card (Cokernel 1)=9 ∧
    Fintype.card (Cokernel 2)=25 ∧ Fintype.card (Cokernel 3)=49 := by
  simp [cokernel_card,prime]

@[expose] def conjugateMultiply (i : Fin 4) : order →+ order where
  toFun x := x*coordinatesEquiv (conjugateCoefficients i)
  map_zero' := zero_mul _
  map_add' x y := add_mul x y _

theorem conjugateMultiply_coordinates (i : Fin 4) (a : Coordinates) :
    conjugateMultiply i (coordinatesEquiv a)=
      coordinatesEquiv (product a (conjugateCoefficients i)) :=
  (PELOrderReductionThree318.coordinates_mul a (conjugateCoefficients i)).symm

/-- The exact dual integral lattice map gives multiplication by p in BOTH
orders. The same n and bar(n) are retained, without rescaling the order. -/
theorem conjugate_after_right (i : Fin 4) (x : order) :
    conjugateMultiply i (rightMultiply i x)=(prime i) • x := by
  obtain ⟨a,rfl⟩ := coordinatesEquiv.surjective x
  rw [rightMultiply_coordinates,conjugateMultiply_coordinates,right_norm]
  have he : (fun j : Fin 4 => (prime i:ℤ)*a j)=(prime i) • a := by
    ext j
    simp [nsmul_eq_mul]
  rw [he,map_nsmul]

theorem right_after_conjugate (i : Fin 4) (x : order) :
    rightMultiply i (conjugateMultiply i x)=(prime i) • x := by
  obtain ⟨a,rfl⟩ := coordinatesEquiv.surjective x
  rw [conjugateMultiply_coordinates,rightMultiply_coordinates,left_norm]
  have he : (fun j : Fin 4 => (prime i:ℤ)*a j)=(prime i) • a := by
    ext j
    simp [nsmul_eq_mul]
  rw [he,map_nsmul]

/-- The lattice morphism is injective on actual original order elements. -/
theorem rightMultiply_injective (i : Fin 4) : Function.Injective (rightMultiply i) := by
  intro x y h
  have hh := congrArg (conjugateMultiply i) h
  rw [conjugate_after_right,conjugate_after_right] at hh
  obtain ⟨a,rfl⟩ := coordinatesEquiv.surjective x
  obtain ⟨b,rfl⟩ := coordinatesEquiv.surjective y
  rw [← map_nsmul,← map_nsmul] at hh
  have he := coordinatesEquiv.injective hh
  apply congrArg coordinatesEquiv
  ext j
  have hj := congrFun he j
  simp only [Pi.smul_apply,nsmul_eq_mul] at hj
  exact mul_left_cancel₀ (by exact_mod_cast (NeZero.ne (prime i))) hj
end PELPrimeLatticeCokernel318
