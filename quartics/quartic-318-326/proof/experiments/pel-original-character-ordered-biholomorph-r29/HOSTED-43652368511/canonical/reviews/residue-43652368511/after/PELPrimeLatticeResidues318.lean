module
public import PELPrimeRightLattice318
public section
noncomputable section
namespace PELPrimeLatticeResidues318
open PELPrincipalOrderCoordinates318 PELPrimeNormalizerData318 PELPrimeRightLattice318
set_option maxHeartbeats 1200000

@[expose] def liftCoefficients : Fin 4 → Fin 4 → Fin 2 → ℤ :=
  ![![![0,1],![0,0],![1,0],![0,0]],
    ![![2,0],![0,0],![0,2],![0,0]],
    ![![3,0],![0,0],![0,0],![0,4]],
    ![![3,6],![0,0],![0,5],![0,0]]]

/-- These are actual integer lifts in the original order coordinates. -/
@[expose] def lift (i : Fin 4) (z : Fin 2 → ZMod (prime i)) : Coordinates :=
  fun k => liftCoefficients i k 0*(z 0).val+liftCoefficients i k 1*(z 1).val

theorem residue_lift (i : Fin 4) (z : Fin 2 → ZMod (prime i)) :
    residue i (lift i z)=z := by
  have h22 : (2 : ZMod 2) = 0 := by decide
  have h23 : (3 : ZMod 2) = 1 := by decide
  have h2n3 : -(3 : ZMod 2) = 1 := by decide
  have h24 : (4 : ZMod 2) = 0 := by decide
  have h34 : (4 : ZMod 3) = 1 := by decide
  have h36 : (6 : ZMod 3) = 0 := by decide
  have h3n8 : -(8 : ZMod 3) = 1 := by decide
  have h5n9 : -(9 : ZMod 5) = 1 := by decide
  have h5n4 : -(4 : ZMod 5) = 1 := by decide
  have h715 : (15 : ZMod 7) = 1 := by decide
  have h770 : (70 : ZMod 7) = 0 := by decide
  have h721 : (21 : ZMod 7) = 0 := by decide
  have h7n97 : -(97 : ZMod 7) = 1 := by decide
  fin_cases i
  · change (Fin 2 → ZMod 2) at z
    change @Eq (Fin 2 → ZMod 2) (residue (0 : Fin 4) (lift (0 : Fin 4) z)) z
    ext j <;> fin_cases j <;>
      norm_num [residue,lift,liftCoefficients,rows,product,conjugateCoefficients,prime] <;>
      push_cast <;> (try simp [ZMod.natCast_zmod_val]) <;> ring_nf <;>
      (try simp only [sub_eq_add_neg, ←mul_neg, h22, h23, h2n3, h24, h34, h36,
        h3n8, h5n9, h5n4, h715, h770, h721, h7n97, mul_zero, mul_one,
        add_zero, zero_add, sub_zero, zero_sub, neg_zero]) <;> ring
  · change (Fin 2 → ZMod 3) at z
    change @Eq (Fin 2 → ZMod 3) (residue (1 : Fin 4) (lift (1 : Fin 4) z)) z
    ext j <;> fin_cases j <;>
      norm_num [residue,lift,liftCoefficients,rows,product,conjugateCoefficients,prime] <;>
      push_cast <;> (try simp [ZMod.natCast_zmod_val]) <;> ring_nf <;>
      (try simp only [sub_eq_add_neg, ←mul_neg, h22, h23, h2n3, h24, h34, h36,
        h3n8, h5n9, h5n4, h715, h770, h721, h7n97, mul_zero, mul_one,
        add_zero, zero_add, sub_zero, zero_sub, neg_zero]) <;> ring
  · change (Fin 2 → ZMod 5) at z
    change @Eq (Fin 2 → ZMod 5) (residue (2 : Fin 4) (lift (2 : Fin 4) z)) z
    ext j <;> fin_cases j <;>
      norm_num [residue,lift,liftCoefficients,rows,product,conjugateCoefficients,prime] <;>
      push_cast <;> (try simp [ZMod.natCast_zmod_val]) <;> ring_nf <;>
      (try simp only [sub_eq_add_neg, ←mul_neg, h22, h23, h2n3, h24, h34, h36,
        h3n8, h5n9, h5n4, h715, h770, h721, h7n97, mul_zero, mul_one,
        add_zero, zero_add, sub_zero, zero_sub, neg_zero]) <;> ring
  · change (Fin 2 → ZMod 7) at z
    change @Eq (Fin 2 → ZMod 7) (residue (3 : Fin 4) (lift (3 : Fin 4) z)) z
    ext j <;> fin_cases j <;>
      norm_num [residue,lift,liftCoefficients,rows,product,conjugateCoefficients,prime] <;>
      push_cast <;> (try simp [ZMod.natCast_zmod_val]) <;> ring_nf <;>
      (try simp only [sub_eq_add_neg, ←mul_neg, h22, h23, h2n3, h24, h34, h36,
        h3n8, h5n9, h5n4, h715, h770, h721, h7n97, mul_zero, mul_one,
        add_zero, zero_add, sub_zero, zero_sub, neg_zero]) <;> ring

theorem residue_surjective (i : Fin 4) : Function.Surjective (residueHom i) := by
  intro z
  exact ⟨lift i z,residue_lift i z⟩

@[expose] def orderResidue (i : Fin 4) : order →+ (Fin 2 → ZMod (prime i)) :=
  (residueHom i).comp coordinatesEquiv.symm.toAddMonoidHom

@[expose] def rightMultiply (i : Fin 4) : order →+ order where
  toFun x := x*coordinatesEquiv (coefficients i)
  map_zero' := zero_mul _
  map_add' x y := add_mul x y _

theorem rightMultiply_coordinates (i : Fin 4) (b : Coordinates) :
    rightMultiply i (coordinatesEquiv b)=coordinatesEquiv (product b (coefficients i)) :=
  (PELOrderReductionThree318.coordinates_mul b (coefficients i)).symm

theorem orderResidue_coordinates (i : Fin 4) (a : Coordinates) :
    orderResidue i (coordinatesEquiv a)=residue i a := by
  change residue i (coordinatesEquiv.symm (coordinatesEquiv a))=residue i a
  rw [AddEquiv.symm_apply_apply]

theorem orderResidue_surjective (i : Fin 4) : Function.Surjective (orderResidue i) := by
  intro z
  refine ⟨coordinatesEquiv (lift i z),?_⟩
  rw [orderResidue_coordinates,residue_lift]

/-- Exact kernel equality on the actual original order, not an abstract
free lattice of the same rank. -/
theorem kernel_eq_range (i : Fin 4) : (orderResidue i).ker=(rightMultiply i).range := by
  ext x
  obtain ⟨a,rfl⟩ := coordinatesEquiv.surjective x
  change orderResidue i (coordinatesEquiv a)=0 ↔
    ∃ b : order,rightMultiply i b=coordinatesEquiv a
  rw [orderResidue_coordinates,kernel_iff]
  constructor
  · rintro ⟨b,hb⟩
    exact ⟨coordinatesEquiv b,by rw [rightMultiply_coordinates,hb]⟩
  · rintro ⟨b,hb⟩
    obtain ⟨c,rfl⟩ := coordinatesEquiv.surjective b
    rw [rightMultiply_coordinates] at hb
    exact ⟨c,coordinatesEquiv.injective hb⟩
end PELPrimeLatticeResidues318
