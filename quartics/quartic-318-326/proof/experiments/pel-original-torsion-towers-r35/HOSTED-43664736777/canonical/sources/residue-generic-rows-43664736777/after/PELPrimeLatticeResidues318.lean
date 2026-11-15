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
    ext j
    fin_cases j
    · calc
        _ = (3 : ZMod 2) * ((z 0).val : ZMod 2) + (2 : ZMod 2) * ((z 1).val : ZMod 2) := by
          have hpoly (a b : ℤ) : product (fun k=>liftCoefficients (0 : Fin 4) k 0*a+liftCoefficients (0 : Fin 4) k 1*b) (conjugateCoefficients (0 : Fin 4)) (rows (0 : Fin 4) (0 : Fin 2)) =
              (3 : ℤ) * a + (2 : ℤ) * b := by
            norm_num [liftCoefficients,rows,product,conjugateCoefficients,prime] <;> ring
          have hrow : product (lift (0 : Fin 4) z) (conjugateCoefficients (0 : Fin 4)) (rows (0 : Fin 4) (0 : Fin 2)) =
              (3 : ℤ) * ((z 0).val : ℤ) + (2 : ℤ) * ((z 1).val : ℤ) :=
            hpoly ((z 0).val : ℤ) ((z 1).val : ℤ)
          change ((product (lift (0 : Fin 4) z) (conjugateCoefficients (0 : Fin 4)) (rows (0 : Fin 4) (0 : Fin 2))) : ZMod 2) = _
          rw [hrow]
          simp only [Int.cast_add,Int.cast_mul,Int.cast_neg,Int.cast_natCast,
            Int.cast_ofNat,Int.cast_zero,Int.cast_one] <;> ring
        _ = z 0 := by
          simp only [ZMod.natCast_zmod_val, h23, h22, neg_zero,
            zero_mul, one_mul, zero_add, add_zero]
    · calc
        _ = -(4 : ZMod 2) * ((z 0).val : ZMod 2) + -(3 : ZMod 2) * ((z 1).val : ZMod 2) := by
          have hpoly (a b : ℤ) : product (fun k=>liftCoefficients (0 : Fin 4) k 0*a+liftCoefficients (0 : Fin 4) k 1*b) (conjugateCoefficients (0 : Fin 4)) (rows (0 : Fin 4) (1 : Fin 2)) =
              (-4 : ℤ) * a + (-3 : ℤ) * b := by
            norm_num [liftCoefficients,rows,product,conjugateCoefficients,prime] <;> ring
          have hrow : product (lift (0 : Fin 4) z) (conjugateCoefficients (0 : Fin 4)) (rows (0 : Fin 4) (1 : Fin 2)) =
              (-4 : ℤ) * ((z 0).val : ℤ) + (-3 : ℤ) * ((z 1).val : ℤ) :=
            hpoly ((z 0).val : ℤ) ((z 1).val : ℤ)
          change ((product (lift (0 : Fin 4) z) (conjugateCoefficients (0 : Fin 4)) (rows (0 : Fin 4) (1 : Fin 2))) : ZMod 2) = _
          rw [hrow]
          simp only [Int.cast_add,Int.cast_mul,Int.cast_neg,Int.cast_natCast,
            Int.cast_ofNat,Int.cast_zero,Int.cast_one] <;> ring
        _ = z 1 := by
          simp only [ZMod.natCast_zmod_val, h24, h2n3, neg_zero,
            zero_mul, one_mul, zero_add, add_zero]
  · change (Fin 2 → ZMod 3) at z
    change @Eq (Fin 2 → ZMod 3) (residue (1 : Fin 4) (lift (1 : Fin 4) z)) z
    ext j
    fin_cases j
    · calc
        _ = (4 : ZMod 3) * ((z 0).val : ZMod 3) + (6 : ZMod 3) * ((z 1).val : ZMod 3) := by
          have hpoly (a b : ℤ) : product (fun k=>liftCoefficients (1 : Fin 4) k 0*a+liftCoefficients (1 : Fin 4) k 1*b) (conjugateCoefficients (1 : Fin 4)) (rows (1 : Fin 4) (0 : Fin 2)) =
              (4 : ℤ) * a + (6 : ℤ) * b := by
            norm_num [liftCoefficients,rows,product,conjugateCoefficients,prime] <;> ring
          have hrow : product (lift (1 : Fin 4) z) (conjugateCoefficients (1 : Fin 4)) (rows (1 : Fin 4) (0 : Fin 2)) =
              (4 : ℤ) * ((z 0).val : ℤ) + (6 : ℤ) * ((z 1).val : ℤ) :=
            hpoly ((z 0).val : ℤ) ((z 1).val : ℤ)
          change ((product (lift (1 : Fin 4) z) (conjugateCoefficients (1 : Fin 4)) (rows (1 : Fin 4) (0 : Fin 2))) : ZMod 3) = _
          rw [hrow]
          simp only [Int.cast_add,Int.cast_mul,Int.cast_neg,Int.cast_natCast,
            Int.cast_ofNat,Int.cast_zero,Int.cast_one] <;> ring
        _ = z 0 := by
          simp only [ZMod.natCast_zmod_val, h34, h36, neg_zero,
            zero_mul, one_mul, zero_add, add_zero]
    · calc
        _ = -(6 : ZMod 3) * ((z 0).val : ZMod 3) + -(8 : ZMod 3) * ((z 1).val : ZMod 3) := by
          have hpoly (a b : ℤ) : product (fun k=>liftCoefficients (1 : Fin 4) k 0*a+liftCoefficients (1 : Fin 4) k 1*b) (conjugateCoefficients (1 : Fin 4)) (rows (1 : Fin 4) (1 : Fin 2)) =
              (-6 : ℤ) * a + (-8 : ℤ) * b := by
            norm_num [liftCoefficients,rows,product,conjugateCoefficients,prime] <;> ring
          have hrow : product (lift (1 : Fin 4) z) (conjugateCoefficients (1 : Fin 4)) (rows (1 : Fin 4) (1 : Fin 2)) =
              (-6 : ℤ) * ((z 0).val : ℤ) + (-8 : ℤ) * ((z 1).val : ℤ) :=
            hpoly ((z 0).val : ℤ) ((z 1).val : ℤ)
          change ((product (lift (1 : Fin 4) z) (conjugateCoefficients (1 : Fin 4)) (rows (1 : Fin 4) (1 : Fin 2))) : ZMod 3) = _
          rw [hrow]
          simp only [Int.cast_add,Int.cast_mul,Int.cast_neg,Int.cast_natCast,
            Int.cast_ofNat,Int.cast_zero,Int.cast_one] <;> ring
        _ = z 1 := by
          simp only [ZMod.natCast_zmod_val, h36, h3n8, neg_zero,
            zero_mul, one_mul, zero_add, add_zero]
  · change (Fin 2 → ZMod 5) at z
    change @Eq (Fin 2 → ZMod 5) (residue (2 : Fin 4) (lift (2 : Fin 4) z)) z
    ext j
    fin_cases j
    · calc
        _ = -(9 : ZMod 5) * ((z 0).val : ZMod 5) := by
          have hpoly (a b : ℤ) : product (fun k=>liftCoefficients (2 : Fin 4) k 0*a+liftCoefficients (2 : Fin 4) k 1*b) (conjugateCoefficients (2 : Fin 4)) (rows (2 : Fin 4) (0 : Fin 2)) =
              (-9 : ℤ) * a + (0 : ℤ) * b := by
            norm_num [liftCoefficients,rows,product,conjugateCoefficients,prime] <;> ring
          have hrow : product (lift (2 : Fin 4) z) (conjugateCoefficients (2 : Fin 4)) (rows (2 : Fin 4) (0 : Fin 2)) =
              (-9 : ℤ) * ((z 0).val : ℤ) + (0 : ℤ) * ((z 1).val : ℤ) :=
            hpoly ((z 0).val : ℤ) ((z 1).val : ℤ)
          change ((product (lift (2 : Fin 4) z) (conjugateCoefficients (2 : Fin 4)) (rows (2 : Fin 4) (0 : Fin 2))) : ZMod 5) = _
          rw [hrow]
          simp only [Int.cast_add,Int.cast_mul,Int.cast_neg,Int.cast_natCast,
            Int.cast_ofNat,Int.cast_zero,Int.cast_one] <;> ring
        _ = z 0 := by
          simp only [ZMod.natCast_zmod_val, h5n9, neg_zero,
            zero_mul, one_mul, zero_add, add_zero]
    · calc
        _ = -(4 : ZMod 5) * ((z 1).val : ZMod 5) := by
          have hpoly (a b : ℤ) : product (fun k=>liftCoefficients (2 : Fin 4) k 0*a+liftCoefficients (2 : Fin 4) k 1*b) (conjugateCoefficients (2 : Fin 4)) (rows (2 : Fin 4) (1 : Fin 2)) =
              (0 : ℤ) * a + (-4 : ℤ) * b := by
            norm_num [liftCoefficients,rows,product,conjugateCoefficients,prime] <;> ring
          have hrow : product (lift (2 : Fin 4) z) (conjugateCoefficients (2 : Fin 4)) (rows (2 : Fin 4) (1 : Fin 2)) =
              (0 : ℤ) * ((z 0).val : ℤ) + (-4 : ℤ) * ((z 1).val : ℤ) :=
            hpoly ((z 0).val : ℤ) ((z 1).val : ℤ)
          change ((product (lift (2 : Fin 4) z) (conjugateCoefficients (2 : Fin 4)) (rows (2 : Fin 4) (1 : Fin 2))) : ZMod 5) = _
          rw [hrow]
          simp only [Int.cast_add,Int.cast_mul,Int.cast_neg,Int.cast_natCast,
            Int.cast_ofNat,Int.cast_zero,Int.cast_one] <;> ring
        _ = z 1 := by
          simp only [ZMod.natCast_zmod_val, h5n4, neg_zero,
            zero_mul, one_mul, zero_add, add_zero]
  · change (Fin 2 → ZMod 7) at z
    change @Eq (Fin 2 → ZMod 7) (residue (3 : Fin 4) (lift (3 : Fin 4) z)) z
    ext j
    fin_cases j
    · calc
        _ = (15 : ZMod 7) * ((z 0).val : ZMod 7) + (70 : ZMod 7) * ((z 1).val : ZMod 7) := by
          have hpoly (a b : ℤ) : product (fun k=>liftCoefficients (3 : Fin 4) k 0*a+liftCoefficients (3 : Fin 4) k 1*b) (conjugateCoefficients (3 : Fin 4)) (rows (3 : Fin 4) (0 : Fin 2)) =
              (15 : ℤ) * a + (70 : ℤ) * b := by
            norm_num [liftCoefficients,rows,product,conjugateCoefficients,prime] <;> ring
          have hrow : product (lift (3 : Fin 4) z) (conjugateCoefficients (3 : Fin 4)) (rows (3 : Fin 4) (0 : Fin 2)) =
              (15 : ℤ) * ((z 0).val : ℤ) + (70 : ℤ) * ((z 1).val : ℤ) :=
            hpoly ((z 0).val : ℤ) ((z 1).val : ℤ)
          change ((product (lift (3 : Fin 4) z) (conjugateCoefficients (3 : Fin 4)) (rows (3 : Fin 4) (0 : Fin 2))) : ZMod 7) = _
          rw [hrow]
          simp only [Int.cast_add,Int.cast_mul,Int.cast_neg,Int.cast_natCast,
            Int.cast_ofNat,Int.cast_zero,Int.cast_one] <;> ring
        _ = z 0 := by
          simp only [ZMod.natCast_zmod_val, h715, h770, neg_zero,
            zero_mul, one_mul, zero_add, add_zero]
    · calc
        _ = -(21 : ZMod 7) * ((z 0).val : ZMod 7) + -(97 : ZMod 7) * ((z 1).val : ZMod 7) := by
          have hpoly (a b : ℤ) : product (fun k=>liftCoefficients (3 : Fin 4) k 0*a+liftCoefficients (3 : Fin 4) k 1*b) (conjugateCoefficients (3 : Fin 4)) (rows (3 : Fin 4) (1 : Fin 2)) =
              (-21 : ℤ) * a + (-97 : ℤ) * b := by
            norm_num [liftCoefficients,rows,product,conjugateCoefficients,prime] <;> ring
          have hrow : product (lift (3 : Fin 4) z) (conjugateCoefficients (3 : Fin 4)) (rows (3 : Fin 4) (1 : Fin 2)) =
              (-21 : ℤ) * ((z 0).val : ℤ) + (-97 : ℤ) * ((z 1).val : ℤ) :=
            hpoly ((z 0).val : ℤ) ((z 1).val : ℤ)
          change ((product (lift (3 : Fin 4) z) (conjugateCoefficients (3 : Fin 4)) (rows (3 : Fin 4) (1 : Fin 2))) : ZMod 7) = _
          rw [hrow]
          simp only [Int.cast_add,Int.cast_mul,Int.cast_neg,Int.cast_natCast,
            Int.cast_ofNat,Int.cast_zero,Int.cast_one] <;> ring
        _ = z 1 := by
          simp only [ZMod.natCast_zmod_val, h721, h7n97, neg_zero,
            zero_mul, one_mul, zero_add, add_zero]

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
