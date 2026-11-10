module
public import PELOriginalRamifiedKernels318
public section
noncomputable section
namespace PELOriginalRamifiedSquare318
open PELPrincipalOrderCoordinates318 PELPrimeNormalizerData318 PELPrimeRightLattice318
open PELOriginalRamifiedResidues318 PELOriginalRamifiedKernels318 PELPrimeLatticeResidues318
open PELPrimeLatticeCokernel318
set_option maxHeartbeats 2000000

/-- Products of ANY two elements of the actual residue kernel have all
four original coordinates divisible by p. This is stronger than square-zero
for individual elements and covers the dyadic prime without inverting2. -/
theorem product_divisibility (i : Fin 4) (a b : Coordinates)
    (ha : divisibility i a) (hb : divisibility i b) :
    ∀ j : Fin 4,(prime i:ℤ)∣product a b j := by
  fin_cases i
  · change (2:ℤ)∣a 0 ∧ (2:ℤ)∣a 2 at ha
    change (2:ℤ)∣b 0 ∧ (2:ℤ)∣b 2 at hb
    have ha0 : (a 0:ZMod 2)=0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr ha.1
    have ha2 : (a 2:ZMod 2)=0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr ha.2
    have hb0 : (b 0:ZMod 2)=0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr hb.1
    have hb2 : (b 2:ZMod 2)=0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr hb.2
    intro j
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp
    fin_cases j <;> simp [product] <;> push_cast <;>
      norm_num [ha0,ha2,hb0,hb2] <;> ring
  · change (3:ℤ)∣a 0 ∧ (3:ℤ)∣a 2 at ha
    change (3:ℤ)∣b 0 ∧ (3:ℤ)∣b 2 at hb
    have ha0 : (a 0:ZMod 3)=0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr ha.1
    have ha2 : (a 2:ZMod 3)=0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr ha.2
    have hb0 : (b 0:ZMod 3)=0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr hb.1
    have hb2 : (b 2:ZMod 3)=0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr hb.2
    intro j
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp
    fin_cases j <;> simp [product] <;> push_cast <;>
      norm_num [ha0,ha2,hb0,hb2] <;> ring
  · change (5:ℤ)∣a 0+3*a 2 ∧ (5:ℤ)∣a 3 at ha
    change (5:ℤ)∣b 0+3*b 2 ∧ (5:ℤ)∣b 3 at hb
    have ha0 : (a 0:ZMod 5)= -3*(a 2:ZMod 5) := by
      have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd (a 0+3*a 2) 5).mpr ha.1
      push_cast at hh
      linear_combination hh
    have ha3 : (a 3:ZMod 5)=0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mpr ha.2
    have hb0 : (b 0:ZMod 5)= -3*(b 2:ZMod 5) := by
      have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd (b 0+3*b 2) 5).mpr hb.1
      push_cast at hh
      linear_combination hh
    have hb3 : (b 3:ZMod 5)=0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mpr hb.2
    intro j
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp
    fin_cases j <;> simp [product] <;> push_cast <;>
      norm_num [ha0,ha3,hb0,hb3] <;> ring
  · change (7:ℤ)∣a 0 ∧ (7:ℤ)∣a 2 at ha
    change (7:ℤ)∣b 0 ∧ (7:ℤ)∣b 2 at hb
    have ha0 : (a 0:ZMod 7)=0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mpr ha.1
    have ha2 : (a 2:ZMod 7)=0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mpr ha.2
    have hb0 : (b 0:ZMod 7)=0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mpr hb.1
    have hb2 : (b 2:ZMod 7)=0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mpr hb.2
    intro j
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp
    fin_cases j <;> simp [product] <;> push_cast <;>
      norm_num [ha0,ha2,hb0,hb2] <;> ring

theorem kernel_product (i : Fin 4) (x y : order)
    (hx : reduction i x=0) (hy : reduction i y=0) :
    ∃ z : order,x*y=(prime i) • z := by
  obtain ⟨a,rfl⟩ := coordinatesEquiv.surjective x
  obtain ⟨b,rfl⟩ := coordinatesEquiv.surjective y
  rw [reduction_coordinates,reduction_zero_iff] at hx hy
  choose c hc using product_divisibility i a b hx hy
  refine ⟨coordinatesEquiv c,?_⟩
  rw [←PELOrderReductionThree318.coordinates_mul,←map_nsmul]
  apply congrArg coordinatesEquiv
  ext j
  simpa only [Pi.smul_apply,nsmul_eq_mul] using hc j

theorem conjugate_in_kernel (i : Fin 4) :
    reduction i (coordinatesEquiv (conjugateCoefficients i))=0 := by
  rw [reduction_coordinates]
  fin_cases i <;> ext <;> norm_num [reduceCoordinates,conjugateCoefficients,prime]

/-- Every p-multiple is a SINGLE product of two actual kernel elements,
using original n and bar(n), not a cardinality argument or a chosen uniformizer. -/
theorem multiple_is_product (i : Fin 4) (z : order) :
    ∃ x y : order,reduction i x=0 ∧ reduction i y=0 ∧ x*y=(prime i) • z := by
  refine ⟨rightMultiply i z,coordinatesEquiv (conjugateCoefficients i),?_,conjugate_in_kernel i,?_⟩
  · change rightMultiply i z∈(reduction i).toAddMonoidHom.ker
    rw [actual_kernel]
    exact ⟨z,rfl⟩
  · exact conjugate_after_right i z

@[expose] def primeMultiple (i : Fin 4) : order →+ order where
  toFun x := (prime i) • x
  map_zero' := nsmul_zero _
  map_add' x y := nsmul_add _ _ _

/-- The additive subgroup underlying the square of the actual two-sided
residue kernel: finite sums of its pairwise products. -/
@[expose] def radicalSquare (i : Fin 4) : AddSubgroup order :=
  AddSubgroup.closure {z | ∃ x y : order,reduction i x=0 ∧ reduction i y=0 ∧ x*y=z}

/-- Exact P_p²=pO on the SAME original integral order, for all four primes.
Both inclusions construct actual products/preimages; no local completion or
optimal-embedding orbit classification is asserted here. -/
theorem radical_square_eq (i : Fin 4) : radicalSquare i=(primeMultiple i).range := by
  apply le_antisymm
  · apply (AddSubgroup.closure_le _).mpr
    rintro z ⟨x,y,hx,hy,rfl⟩
    obtain ⟨w,hw⟩ := kernel_product i x y hx hy
    exact ⟨w,hw.symm⟩
  · rintro z ⟨w,rfl⟩
    obtain ⟨x,y,hx,hy,hxy⟩ := multiple_is_product i w
    have h : x*y∈radicalSquare i :=
      AddSubgroup.subset_closure ⟨x,y,hx,hy,rfl⟩
    simpa only [hxy] using h
end PELOriginalRamifiedSquare318
