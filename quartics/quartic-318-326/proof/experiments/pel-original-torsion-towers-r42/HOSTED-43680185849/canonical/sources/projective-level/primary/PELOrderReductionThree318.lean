module
public import PELMaximalIntegralOrder318
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Congruence.Hom
public section
noncomputable section
namespace PELOrderReductionThree318
open PELPrincipalOrderCoordinates318 QuaternionAlgebra
set_option maxHeartbeats 1200000
abbrev F3 := ZMod 3
abbrev Reduction := QuaternionAlgebra F3 0 0 2

/-- Reduction in the SAME order basis. Since 2⁻¹=−1 and 10⁻¹=1 mod3,
these are the literal original quaternion coordinates, not a chosen finite ring. -/
@[expose] def reduceCoordinates (a : Coordinates) : Reduction :=
  ⟨(a 0:F3)-(a 2:F3),(a 1:F3)-(a 3:F3),-(a 2:F3),(a 3:F3)⟩

theorem reduce_add (a b : Coordinates) :
    reduceCoordinates (a+b)=reduceCoordinates a+reduceCoordinates b := by
  ext <;> simp [reduceCoordinates] <;> ring

theorem reduce_product (a b : Coordinates) :
    reduceCoordinates (product a b)=reduceCoordinates a*reduceCoordinates b := by
  have h3 : (3:F3)=0 := by decide
  ext <;> simp [reduceCoordinates,product] <;> push_cast
  · linear_combination (-70*(a 1:F3)*(b 1:F3)-14*(a 1:F3)*(b 3:F3)-
      56*(a 3:F3)*(b 1:F3)-14*(a 3:F3)*(b 3:F3)-(a 2:F3)*(b 2:F3))*h3
  · linear_combination (3*(a 2:F3)*(b 1:F3)-2*(a 1:F3)*(b 2:F3)-
      (a 3:F3)*(b 2:F3))*h3
  · linear_combination (-14*(a 3:F3)*(b 1:F3)-(a 2:F3)*(b 2:F3)+
      14*(a 1:F3)*(b 3:F3))*h3
  · linear_combination ((a 3:F3)*(b 2:F3)+2*(a 1:F3)*(b 2:F3)-
      2*(a 2:F3)*(b 1:F3))*h3

theorem coordinates_mul (a b : Coordinates) :
    coordinatesEquiv (product a b)=coordinatesEquiv a*coordinatesEquiv b :=
  Subtype.ext (embed_mul a b)

theorem coordinates_one : coordinatesEquiv ![1,0,0,0]=1 := by
  apply Subtype.ext
  change embed ![1,0,0,0]=1
  ext <;> norm_num [embed]

/-- Actual ring map from the original maximal order, including multiplication. -/
@[expose] def reduction : order →+* Reduction where
  toFun x := reduceCoordinates (coordinatesEquiv.symm x)
  map_zero' := by ext <;> simp [reduceCoordinates]
  map_one' := by rw [← coordinates_one]; ext <;> simp [reduceCoordinates]
  map_add' x y := by rw [map_add]; exact reduce_add _ _
  map_mul' x y := by
    obtain ⟨a,rfl⟩ := coordinatesEquiv.surjective x
    obtain ⟨b,rfl⟩ := coordinatesEquiv.surjective y
    rw [← coordinates_mul]
    simpa only [AddEquiv.symm_apply_apply] using reduce_product a b

@[simp] theorem reduction_coordinates (a : Coordinates) :
    reduction (coordinatesEquiv a)=reduceCoordinates a := by
  simp [reduction]

theorem reduction_surjective : Function.Surjective reduction := by
  intro x
  obtain ⟨a,ha⟩ := ZMod.intCast_surjective (x.re-x.imJ)
  obtain ⟨b,hb⟩ := ZMod.intCast_surjective (x.imI+x.imK)
  obtain ⟨c,hc⟩ := ZMod.intCast_surjective (-x.imJ)
  obtain ⟨d,hd⟩ := ZMod.intCast_surjective x.imK
  refine ⟨coordinatesEquiv ![a,b,c,d],?_⟩
  rw [reduction_coordinates]
  ext <;> simp [reduceCoordinates,ha,hb,hc,hd]

theorem reduce_zero_iff (a : Coordinates) :
    reduceCoordinates a=0 ↔ ∀ i, (a i:F3)=0 := by
  constructor
  · intro h
    have hr := congrArg QuaternionAlgebra.re h
    have hi := congrArg QuaternionAlgebra.imI h
    have hj := congrArg QuaternionAlgebra.imJ h
    have hk := congrArg QuaternionAlgebra.imK h
    have h2 : (a 2:F3)=0 := by simpa [reduceCoordinates] using hj
    have h3 : (a 3:F3)=0 := by simpa [reduceCoordinates] using hk
    have h0 : (a 0:F3)=0 := by simpa [reduceCoordinates,h2] using hr
    have h1 : (a 1:F3)=0 := by simpa [reduceCoordinates,h3] using hi
    intro i
    fin_cases i <;> assumption
  · intro h
    ext <;> simp [reduceCoordinates,h]

/-- The kernel is exactly 3 times the original order, not merely a kernel
with the expected cardinality. Negative integer coordinates are included. -/
theorem kernel_iff_three (x : order) : reduction x=0 ↔ ∃ y : order, x=(3:ℤ) • y := by
  obtain ⟨a,rfl⟩ := coordinatesEquiv.surjective x
  rw [reduction_coordinates,reduce_zero_iff]
  constructor
  · intro h
    have hd : ∀ i, (3:ℤ) ∣ a i := fun i =>
      (ZMod.intCast_zmod_eq_zero_iff_dvd (a i) 3).mp (h i)
    choose b hb using hd
    refine ⟨coordinatesEquiv b,?_⟩
    rw [← map_zsmul]
    congr 1
    ext i
    change a i=(3:ℤ) • b i
    simpa only [zsmul_eq_mul,Int.cast_ofNat] using hb i
  · rintro ⟨y,hy⟩
    have hh := congrArg coordinatesEquiv.symm hy
    have ha : a=(3:ℤ) • coordinatesEquiv.symm y := by
      simpa only [AddEquiv.symm_apply_apply,map_zsmul] using hh
    intro i
    rw [ha]
    change (((3:ℤ) • coordinatesEquiv.symm y i : ℤ):F3)=0
    simp only [zsmul_eq_mul,Int.cast_mul,Int.cast_ofNat]
    have h3 : (3:F3)=0 := by decide
    rw [h3,zero_mul]

/-- This congruence is proved to be literal congruence modulo3O. -/
@[expose] def moduloThree : RingCon order := RingCon.ker reduction

theorem moduloThree_iff (x y : order) :
    moduloThree x y ↔ ∃ z : order, x-y=(3:ℤ) • z := by
  change reduction x=reduction y ↔ _
  rw [← sub_eq_zero,← map_sub,kernel_iff_three]

abbrev QuotientOrder := moduloThree.Quotient

/-- The actual quotient O/3O, not an assumed isomorphic ring. -/
@[expose] def quotientEquiv : QuotientOrder ≃+* Reduction :=
  RingCon.quotientKerEquivOfSurjective reduction reduction_surjective

theorem quotientEquiv_mk (x : order) : quotientEquiv (moduloThree.mk' x)=reduction x := rfl
end PELOrderReductionThree318
