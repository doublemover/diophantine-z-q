module
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Tactic
public section
noncomputable section
namespace ProductLocalization318
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
abbrev Common (x y : S) := Localization.Away (x*y)
@[expose] def inverseLeft (x y : S) : Common x y :=
  algebraMap S (Common x y) y * IsLocalization.Away.invSelf (x*y)
@[expose] def inverseRight (x y : S) : Common x y :=
  algebraMap S (Common x y) x * IsLocalization.Away.invSelf (x*y)

theorem left_inverse (x y : S) : algebraMap S (Common x y) x * inverseLeft x y=1 := by
  rw [inverseLeft,←mul_assoc,←map_mul]
  exact IsLocalization.Away.mul_invSelf _
theorem right_inverse (x y : S) : algebraMap S (Common x y) y * inverseRight x y=1 := by
  rw [inverseRight,←mul_assoc,←map_mul,mul_comm y x]
  exact IsLocalization.Away.mul_invSelf _

@[expose] def leftMap (x y : S) : Localization.Away x →ₐ[R] Common x y :=
  IsLocalization.Away.liftAlgHom (f := Algebra.algHom R S (Common x y)) x
    (IsUnit.of_mul_eq_one_right (inverseLeft x y) (by
      change inverseLeft x y * algebraMap S (Common x y) x=1
      rw [mul_comm,left_inverse]))
@[expose] def rightMap (x y : S) : Localization.Away y →ₐ[R] Common x y :=
  IsLocalization.Away.liftAlgHom (f := Algebra.algHom R S (Common x y)) y
    (IsUnit.of_mul_eq_one_right (inverseRight x y) (by
      change inverseRight x y * algebraMap S (Common x y) y=1
      rw [mul_comm,right_inverse]))

@[simp] theorem leftMap_integral (x y s : S) :
    leftMap (R:=R) x y (algebraMap S (Localization.Away x) s)=algebraMap S (Common x y) s := by
  simp [leftMap,rightMap,IsLocalization.Away.liftAlgHom_apply]
  rfl
@[simp] theorem rightMap_integral (x y s : S) :
    rightMap (R:=R) x y (algebraMap S (Localization.Away y) s)=algebraMap S (Common x y) s := by
  simp [leftMap,rightMap,IsLocalization.Away.liftAlgHom_apply]
  rfl

theorem inverse_unique {T : Type*} [CommRing T] (a b c : T) (hab : a*b=1) (hac : a*c=1) : b=c := by
  calc b=(c*a)*b := by rw [mul_comm c a,hac,one_mul]
       _=c*(a*b) := by ring
       _=c := by rw [hab,mul_one]

theorem leftMap_inverse (x y : S) :
    leftMap (R:=R) x y (IsLocalization.Away.invSelf x)=inverseLeft x y := by
  apply inverse_unique (algebraMap S (Common x y) x)
  · have h:=congrArg (leftMap (R:=R) x y) (IsLocalization.Away.mul_invSelf (S:=Localization.Away x) x)
    simpa only [map_mul,map_one,leftMap_integral] using h
  · exact left_inverse x y

theorem rightMap_inverse (x y : S) :
    rightMap (R:=R) x y (IsLocalization.Away.invSelf y)=inverseRight x y := by
  apply inverse_unique (algebraMap S (Common x y) y)
  · have h:=congrArg (rightMap (R:=R) x y) (IsLocalization.Away.mul_invSelf (S:=Localization.Away y) y)
    simpa only [map_mul,map_one,rightMap_integral] using h
  · exact right_inverse x y
end ProductLocalization318
