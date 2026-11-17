module
public import ActualTwoDescentEllipticPointExtraction318
public section
noncomputable section
namespace ActualTwoDescentTorsionKummerValues318
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [CharZero K]


open ActualTwoDescentEllipticModel318 ActualTwoDescentSimpleRootCoordinates318
open ActualTwoDescentSquareClassQuotient318 ActualTwoDescentKummerHom318
open ActualTwoDescentKummerAffineCoordinates318 ActualTwoDescentActualTorsionPoint318
open ActualTwoDescentLiteralKummerClasses318
variable [DecidableEq K]

def firstTorsion (n : K) (hn : n ≠ 0) : Point n := point n n 0 hn (by ring)
def zeroTorsion (n : K) (hn : n ≠ 0) : Point n := point n 0 0 hn (by ring)
def firstTorsionClass (n : K) (hn : n ≠ 0) : SquareClass K × SquareClass K := (classOf n hn,1)
def secondTorsionClass (n : K) (hn : n ≠ 0) : SquareClass K × SquareClass K :=
  (classOf 3 (by norm_num),classOf (-n) (neg_ne_zero.mpr hn))
def retainedBetaClass (b : K) (hb : b ≠ 0) : SquareClass K × SquareClass K := (classOf b hb,1)

lemma actual_first_torsion_class (n : K) (hn : n ≠ 0) :
    kummerClass n hn (firstTorsion n hn)=firstTorsionClass n hn := by
  apply Prod.ext
  · change classOf (rootCoordinate (firstRoot n hn) (.some n 0 _)) _=classOf n hn
    rw [actual_first_coordinate n n 0 hn _ (by intro he; apply hn; linear_combination he/4)]
    apply (class_of_eq_iff _ _ _ _).mpr
    exact ⟨2,by norm_num,by ring⟩
  · change classOf (rootCoordinate (secondRoot n hn) (.some n 0 _)) _=1
    rw [actual_second_at_root]
    rw [←class_of_one]
    apply (class_of_eq_iff _ _ _ _).mpr
    exact ⟨2*n,mul_ne_zero (by norm_num) hn,by ring⟩

lemma actual_second_torsion_class (n : K) (hn : n ≠ 0) :
    kummerClass n hn (torsionPoint n hn)=secondTorsionClass n hn := by
  apply Prod.ext
  · change classOf (rootCoordinate (firstRoot n hn) (.some (-3*n) 0 _)) _=classOf 3 _
    rw [actual_first_at_root]
    apply (class_of_eq_iff _ _ _ _).mpr
    exact ⟨2*n,mul_ne_zero (by norm_num) hn,by ring⟩
  · change classOf (rootCoordinate (secondRoot n hn) (.some (-3*n) 0 _)) _=classOf (-n) _
    rw [actual_second_coordinate n (-3*n) 0 hn _ (by intro he; apply hn; linear_combination -he/4)]
    apply (class_of_eq_iff _ _ _ _).mpr
    exact ⟨2,by norm_num,by ring⟩

lemma actual_zero_torsion_class (n : K) (hn : n ≠ 0) :
    kummerClass n hn (zeroTorsion n hn)=secondTorsionClass n hn*firstTorsionClass n hn := by
  apply Prod.ext
  · change classOf (rootCoordinate (firstRoot n hn) (.some 0 0 _)) _=classOf 3 _*classOf n hn
    rw [actual_first_coordinate n 0 0 hn _ (by intro he; apply hn; linear_combination he/3),←class_of_mul]
    congr 1
    ring
  · change classOf (rootCoordinate (secondRoot n hn) (.some 0 0 _)) _=classOf (-n) _*1
    rw [actual_second_coordinate n 0 0 hn _ (by simpa using neg_ne_zero.mpr hn),mul_one]
    congr 1
    ring

end ActualTwoDescentTorsionKummerValues318
