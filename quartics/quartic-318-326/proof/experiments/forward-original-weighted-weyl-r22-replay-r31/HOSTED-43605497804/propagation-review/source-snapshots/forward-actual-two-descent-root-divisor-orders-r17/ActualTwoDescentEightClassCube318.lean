module
public import ActualTwoDescentTorsionKummerValues318
public section
noncomputable section
namespace ActualTwoDescentEightClassCube318
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [CharZero K]


open ActualTwoDescentSquareClassQuotient318 ActualTwoDescentTorsionKummerValues318
variable [DecidableEq K]

abbrev Cube := ZMod 2 × ZMod 2 × ZMod 2

def cubeClass (n b : K) (hn : n ≠ 0) (hb : b ≠ 0) (v : Cube) : SquareClass K × SquareClass K :=
  secondTorsionClass n hn ^ v.1.val * firstTorsionClass n hn ^ v.2.1.val * retainedBetaClass b hb ^ v.2.2.val

lemma class_of_pow (a : K) (ha : a ≠ 0) (k : ℕ) :
    classOf (a^k) (pow_ne_zero _ ha)=classOf a ha ^ k := by
  have hu : Units.mk0 (a^k) (pow_ne_zero _ ha)=(Units.mk0 a ha)^k := by ext; rfl
  rw [classOf,hu]
  rfl

lemma actual_cube_literal (n b : K) (hn : n ≠ 0) (hb : b ≠ 0) (ε c e : ZMod 2) :
    cubeClass n b hn hb (ε,c,e)=
      (classOf ((3 : K)^ε.val*n^c.val*b^e.val)
        (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hn)) (pow_ne_zero _ hb)),
       classOf ((-n)^ε.val) (pow_ne_zero _ (neg_ne_zero.mpr hn))) := by
  apply Prod.ext
  · change classOf (3 : K) _ ^ ε.val*classOf n hn ^ c.val*classOf b hb ^ e.val=_
    rw [class_of_mul,class_of_mul,class_of_pow,class_of_pow,class_of_pow]
  · change classOf (-n) _ ^ ε.val*(1 : SquareClass K)^c.val*1^e.val=_
    rw [one_pow,one_pow,mul_one,mul_one,class_of_pow]

lemma cube_card : Nat.card Cube=8 := by
  simp [Cube,Nat.card_prod,Nat.card_eq_fintype_card,ZMod.card]

end ActualTwoDescentEightClassCube318
