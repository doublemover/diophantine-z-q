module
public import ActualKummerGalois318
public section
noncomputable section
namespace CharacterRoot318
open KummerTensorField318 FourRootAutomorphisms318
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {F:Type*} [Field F] [CharZero F] (a:Fin 4→F)
@[expose] def radicand (s:Finset (Fin 4)):F:=∏i∈s,a i
@[expose] def root (s:Finset (Fin 4)):Raw a:=∏i∈s,generator a i
@[expose] def sign (s:Finset (Fin 4)) (b:Fin 4→Bool):F:=
  ∏i∈s,if b i then -1 else 1

theorem root_square (s:Finset (Fin 4)) :
    root a s^2=algebraMap F (Raw a) (radicand a s):=by
  simp only [root,radicand,←Finset.prod_pow,map_prod,generator_square]

theorem sign_action (s:Finset (Fin 4)) (b:Fin 4→Bool) :
    signEquiv a b (root a s)=algebraMap F (Raw a) (sign (F:=F) s b)*root a s:=by
  simp only [root,sign,map_prod,signEquiv_generator,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  cases h:b i
  · simp only [Bool.false_eq_true,ite_false,map_one,one_mul]
  · simp only [ite_true,map_neg,map_one]
    change -generator a i=-(1:Raw a)*generator a i
    exact (neg_one_mul (generator a i)).symm

variable [Fact (QuadraticTower318.Independent a)]
theorem root_ne_zero (s:Finset (Fin 4)) : root a s≠0:=
  Finset.prod_ne_zero_iff.mpr (fun i _=>generator_ne_zero a i)

/-- The actual root-sign automorphism fixes a character root precisely when
its specified character sign is positive. -/
theorem sign_fixes_iff (s:Finset (Fin 4)) (b:Fin 4→Bool) :
    signEquiv a b (root a s)=root a s↔sign (F:=F) s b=1:=by
  rw [sign_action]
  constructor
  · intro h
    apply (algebraMap F (Raw a)).injective
    simpa only [map_one] using mul_right_cancel₀ (root_ne_zero a s)
      (h.trans (one_mul (root a s)).symm)
  · intro h
    rw [h,map_one,one_mul]
end CharacterRoot318
