module
public import InfinityRingHomExt318
public import Mathlib.RingTheory.Ideal.Pointwise
public section
noncomputable section
namespace InfinitySignResidue318
open InfinityReciprocalAction318 InfinityOrderCoordinates318 InfinitySignCoordinates318
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c:Fin 4→ℚˣ) {F:Type*} [Field F] [Algebra ℚ F]
local instance fieldCharZero:CharZero F:=Algebra.charZero_of_charZero ℚ F
local instance chartAlgebra:Algebra (Base c) (Order c):=(ReciprocalInfinityBase318.chartMap c).toAlgebra
local instance chartSMul:SMul (Base c) (Order c):=(chartAlgebra c).toSMul
local instance chartModule:Module (Base c) (Order c):=Algebra.toModule
variable (p:Order c→+*F) (hu:p (coordinate c)=0)
lemma generator_ne_zero (j:Fin 3):p (generator c j)≠0:=
  ((generator_unit c j).map p).ne_zero
include hu
/-- At any field-valued infinity point, an original full-field sign fixes
the entire residue map exactly when all four sign bits are equal. -/
theorem fixed_iff (b:Fin 4→Bool):
    p.comp (sign c b).toRingHom=p↔∀j:Fin 4,b j=b 0:=by
  constructor
  · intro he
    have hs:∀j:Fin 3,b j.succ=b 0:=by
      intro j
      by_contra hne
      have hx:Bool.xor (b j.succ) (b 0)=true:=by
        cases hj:b j.succ <;> cases h0:b 0 <;> simp_all
      have hy:=RingHom.congr_fun he (generator c j)
      change p (sign c b (generator c j))=p (generator c j) at hy
      rw [on_generator,hx] at hy
      simp only [ite_true,map_neg] at hy
      have hz:(2:F)*p (generator c j)=0:=by linear_combination -hy
      exact (mul_ne_zero (by norm_num) (generator_ne_zero c p j)) hz
    intro j
    exact Fin.cases rfl hs j
  · intro hb
    apply InfinityRingHomExt318.hom_ext c
    · change p (sign c b (coordinate c))=p (coordinate c)
      rw [on_coordinate]
      cases h0:b 0 <;> simp [h0,map_neg,hu]
    · intro j
      change p (sign c b (generator c j))=p (generator c j)
      rw [on_generator,hb j.succ]
      cases b 0 <;> rfl

omit [Algebra ℚ F] hu in
lemma constant_bits (b:Fin 4→Bool):
    (∀j,b j=b 0)↔b=(fun _=>false)∨b=(fun _=>true):=by
  constructor
  · intro h
    cases h0:b 0
    · left;funext j;exact (h j).trans h0
    · right;funext j;exact (h j).trans h0
  · rintro (rfl|rfl) <;> intro j <;> rfl

theorem fixed_exactly (b:Fin 4→Bool):p.comp (sign c b).toRingHom=p↔
    b=(fun _=>false)∨b=(fun _=>true):=by
  rw [fixed_iff c p hu,constant_bits]

/-- Actual Ideal.inertia membership, not a renamed coordinate stabilizer. -/
theorem sign_mem_inertia (b:Fin 4→Bool):
    sign c b∈(RingHom.ker p).inertia (Order c≃ₐ[Base c]Order c)↔
      b=(fun _=>false)∨b=(fun _=>true):=by
  rw [←fixed_exactly c p hu b,Ideal.mem_inertia]
  constructor
  · intro h
    apply RingHom.ext
    intro x
    have hx:=h x
    change p (sign c b x-x)=0 at hx
    change p (sign c b x)=p x
    simpa only [map_sub,sub_eq_zero] using hx
  · intro h x
    have hx:=RingHom.congr_fun h x
    change p (sign c b x-x)=0
    change p (sign c b x)=p x at hx
    rw [map_sub,hx,sub_self]

/-- The diagonal original sign is identity on the entire actual prime
quotient. This does not assert identity on a nonreduced scheme fiber. -/
theorem diagonal_quotient_fixed (x:Order c):
    Ideal.Quotient.mk (RingHom.ker p) (sign c (fun _=>true) x)=
      Ideal.Quotient.mk (RingHom.ker p) x:=by
  apply Ideal.Quotient.eq.mpr
  exact (Ideal.mem_inertia.mp ((sign_mem_inertia c p hu _).mpr (Or.inr rfl))) x
end InfinitySignResidue318
