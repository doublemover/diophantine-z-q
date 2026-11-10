module
public import ActualOrbitLocalFilter318
public section
noncomputable section
namespace PadicQuadraticCoordinates318
open ConcreteG8Domain (K)
open scoped QuadraticAlgebra Topology
set_option maxHeartbeats 1000000

/- Coordinate arithmetic over Qp, without assuming sqrt(2) belongs to Qp.
The inverse is the exact norm quotient, including the totalized zero case. -/
@[expose] def mul {F : Type*} [CommRing F] (x y : F×F) : F×F :=
  (x.1*y.1+2*x.2*y.2,x.1*y.2+x.2*y.1)
@[expose] def sq {F : Type*} [CommRing F] (x : F×F) : F×F := mul x x
@[expose] def qnorm {F : Type*} [CommRing F] (x : F×F) : F := x.1^2-2*x.2^2
@[expose] def inverse {F : Type*} [Field F] (x : F×F) : F×F :=
  (x.1/qnorm x,-x.2/qnorm x)
@[expose] def divide {F : Type*} [Field F] (x y : F×F) : F×F := mul x (inverse y)
@[expose] def lift (p : ℕ) [Fact p.Prime] (x : K) : ℚ_[p]×ℚ_[p] :=
  ((x.re:ℚ_[p]),(x.im:ℚ_[p]))

@[simp] lemma lift_zero (p : ℕ) [Fact p.Prime] : lift p 0=0 := by simp [lift]
@[simp] lemma lift_one (p : ℕ) [Fact p.Prime] : lift p 1=(1,0) := by simp [lift]
@[simp] lemma lift_two (p : ℕ) [Fact p.Prime] : lift p 2=(2,0) := by simp [lift]
lemma lift_add (p : ℕ) [Fact p.Prime] (x y : K) : lift p (x+y)=lift p x+lift p y := by
  ext <;> simp [lift]
lemma lift_sub (p : ℕ) [Fact p.Prime] (x y : K) : lift p (x-y)=lift p x-lift p y := by
  ext <;> simp [lift]
lemma lift_mul (p : ℕ) [Fact p.Prime] (x y : K) : lift p (x*y)=mul (lift p x) (lift p y) := by
  ext <;> simp [lift,mul] <;> push_cast <;> ring
lemma lift_sq (p : ℕ) [Fact p.Prime] (x : K) : lift p (x^2)=sq (lift p x) := by
  simpa only [pow_two,sq] using lift_mul p x x
lemma lift_inverse (p : ℕ) [Fact p.Prime] (x : K) : lift p x⁻¹=inverse (lift p x) := by
  ext <;> simp [lift,inverse,qnorm,QuadraticAlgebra.inv_def,QuadraticAlgebra.norm_def]
    <;> push_cast <;> ring
lemma lift_divide (p : ℕ) [Fact p.Prime] (x y : K) : lift p (x/y)=divide (lift p x) (lift p y) := by
  rw [div_eq_mul_inv,lift_mul,lift_inverse]
  rfl

section Continuity
variable {F X : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [ContinuousInv₀ F] [TopologicalSpace X]

@[fun_prop] lemma mul_continuous : Continuous (fun z : (F×F)×(F×F) => mul z.1 z.2) := by
  unfold mul
  fun_prop
@[fun_prop] lemma sq_continuous : Continuous (sq (F:=F)) := by
  unfold sq mul
  fun_prop
@[fun_prop] lemma qnorm_continuous : Continuous (qnorm (F:=F)) := by
  unfold qnorm
  fun_prop
lemma inverse_continuousAt {x : F×F} (hx : qnorm x≠0) :
    ContinuousAt (inverse (F:=F)) x := by
  unfold inverse
  exact (continuous_fst.continuousAt.div qnorm_continuous.continuousAt hx).prodMk
    (continuous_snd.neg.continuousAt.div qnorm_continuous.continuousAt hx)
lemma divide_continuousAt {x : X} {f g : X → F×F}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) (hn : qnorm (g x)≠0) :
    ContinuousAt (fun y => divide (f y) (g y)) x :=
  mul_continuous.continuousAt.comp (hf.prodMk ((inverse_continuousAt hn).comp hg))
end Continuity

end PadicQuadraticCoordinates318
