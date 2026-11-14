module
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.Tactic
public section
noncomputable section
namespace PerfectCoefficientPairing318
open Module
set_option maxHeartbeats 1800000
variable {R A ι : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι]
  (b : Basis ι R A) (σ : ι → ι) (hσ : Function.Involutive σ)
  (ε : A →ₗ[R] R)
  (hpair : ∀ i j,ε (b i*b j)=if j=σ i then 1 else 0)

/-- Actual multiplication followed by the specified coefficient functional. -/
@[expose] def pairing : A →ₗ[R] Module.Dual R A where
  toFun x :=
    { toFun := fun y => ε (x*y)
      map_add' := fun y z => by rw [mul_add,map_add]
      map_smul' := fun r y => by rw [Algebra.mul_smul_comm,map_smul] }
  map_add' x y := by ext z; simp only [add_mul,map_add,LinearMap.add_apply]
  map_smul' r x := by ext y; simp only [Algebra.smul_mul_assoc,map_smul,LinearMap.smul_apply]

@[expose] def inverse (f : Module.Dual R A) : A := ∑ i, f (b (σ i)) • b i

include hσ hpair in
 theorem pairing_coordinate (x : A) (i : ι) : ε (x*b (σ i))=b.repr x i := by
  conv_lhs => rw [←b.sum_repr x]
  simp only [Finset.sum_mul,Algebra.smul_mul_assoc,map_sum,map_smul,hpair,smul_eq_mul]
  have hs (j : ι) : σ i=σ j ↔ i=j := hσ.injective.eq_iff
  simp only [hs,mul_ite,mul_one,mul_zero]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji; simp [Ne.symm hji]
  · simp

include hσ hpair in
 theorem inverse_pairing (x : A) : inverse b σ (pairing ε x)=x := by
  change (∑ i, ε (x*b (σ i)) • b i)=x
  simp only [pairing_coordinate b σ hσ ε hpair]
  exact b.sum_repr x

include hσ hpair in
 theorem pairing_inverse (f : Module.Dual R A) : pairing ε (inverse b σ f)=f := by
  apply b.ext
  intro j
  change ε ((∑ i,f (b (σ i)) • b i)*b j)=f (b j)
  simp only [Finset.sum_mul,Algebra.smul_mul_assoc,map_sum,map_smul,hpair,smul_eq_mul]
  rw [Finset.sum_eq_single (σ j)]
  · simp only [hσ j,ite_true,mul_one]
  · intro k _ hk
    have hh : j≠σ k := by
      intro he
      have := congrArg σ he
      rw [hσ k] at this
      exact hk this.symm
    simp only [hh,ite_false,mul_zero]
  · simp

/-- Perfect duality over the integral base, with explicit inverse. No
invertibility of2, discriminant, root or coefficient is required. -/
@[expose] def equivalence : A ≃ₗ[R] Module.Dual R A where
  __ := pairing ε
  invFun := inverse b σ
  left_inv := inverse_pairing b σ hσ ε hpair
  right_inv := pairing_inverse b σ hσ ε hpair

theorem equivalence_apply (x y : A) : equivalence b σ hσ ε hpair x y=ε (x*y) := rfl

/-- Compatibility with the genuine A action by precomposition with
multiplication. This records the module action, not only an R-vector-space iso. -/
theorem multiplication_compatibility (a x y : A) :
    equivalence b σ hσ ε hpair (a*x) y=equivalence b σ hσ ε hpair x (a*y) := by
  change ε ((a*x)*y)=ε (x*(a*y))
  congr 1
  ring
end PerfectCoefficientPairing318
