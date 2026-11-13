module
public import TensorCoefficientDuality318
public section
noncomputable section
namespace FiniteDualModuleAction318
set_option maxHeartbeats 1600000
variable (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]

/-- The actual R-dual equipped with the multiplication-precomposition
A action. A separate carrier prevents confusing it with pointwise scalar
multiplication on the R-valued codomain. -/
@[expose] def Dual := A →ₗ[R] R
instance : AddCommGroup (Dual R A) := inferInstanceAs (AddCommGroup (A →ₗ[R] R))
@[expose] def evaluate (f : Dual R A) (x : A) : R := f x
@[expose] def action (a : A) (f : Dual R A) : Dual R A :=
  { toFun := fun x => f (a*x)
    map_add' := fun x y => by rw [mul_add,map_add]
    map_smul' := fun r x => by rw [Algebra.mul_smul_comm,map_smul] }
instance : Module A (Dual R A) where
  smul := action R A
  one_smul f := by apply LinearMap.ext; intro x; change f (1*x)=f x; rw [one_mul]
  mul_smul a b f := by
    apply LinearMap.ext; intro x
    change f ((a*b)*x)=f (b*(a*x))
    congr 1; ring
  smul_zero a := by apply LinearMap.ext; intro x; rfl
  smul_add a f g := by apply LinearMap.ext; intro x; rfl
  add_smul a b f := by
    apply LinearMap.ext; intro x
    change f ((a+b)*x)=f (a*x)+f (b*x)
    rw [add_mul,map_add]
  zero_smul f := by
    apply LinearMap.ext; intro x
    change f (0*x)=0
    rw [zero_mul,map_zero]

theorem action_evaluate (a : A) (f : Dual R A) (x : A) : evaluate R A (a • f) x=evaluate R A f (a*x) := rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  (F : TensorCoefficientDuality318.Frame R A ι)

/-- A genuine A-linear isomorphism onto the ENTIRE finite dual module,
with its correct action, rather than merely an R-linear rank calculation. -/
@[expose] def frame : A ≃ₗ[A] Dual R A where
  toFun := F.duality
  invFun := F.duality.symm
  left_inv := F.duality.symm_apply_apply
  right_inv := F.duality.apply_symm_apply
  map_add' := F.duality.map_add
  map_smul' a x := by
    apply LinearMap.ext
    intro y
    change F.duality (a*x) y=F.duality x (a*y)
    exact F.duality_mul a x y

theorem frame_evaluate (x y : A) : evaluate R A (frame R A F x) y=F.coefficient (x*y) := rfl

theorem frame_one (y : A) : evaluate R A (frame R A F 1) y=F.coefficient y := by
  rw [frame_evaluate,one_mul]
end FiniteDualModuleAction318
