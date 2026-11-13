module
public import FiniteDualModuleAction318
public section
noncomputable section
namespace ValuedDualPrecomposition318
variable (P A M : Type*) [CommRing P] [CommRing A] [Algebra P A]
  [AddCommGroup M] [Module P M]

/-- Multiplication on the INPUT of the whole valued dual. This is not
the pointwise action on the codomain. Generalizes FiniteDualModuleAction318. -/
@[expose] def action (a : A) (f : A →ₗ[P] M) : A →ₗ[P] M :=
  { toFun := fun x => f (a*x)
    map_add' := fun x y => by rw [mul_add,map_add]
    map_smul' := fun r x => by rw [Algebra.mul_smul_comm,map_smul] }

@[instance_reducible] def actionModule : Module A (A →ₗ[P] M) where
  smul := action P A M
  one_smul f := by
    apply LinearMap.ext; intro x
    change f (1*x)=f x
    rw [one_mul]
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

local instance : Module A (A →ₗ[P] M) := actionModule P A M

/-- The old pointwise P module and new precomposition A module agree
along the ACTUAL algebra map, by linearity of every functional. -/
@[instance_reducible] def baseTower : IsScalarTower P A (A →ₗ[P] M) where
  smul_assoc p a f := by
    apply LinearMap.ext; intro x
    change f ((p • a)*x)=p • f (a*x)
    rw [smul_mul_assoc,map_smul]

lemma action_value (a : A) (f : A →ₗ[P] M) (x : A) :
    (a • f) x=f (a*x) := rfl

/-- Exact old finite dual identification, including its multiplication action. -/
@[expose] def oldDual :
    letI : Module A (A →ₗ[P] P) := actionModule P A P
    FiniteDualModuleAction318.Dual P A ≃ₗ[A] (A →ₗ[P] P) := by
  letI : Module A (A →ₗ[P] P) := actionModule P A P
  exact
    { toFun := fun f => f
      invFun := fun f => f
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
end ValuedDualPrecomposition318
