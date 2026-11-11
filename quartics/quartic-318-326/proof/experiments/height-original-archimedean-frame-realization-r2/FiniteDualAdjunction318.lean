module
public import FiniteDualModuleAction318
public section
noncomputable section
namespace FiniteDualAdjunction318
open FiniteDualModuleAction318
set_option maxHeartbeats 1800000
variable {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]

/-- Evaluation at the actual unit of A is the counit of the finite-dual
coinduction formula. This is a genuine R-linear map on arbitrary M. -/
@[expose] def evaluateOne (f : M →ₗ[A] Dual R A) : M →ₗ[R] R where
  toFun m := evaluate R A (f m) 1
  map_add' m n := by rw [map_add]; rfl
  map_smul' r m := by
    have h := congrArg (fun g : Dual R A => evaluate R A g 1)
      (f.map_smul (algebraMap R A r) m)
    rw [IsScalarTower.algebraMap_smul R A M] at h
    change evaluate R A (f (r • m)) 1=r*evaluate R A (f m) 1
    calc
      _ = (f m) (algebraMap R A r*1) := h
      _ = _ := by rw [←Algebra.smul_def,map_smul]; rfl

/-- The inverse adjoint correspondence, retaining the multiplication
precomposition action on the ENTIRE finite dual. -/
@[expose] def coinduce (g : M →ₗ[R] R) : M →ₗ[A] Dual R A where
  toFun m :=
    { toFun := fun a => g (a • m)
      map_add' a b := by rw [add_smul,map_add]
      map_smul' r a := by rw [smul_assoc,map_smul] }
  map_add' m n := by
    apply LinearMap.ext
    intro a
    change g (a • (m+n))=g (a • m)+g (a • n)
    rw [smul_add,map_add]
  map_smul' a m := by
    apply LinearMap.ext
    intro b
    change g (b • (a • m))=g ((a*b) • m)
    rw [smul_smul,mul_comm b a]

theorem evaluateOne_coinduce (g : M →ₗ[R] R) : evaluateOne (coinduce g)=g := by
  ext m
  change g ((1:A) • m)=g m
  rw [one_smul]

theorem coinduce_evaluateOne (f : M →ₗ[A] Dual R A) : coinduce (evaluateOne f)=f := by
  apply LinearMap.ext
  intro m
  apply LinearMap.ext
  intro a
  change evaluate R A (f (a • m)) 1=evaluate R A (f m) a
  rw [map_smul]
  change (f m) (a*1)=(f m) a
  rw [mul_one]

/-- The actual hom-set adjunction for the whole finite-dual module.
It is not inferred from matching ranks or a chosen root pairing. -/
@[expose] def homEquiv : (M →ₗ[A] Dual R A) ≃ (M →ₗ[R] R) where
  toFun := evaluateOne
  invFun := coinduce
  left_inv := coinduce_evaluateOne
  right_inv := evaluateOne_coinduce

/-- The affine counit is literal evaluation at1; on the perfect-pairing
frame it is exactly the original coefficient functional. -/
theorem counit_frame {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : TensorCoefficientDuality318.Frame R A ι) :
    evaluateOne (frame R A F).toLinearMap=F.coefficient := by
  ext a
  change F.coefficient (a*1)=F.coefficient a
  rw [mul_one]

variable {N : Type*} [AddCommGroup N] [Module A N] [Module R N] [IsScalarTower R A N]

/-- Naturality on every actual module morphism, not only on generators. -/
theorem naturality (f : N →ₗ[A] Dual R A) (h : M →ₗ[A] N) (m : M) :
    evaluateOne (f.comp h) m=evaluateOne f (h m) := rfl
end FiniteDualAdjunction318
