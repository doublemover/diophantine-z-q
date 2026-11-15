module
public import FiniteModuleImageFrame318
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.TensorProduct.Finite
public section
noncomputable section
namespace FiniteCotangentImage318
open NumberField ActualFinitePlaceIntegers318
open scoped TensorProduct
variable {K : Type*} [Field K] [NumberField K] (w : FinitePlace K)
  (A : Type*) [CommRing A] [Algebra (Integers w) A] [Algebra A (Integers w)]
  [IsScalarTower (Integers w) A (Integers w)]
  [Algebra.EssFiniteType (Integers w) A]

/-- Pullback of the actual integral relative cotangent module along the given
integral point A→Integers w. This is NOT the differential module of the field. -/
abbrev Fiber := TensorProduct A (Integers w) (KaehlerDifferential (Integers w) A)

/-- Essential finite type, not normality alone, supplies finite generation. -/
theorem fiber_finite : Module.Finite (Integers w) (Fiber w A) := by infer_instance

/-- The tensor square relevant to quadratic sections; no invertibility or
identification with a regular model's dualizing square is asserted. -/
abbrev QuadraticFiber := TensorProduct (Integers w) (Fiber w A) (Fiber w A)

theorem quadraticFiber_finite : Module.Finite (Integers w) (QuadraticFiber w A) := by
  infer_instance

variable (ev : Fiber w A →ₗ[Integers w] K)

/-- Construct the quadratic evaluation from the SAME supplied cotangent
functional. The functional's geometric/generic provenance is still an input. -/
@[expose] def evaluationBilinear : Fiber w A →ₗ[Integers w] Fiber w A →ₗ[Integers w] K where
  toFun x :=
    { toFun := fun y => ev x*ev y
      map_add' y z := by simp only [map_add,mul_add]
      map_smul' a y := by simp only [map_smul,Algebra.smul_def]; ring }
  map_add' x y := by
    apply LinearMap.ext
    intro z
    simp only [map_add,LinearMap.add_apply]
    exact add_mul (ev x) (ev y) (ev z)
  map_smul' a x := by
    apply LinearMap.ext
    intro y
    simp only [map_smul,LinearMap.smul_apply,Algebra.smul_def]
    ring

@[expose] def quadraticEvaluation : QuadraticFiber w A →ₗ[Integers w] K :=
  TensorProduct.lift (evaluationBilinear w A ev)

@[simp] theorem quadraticEvaluation_tmul (x y : Fiber w A) :
    quadraticEvaluation w A ev (x ⊗ₜ[Integers w] y)=ev x*ev y := rfl

/-- The image is constructed, and its finite generation is a consequence of
essential finite type and tensor base change, not a caller-supplied lattice fact. -/
theorem image_fg : (quadraticEvaluation w A ev).range.FG :=
  Submodule.fg_range (quadraticEvaluation w A ev)

/-- One actual nonzero quadratic section suffices. The source module need
not be torsion-free or rank one; its image is the exact embedded submodule. -/
@[expose] def imageFrame (x : QuadraticFiber w A)
    (hx : quadraticEvaluation w A ev x≠0) :
    Integers w ≃ₗ[Integers w] (quadraticEvaluation w A ev).range :=
  FiniteModuleImageFrame318.frame w (QuadraticFiber w A) (quadraticEvaluation w A ev) x hx
end FiniteCotangentImage318
