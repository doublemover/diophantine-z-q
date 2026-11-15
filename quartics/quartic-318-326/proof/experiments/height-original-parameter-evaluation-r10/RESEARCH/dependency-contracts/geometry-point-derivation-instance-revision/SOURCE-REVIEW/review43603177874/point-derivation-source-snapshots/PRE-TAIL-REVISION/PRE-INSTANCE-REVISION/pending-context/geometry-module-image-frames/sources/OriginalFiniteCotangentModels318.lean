module
public import FiniteCotangentImage318
public import OriginalFiniteImageModels318
public section
noncomputable section
namespace OriginalFiniteCotangentModels318
open NumberField ActualFinitePlaceIntegers318 OriginalPointFinitePlaceRoots318
open OriginalExcludedPlaceData318
variable (c : Fin 4 → ℚˣ) (t : ℚ)
  (hn : ∀ j, RationalContactPoint318.parameters c t j≠0) (i : Fin 4)
  (A : BadPlace c t → Type*) [∀ b, CommRing (A b)]
  [∀ b, Algebra (Integers b.val) (A b)] [∀ b, Algebra (A b) (Integers b.val)]
  [∀ b, IsScalarTower (Integers b.val) (A b) (Integers b.val)]
  [∀ b, Algebra.EssFiniteType (Integers b.val) (A b)]
  (ev : (b : BadPlace c t) → FiniteCotangentImage318.Fiber b.val (A b) →ₗ[Integers b.val] K c t)
  (s : (b : BadPlace c t) → Fin 2 → FiniteCotangentImage318.QuadraticFiber b.val (A b))
  (hs : ∀ (b : BadPlace c t) (n : Fin 2),
    FiniteCotangentImage318.quadraticEvaluation b.val (A b) (ev b) (s b n)=
      (![ContactBicanonicalPointHeight318.a0 c t hn i,
        ContactBicanonicalPointHeight318.a1 c t hn i] n))

/-- Specialize the image producer to the finite cotangent tensor square.
Actual finite-type charts, integral points, functionals and ORIGINAL lifts are
still required. No finite-generation/free-frame premise appears. -/
@[expose] def evaluationData : OriginalFiniteImageModels318.EvaluationData c t hn i
    (fun b => FiniteCotangentImage318.QuadraticFiber b.val (A b)) where
  evaluation b := FiniteCotangentImage318.quadraticEvaluation b.val (A b) (ev b)
  originalSection := s
  section_value := hs

@[expose] def finiteModels : OriginalFiniteModelFrames318.FiniteModels c t hn i :=
  OriginalFiniteImageModels318.finiteModels c t hn i
    (fun b => FiniteCotangentImage318.QuadraticFiber b.val (A b))
    (evaluationData c t hn i A ev s hs)

/-- Exact image identity at every excluded place. Calling it a dualizing or
maximal-model lattice requires an additional geometric comparison. -/
theorem model_eq_image (b : BadPlace c t) :
    (finiteModels c t hn i A ev s hs).model b=
      (FiniteCotangentImage318.quadraticEvaluation b.val (A b) (ev b)).range := rfl
end OriginalFiniteCotangentModels318
