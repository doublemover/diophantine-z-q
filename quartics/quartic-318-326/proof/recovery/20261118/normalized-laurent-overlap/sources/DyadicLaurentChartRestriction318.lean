module
public import DyadicNormalizedLaurentSquare318
public import Mathlib.RingTheory.Localization.BaseChange
public section
noncomputable section
namespace DyadicLaurentChartRestriction318
open scoped TensorProduct
open DyadicNormalizedRatioCharts318
variable {P D : Type*} [CommRing P] [CommRing D] [Algebra P D]
variable (M : Submonoid P) [IsLocalization M D]
variable (B : Type*) [CommRing B] [Algebra P B] [Algebra D B] [IsScalarTower P D B]

/-- Localization of the actual integral subalgebra in the chosen ambient,
not a raw presentation localized before normalization. -/
@[expose] def localizedChart :
    D ⊗[P] integralClosure P B ≃ₐ[D] integralClosure D B :=
  (AlgEquiv.ofBijective (TensorProduct.toIntegralClosure P D B)
    (TensorProduct.toIntegralClosure_bijective_of_isLocalization (S:=D) (B:=B) M)).trans
      (restrictClosure (IsLocalization.algebraLid M D B))

theorem localizedChart_tmul (s : D) (x : integralClosure P B) :
    (localizedChart M B (s ⊗ₜ[P] x) : B) = algebraMap D B s * (x:B) := by
  letI := IsLocalization.tensorProduct_compatibleSMul M D D B
  change IsLocalization.algebraLid M D B
    (Algebra.TensorProduct.map (AlgHom.id D D) (integralClosure P B).val (s ⊗ₜ[P] x)) = _
  rw [Algebra.TensorProduct.map_tmul]
  change Algebra.TensorProduct.lidOfCompatibleSMul P D B (s ⊗ₜ[P] (x:B))=_
  rw [Algebra.TensorProduct.lidOfCompatibleSMul_tmul,Algebra.smul_def]

variable {B} {E : Type*} [CommRing E] [Algebra P E] [Algebra D E] [IsScalarTower P D E]
/-- Compatibility is on all elements of the localized normalized algebra, not
just its fraction-field isomorphism class. -/
theorem localizedChart_naturality (e : B ≃ₐ[D] E)
    (x : D ⊗[P] integralClosure P B) :
    localizedChart M E (Algebra.TensorProduct.congr (AlgEquiv.refl : D ≃ₐ[D] D)
      (restrictClosure (e.restrictScalars P)) x) =
      restrictClosure e (localizedChart M B x) := by
  induction x using TensorProduct.inductionOn with
  | zero => simp
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul d y =>
    apply Subtype.ext
    change (localizedChart M E (d ⊗ₜ[P] (restrictClosure (e.restrictScalars P) y)) : E) =
      e (localizedChart M B (d ⊗ₜ[P] y) : B)
    rw [localizedChart_tmul,localizedChart_tmul,map_mul,AlgEquiv.commutes] <;> rfl

section Concrete
open Polynomial DyadicNormalizedLaurentSquare318
variable (A : Type*) [CommRing A]

@[expose] def direction (atInfinity : Bool) : Overlap A ≃+* Overlap A :=
  if atInfinity then LaurentPolynomial.invert.toRingEquiv else RingEquiv.refl _
@[expose] def parameterMap (atInfinity : Bool) : A[X] →+* Overlap A :=
  (direction A atInfinity).toRingHom.comp (algebraMap A[X] (Overlap A))

theorem parameter_images (atInfinity : Bool) :
    parameterMap A atInfinity X = LaurentPolynomial.T (if atInfinity then -1 else 1) := by
  cases atInfinity <;> simp [parameterMap,direction,LaurentPolynomial.algebraMap_eq_toLaurent,
    Polynomial.toLaurent_X]

theorem actual_localization (atInfinity : Bool) :
    letI := (parameterMap A atInfinity).toAlgebra
    IsLocalization.Away (X : A[X]) (Overlap A) :=
  (IsLocalization.isLocalization_iff_of_ringEquiv (Submonoid.powers (X : A[X]))
    (direction A atInfinity)).mp (inferInstance : IsLocalization.Away (X:A[X]) (Overlap A))

/-- For either original parameter embedding, the affine chart after restricting
to its parameter unit open is identified with the integral closure over the
same actual Laurent ring. No generic normality assumption on B is required. -/
@[expose] def restrictToLaurent (atInfinity : Bool) (B : Type*) [CommRing B]
    [Algebra (Overlap A) B] :
    letI := (parameterMap A atInfinity).toAlgebra
    letI := ((algebraMap (Overlap A) B).comp (parameterMap A atInfinity)).toAlgebra
    Overlap A ⊗[A[X]] integralClosure A[X] B ≃ₐ[Overlap A] integralClosure (Overlap A) B := by
  letI := (parameterMap A atInfinity).toAlgebra
  letI := ((algebraMap (Overlap A) B).comp (parameterMap A atInfinity)).toAlgebra
  letI : IsScalarTower A[X] (Overlap A) B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsLocalization.Away (X : A[X]) (Overlap A) := actual_localization A atInfinity
  exact localizedChart (Submonoid.powers (X:A[X])) B
end Concrete
end DyadicLaurentChartRestriction318
