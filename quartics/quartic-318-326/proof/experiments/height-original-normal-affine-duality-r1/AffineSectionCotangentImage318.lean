module
public import LocalSectionAffineChart318
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public section
noncomputable section
namespace AffineSectionCotangentImage318
open AlgebraicGeometry CategoryTheory LocalSectionAffineChart318
open scoped TensorProduct
set_option maxHeartbeats 1000000
universe u
variable {R : Type u} [CommRing R] [IsLocalRing R]
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
  {g : Spec (CommRingCat.of R) ⟶ X} (C : Data f g)

local instance scalarAlgebra : Algebra R C.ring := C.scalar.hom.toAlgebra
local instance evaluationAlgebra : Algebra C.ring R := C.evaluation.hom.toAlgebra

/-- Actual relative cotangent module of the normal-model affine chart,
specialized along its actual integral section. This is NOT Omega(R/R). -/
abbrev Cotangent := R ⊗[C.ring] KaehlerDifferential R C.ring

instance finite_cotangent : Module.Finite R (Cotangent C) := by
  letI : Algebra.FiniteType R C.ring := RingHom.finiteType_algebraMap.mp C.finite_type
  letI : Module.Finite C.ring (KaehlerDifferential R C.ring) := inferInstance
  infer_instance

@[expose] def differential (a : C.ring) : Cotangent C :=
  (1:R) ⊗ₜ[C.ring] KaehlerDifferential.D R C.ring a

variable (F : Type u) [Field F] [Algebra R F]
/-- Scalar extension of the actual integral cotangent specialization;
it retains the tangent direction of the original scheme point. -/
abbrev GenericCotangent := F ⊗[R] Cotangent C

@[expose] def toGeneric : Cotangent C →ₗ[R] GenericCotangent C F :=
  TensorProduct.mk R F (Cotangent C) 1

/-- The actual image of the integral cotangent module, not a freely
selected generator. Torsion in the integral module is allowed. -/
@[expose] def integralImage : Submodule R (GenericCotangent C F) :=
  (toGeneric C F).range

instance finite_image : Module.Finite R (integralImage C F) := by
  apply Module.Finite.of_surjective (toGeneric C F).rangeRestrict
  intro x
  obtain ⟨y,hy⟩ := x.property
  exact ⟨y,Subtype.ext hy⟩

lemma differential_mem (a : C.ring) : toGeneric C F (differential C a)∈integralImage C F :=
  ⟨differential C a,rfl⟩

/-- The actual image spans the whole scalar-extended cotangent space.
Neither dimension one nor a dualizing/Hodge identification is asserted. -/
theorem image_spans : Submodule.span F (Set.range (toGeneric C F))=⊤ := by
  apply top_unique
  intro z _
  induction z using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul a b =>
    have hb : toGeneric C F b∈Submodule.span F (Set.range (toGeneric C F)) :=
      Submodule.subset_span ⟨b,rfl⟩
    have hh := (Submodule.span F (Set.range (toGeneric C F))).smul_mem a hb
    simpa only [toGeneric,TensorProduct.mk_apply,TensorProduct.smul_tmul',smul_eq_mul,mul_one] using hh
  | add x y hx hy => exact Submodule.add_mem _ hx hy

/-- This freeness is of the finite integral IMAGE in a generic vector
space, not regularity of the arithmetic model or freeness of its entire
cotangent module. Rank one and the actual canonical comparison remain open. -/
theorem image_free [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R F] :
    Module.Free R (integralImage C F) := by
  letI : Module.IsTorsionFree R F := inferInstance
  letI : Module.IsTorsionFree R (GenericCotangent C F) := Module.IsTorsionFree.trans F
  letI : Module.IsTorsionFree R (integralImage C F) := inferInstance
  exact Module.free_of_finite_type_torsion_free'
end AffineSectionCotangentImage318
