module
public import GeometricIntegralConstants318
public import SourceScalarExtension318
public import AffineGlobalFunction318
public import ActualQuotientConstantPullback318
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

public section
noncomputable section
namespace ActualSourceRationalConstants318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open scoped TensorProduct
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev X := ContactGlobalSmooth318.Model units
abbrev A := ContactKummerOrder318.SourceOrder units
abbrev p := ContactIntrinsicDifferentials318.structureMap units
abbrev j := SourceGlobalAffine318.chartEmbedding units
abbrev structuralConstant := ActualQuotientConstantPullback318.sourceConstant

local instance modelIntegral : IsIntegral X := ContactProjectiveModel318.model_integral units
local instance sourceDomain : IsDomain A := ContactKummerOrder318.source_domain units
local instance modelProper : IsProper p :=
  (ContactGlobalProper318.proper_integral_extension units).2.2
local instance topNonempty : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
local instance geometricDomain : IsDomain (AlgebraicClosure ℚ ⊗[ℚ] A) :=
  SourceScalarExtension318.scalarExtension_domain (AlgebraicClosure ℚ) units

lemma value_constant (a : ℚ) :
    AffineGlobalFunction318.value j (structuralConstant a) = algebraMap ℚ A a :=
  DFunLike.congr_fun (RingHom.ext_rat
    ((AffineGlobalFunction318.value j).comp structuralConstant) (algebraMap ℚ A)) a

lemma value_injective : Function.Injective (AffineGlobalFunction318.value j) := by
  intro r s h
  apply X.germToFunctionField_injective ⊤
  rw [← AffineGlobalFunction318.generic_value j r,
    ← AffineGlobalFunction318.generic_value j s, h]

/-- Every global regular function on the original complete source is an
original structural rational constant. Properness supplies integrality;
the actual source scalar-extension domain rules out extra constants. -/
theorem constant_bijective : Function.Bijective structuralConstant := by
  letI : Algebra ℚ Γ(X, ⊤) := structuralConstant.toAlgebra
  have hc : structuralConstant.IsIntegral := by
    exact (RingHom.isIntegral_of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv).surjective).trans _ _
      (isIntegral_appTop_of_universallyClosed p)
  have hi (r : Γ(X, ⊤)) : IsIntegral ℚ r := hc r
  let f : Γ(X, ⊤) →ₐ[ℚ] A :=
    { AffineGlobalFunction318.value j with
      commutes' := value_constant }
  refine ⟨structuralConstant.injective, ?_⟩
  intro r
  obtain ⟨a, ha⟩ := GeometricIntegralConstants318.integral_is_constant ((hi r).map f)
  refine ⟨a, value_injective ?_⟩
  exact (value_constant a).trans ha

end ActualSourceRationalConstants318
