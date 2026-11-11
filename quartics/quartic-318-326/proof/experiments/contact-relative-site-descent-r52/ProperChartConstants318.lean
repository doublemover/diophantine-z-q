module
public import GeometricIntegralConstants318
public import AffineGlobalFunction318
public import StructuralConstantPullback318
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public section
noncomputable section
namespace ProperChartConstants318
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {K A : Type u} [Field K] [CommRing A] [Algebra K A]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of K))
    (j : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion j]
    (hj : j ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K A)))

/-- The exact structural field map through the original Spec/sections comparison. -/
@[expose] def structuralMap : K →+* Γ(X, ⊤) :=
  p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom

include hj in
lemma value_constant (a : K) :
    AffineGlobalFunction318.value j (structuralMap p a) =
      algebraMap K A a := by
  rw [AffineGlobalFunction318.value_appTop]
  have hs := StructuralConstantPullback318.app_constant j _ p hj a
  change j.appTop (structuralMap p a) =
    structuralMap (Spec.map (CommRingCat.ofHom (algebraMap K A))) a at hs
  rw [hs]
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom
    ((Spec.map (CommRingCat.ofHom (algebraMap K A))).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a)) = _
  have hn := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap K A))) a
  exact (congrArg (Scheme.ΓSpecIso (CommRingCat.of A)).hom hn.symm).trans
    (Iso.inv_hom_id_apply _ _)

variable [IsIntegral X] [IsDomain A]
local instance : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
lemma value_injective : Function.Injective (AffineGlobalFunction318.value j) := by
  intro r s h
  apply X.germToFunctionField_injective ⊤
  rw [← AffineGlobalFunction318.generic_value j r,
    ← AffineGlobalFunction318.generic_value j s, h]

include hj in
/-- Properness and an actual geometrically integral affine chart determine
all global functions through the original structural field map. -/
theorem constant_bijective [IsProper p]
    [IsDomain (AlgebraicClosure K ⊗[K] A)] :
    Function.Bijective (structuralMap p) := by
  let : Algebra K Γ(X, ⊤) := (structuralMap p).toAlgebra
  have hc : (structuralMap p).IsIntegral :=
    (RingHom.isIntegral_of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).surjective).trans _ _
      (isIntegral_appTop_of_universallyClosed p)
  have hi (r : Γ(X, ⊤)) : IsIntegral K r := hc r
  let f : Γ(X, ⊤) →ₐ[K] A :=
    { AffineGlobalFunction318.value j with commutes' := value_constant p j hj }
  refine ⟨(structuralMap p).injective, ?_⟩
  intro r
  obtain ⟨a, ha⟩ := GeometricIntegralConstants318.integral_is_constant ((hi r).map f)
  exact ⟨a, value_injective j ((value_constant p j hj a).trans ha)⟩
end ProperChartConstants318
