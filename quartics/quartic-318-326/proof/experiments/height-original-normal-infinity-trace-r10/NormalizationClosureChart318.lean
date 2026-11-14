module
public import NormalizationSourceCompatibility318
public section
noncomputable section
namespace NormalizationClosureChart318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

/-- A whole affine chart with both literal ring maps retained. The
source square is necessary for transporting the original signed point. -/
structure Data {A B C : CommRingCat} {Y : Scheme}
    (ι : C →+* B) (s : A →+* C) (f : Spec B ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] (j : Spec A ⟶ Y) where
  chart : Spec C ⟶ f.normalization
  isOpen : IsOpenImmersion chart
  source : Spec.map (CommRingCat.ofHom ι) ≫ chart=f.toNormalization
  base : chart ≫ f.fromNormalization=Spec.map (CommRingCat.ofHom s) ≫ j

variable {A B : CommRingCat} {Y : Scheme}
  (φ : A ⟶ B) (j : Spec A ⟶ Y) [IsOpenImmersion j]
  (f : Spec B ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
  (hf : f=Spec.map φ ≫ j)

/-- The actual integral-closure affine chart is constructed by the
native normalization section isomorphism. Its two squares are the exact
existing normalization source/base compatibility theorems. -/
@[expose] def data :
    letI := φ.hom.toAlgebra
    Data (A:=A) (B:=B) (C:=CommRingCat.of (integralClosure A B))
      (integralClosure A B).val.toRingHom (algebraMap A (integralClosure A B)) f j := by
  letI := φ.hom.toAlgebra
  let e := InfinityGlobalChart318.sectionsEquiv_of_factor φ j f hf
  let hU := (NormalizationBaseCompatibility318.target_affine j).preimage f.fromNormalization
  let E := Scheme.Spec.mapIso e.toCommRingCatIso.op
  refine ⟨E.hom ≫ hU.fromSpec,?_,?_,?_⟩
  · infer_instance
  · exact NormalizationSourceCompatibility318.factored_chart_original φ j f hf
      (AlgEquiv.refl A (integralClosure A B))
  · exact NormalizationBaseCompatibility318.factored_chart_over_base φ j f hf
      (AlgEquiv.refl A (integralClosure A B))
end NormalizationClosureChart318
