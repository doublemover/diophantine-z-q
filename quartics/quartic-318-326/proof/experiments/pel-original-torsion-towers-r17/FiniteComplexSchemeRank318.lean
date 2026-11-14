module
public import FiniteEtaleComplexSections318
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public section
noncomputable section
namespace FiniteComplexSchemeRank318
open AlgebraicGeometry CategoryTheory
variable {X : Scheme} (π : X⟶Spec (CommRingCat.of ℂ))
local instance : Algebra ℂ Γ(X,⊤) := FiniteEtaleComplexSections318.algebra π
/-- Native scheme rank over the original complex base is the dimension
of the WHOLE actual global algebra, with its structural scalar action. -/
lemma rank_eq [IsFinite π] [Flat π] (c : Spec (CommRingCat.of ℂ)) :
    π.finrank c=Module.finrank ℂ Γ(X,⊤) := by
  letI : IsAffine X := isAffine_of_isAffineHom π
  letI : Module.Finite ℂ Γ(X,⊤) := FiniteEtaleComplexSections318.finite π
  let f := Spec.map (CommRingCat.ofHom
    (FiniteEtaleComplexSections318.coefficientMap π))
  letI : IsFinite f := by
    change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap ℂ Γ(X,⊤))))
    infer_instance
  letI : Flat f := by
    change Flat (Spec.map (CommRingCat.ofHom (algebraMap ℂ Γ(X,⊤))))
    infer_instance
  have hf : X.isoSpec.hom≫f=π :=
    FiniteEtaleComplexSections318.coefficient_square π
  calc
    π.finrank c=(X.isoSpec.hom≫f).finrank c :=
      congrArg (fun g => g.finrank c) hf.symm
    _=f.finrank c := congrFun (Scheme.Hom.finrank_comp_left_of_isIso X.isoSpec.hom f) c
    _=Module.finrank ℂ Γ(X,⊤) := by
      change (Spec.map (CommRingCat.ofHom (algebraMap ℂ Γ(X,⊤)))).finrank c=_
      rw [Scheme.Hom.finrank_SpecMap_algebraMap,Module.rankAtStalk_eq_finrank_of_free]
      rfl
end FiniteComplexSchemeRank318
