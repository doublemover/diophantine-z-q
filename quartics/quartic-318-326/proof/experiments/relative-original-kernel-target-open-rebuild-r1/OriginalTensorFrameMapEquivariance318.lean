module
public import OriginalEquivariantFrameBijection318
public section
noncomputable section
namespace OriginalTensorFrameMapEquivariance318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u
variable {X : Scheme.{u}} (A B D : Line X) (I : X.Modules)
    (c : SheafOfModules.unit X.ringCatSheaf ≅ IntrinsicTensorSheaf318.tensor I A.object)
    (d : IntrinsicTensorSheaf318.tensor I B.object ≅ D.object)
/-- Entire original tensor/conjugation map, with its literal two
comparison isomorphisms. No duality triangle identity is assumed. -/
@[expose] def map (e : A.object ≅ B.object) : OriginalLineFrameUnitTorsor318.Frames D :=
  c ≪≫ TensorSheafFunctor318.congr (Iso.refl I) e ≪≫ d
lemma equivariant (u : Γ(X,⊤)ˣ) (e : A.object ≅ B.object) :
    map A B D I c d (OriginalLineIsomUnitTorsor318.act A B u e)=
      OriginalLineFrameUnitTorsor318.act D u (map A B D I c d e) := by
  unfold map OriginalLineIsomUnitTorsor318.act OriginalLineAutomorphismUnits318.iso
  rw [OriginalTensorScalarNormalization318.right_trans,
    OriginalTensorScalarNormalization318.right_scalar]
  have hc : (StructureLineAutomorphisms318.iso X u).hom ≫ c.hom=
      c.hom ≫ (ModuleScalarComposition318.unitIso
        (IntrinsicTensorSheaf318.tensor I A.object) u).hom := by
    simpa only [OriginalTensorScalarNormalization318.structure_scalar,Iso.trans_hom] using
      congrArg Iso.hom (OriginalTensorScalarNormalization318.scalar_natural c u)
  apply Iso.ext
  simp only [OriginalLineFrameUnitTorsor318.act,Iso.trans_hom,←Category.assoc]
  rw [←hc]
/-- Bijection follows from full scalar normalization and actual reverse
witnesses, not an imposed inverse law for the old tensor cancellation. -/
lemma bijective (g : OriginalLineFrameUnitTorsor318.Frames D → (A.object ≅ B.object)) :
    Function.Bijective (map A B D I c d) :=
  OriginalEquivariantFrameBijection318.bijective A B D _ g (equivariant A B D I c d)
end OriginalTensorFrameMapEquivariance318
