module
public import OpenUnitNorm318
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Topology.Sheaves.Functors
public section
noncomputable section
namespace StructureUnitsSheaf318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
set_option maxHeartbeats 450000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
/-- Invertible regular functions form an actual sheaf: both a coefficient
and its inverse are glued in the original structure sheaf. -/
lemma isSheaf {S:TopCat.{u}} (F:S.Sheaf CommRingCat.{u}):
    TopCat.Presheaf.IsSheaf (F.obj⋙OpenUnitNorm318.unitsFunctor):=by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι V s hs
  let a (i:ι):F.obj.obj (op (V i)):=Units.val (s i)
  let b (i:ι):F.obj.obj (op (V i)):=(s i).inv
  have ha:TopCat.Presheaf.IsCompatible F.obj V a:=by
    intro i j
    exact congrArg Units.val (hs i j)
  have hb:TopCat.Presheaf.IsCompatible F.obj V b:=by
    intro i j
    exact congrArg Units.inv (hs i j)
  obtain ⟨av,hav,-⟩:=F.existsUnique_gluing V a ha
  obtain ⟨bv,hbv,-⟩:=F.existsUnique_gluing V b hb
  have hab:av*bv=1:=by
    apply F.eq_of_locally_eq V
    intro i
    rw [map_mul,map_one,hav i,hbv i]
    exact (s i).val_inv
  have hba:bv*av=1:=by rw [mul_comm,hab]
  let z:(F.obj.obj (op (iSup V)))ˣ:=⟨av,bv,hab,hba⟩
  refine ⟨z,?_,?_⟩
  · intro i
    apply Units.ext
    exact hav i
  · intro z' hz'
    apply Units.ext
    apply F.eq_of_locally_eq V
    intro i
    exact (congrArg Units.val (hz' i)).trans (hav i).symm
/-- The actual sheaf of invertible regular functions of a Scheme. -/
@[expose] def units (Y:Scheme.{u}):TopCat.Sheaf CommGrpCat Y.carrier:=
  ⟨Y.presheaf⋙OpenUnitNorm318.unitsFunctor,isSheaf Y.sheaf⟩
@[expose] def pushedUnits {X Y:Scheme.{u}} (f:X⟶Y):TopCat.Sheaf CommGrpCat Y.carrier:=
  ⟨(f.base _* X.presheaf)⋙OpenUnitNorm318.unitsFunctor,
    isSheaf ⟨f.base _* X.presheaf,TopCat.Sheaf.pushforward_sheaf_of_sheaf f.base X.sheaf.property⟩⟩
variable {X Y:Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f:X⟶Y) [IsDominant f] [IsFinite f] (hY:NormalAffineBasis318.HasBasis Y)
/-- The actual norm is a morphism of the genuine unit sheaves. -/
@[expose] def norm:pushedUnits f⟶units Y:=⟨OpenUnitNorm318.norm f hY⟩
lemma norm_app (U:Y.Opens) (s:Γ(X,f⁻¹ᵁU)ˣ):
    (norm f hY).hom.app (op U) s=(OpenUnitNorm318.norm f hY).app (op U) s:=rfl
end StructureUnitsSheaf318
