module
public import DominantFunctionField318
public section
noncomputable section
namespace CommonOpenFunctionField318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {U X Y:Scheme.{u}} [IrreducibleSpace U] [IrreducibleSpace X] [IrreducibleSpace Y]
    (a:U⟶X) (b:U⟶Y) [IsOpenImmersion a] [IsOpenImmersion b]
    (f:X⟶Y) [IsDominant f]

lemma map_congr {V W:Scheme.{u}} [IrreducibleSpace V] [IrreducibleSpace W]
    {g h:V⟶W} [IsDominant g] [IsDominant h] (e:g=h):
    DominantFunctionField318.map g=DominantFunctionField318.map h:=by
  cases e
  rfl

/-- An actual map agreeing with two actual dense-open embeddings induces
an isomorphism on the actual generic stalks, with precisely that stalk map. -/
theorem actual_generic_iso (h:a≫f=b):IsIso (DominantFunctionField318.map f):=by
  letI:IsDominant a:=⟨IsOpenMap.denseRange_of_isPreirreducibleSpace a a.isOpenEmbedding.isOpenMap⟩
  letI:IsDominant b:=⟨IsOpenMap.denseRange_of_isPreirreducibleSpace b b.isOpenEmbedding.isOpenMap⟩
  have he:=map_congr h
  rw [DominantFunctionField318.map_comp,DominantFunctionField318.map_open a,
    DominantFunctionField318.map_open b] at he
  haveI:IsIso (DominantFunctionField318.map f≫(OpenFunctionField318.fieldIso a).hom):=by
    rw [he]
    infer_instance
  have hf:DominantFunctionField318.map f=
      (DominantFunctionField318.map f≫(OpenFunctionField318.fieldIso a).hom)≫
        (OpenFunctionField318.fieldIso a).inv:=by simp
  rw [hf]
  infer_instance
end CommonOpenFunctionField318
