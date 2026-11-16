module
public import AffineDominantNormRestriction318
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public section
noncomputable section
namespace FunctionFieldGluing318
open AlgebraicGeometry CategoryTheory TopologicalSpace
set_option maxHeartbeats 350000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (Y:Scheme.{u}) [IsIntegral Y]
lemma intersection_nonempty (U V:Y.Opens) [Nonempty U] [Nonempty V]:Nonempty (U ⊓ V : Y.Opens):=by
  have hu:genericPoint Y∈U:=
    ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr (by simpa using (inferInstance:Nonempty U))
  have hv:genericPoint Y∈V:=
    ((genericPoint_spec Y).mem_open_set_iff V.isOpen).mpr (by simpa using (inferInstance:Nonempty V))
  exact ⟨⟨genericPoint Y,hu,hv⟩⟩
/-- Sections on an actual open cover with the same original generic germ
are compatible. No affine or reduced-point replacement is used. -/
lemma compatible {ι:Type*} (V:ι→Y.Opens) [∀i,Nonempty (V i)]
    (s:∀i,Γ(Y,V i)) (z:Y.functionField)
    (hs:∀i,Y.germToFunctionField (V i) (s i)=z):
    TopCat.Presheaf.IsCompatible Y.presheaf V s:=by
  intro i j
  letI:Nonempty (V i ⊓ V j : Y.Opens):=intersection_nonempty Y (V i) (V j)
  apply Y.germToFunctionField_injective (V i⊓V j)
  rw [AffineDominantNormRestriction318.germ_restrict,
    AffineDominantNormRestriction318.germ_restrict,hs i,hs j]
/-- A genuine section on the whole open, characterized by its original
function-field germ, obtained from actual sheaf gluing. -/
lemma exists_section {ι:Type*} (V:ι→Y.Opens) [∀i,Nonempty (V i)]
    (U:Y.Opens) [Nonempty U] (inc:∀i,V i⟶U) (cover:U ≤ iSup V)
    (s:∀i,Γ(Y,V i)) (z:Y.functionField)
    (hs:∀i,Y.germToFunctionField (V i) (s i)=z):
    ∃a:Γ(Y,U),Y.germToFunctionField U a=z:=by
  obtain ⟨a,ha,-⟩:=Y.sheaf.existsUnique_gluing' V U inc cover s (compatible Y V s z hs)
  change ∀i, Y.presheaf.map (inc i).op a = s i at ha
  obtain ⟨x⟩:Nonempty U:=inferInstance
  have hx:x.1∈iSup V:=cover x.2
  obtain ⟨i,hi⟩:=Opens.mem_iSup.mp hx
  refine ⟨a,?_⟩
  rw [←AffineDominantNormRestriction318.germ_restrict Y (inc i) a,ha i,hs i]
end FunctionFieldGluing318
