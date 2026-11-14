module
public import OriginalTensorScalarNormalization318
public section
noncomputable section
namespace OriginalEquivariantFrameBijection318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u
variable {X : Scheme.{u}} (L K D : Line X)
local notation "I" => L.object ≅ K.object
local notation "F" => OriginalLineFrameUnitTorsor318.Frames D
lemma isom_one (e : I) : OriginalLineIsomUnitTorsor318.act L K 1 e=e := by
  apply Iso.ext
  change ModuleScalar318.map L.object 1 ≫ e.hom=e.hom
  rw [ModuleScalarComposition318.map_one,Category.id_comp]
lemma frame_action_injective (e : F) :
    Function.Injective (fun u : Γ(X,⊤)ˣ => OriginalLineFrameUnitTorsor318.act D u e) := by
  intro u v h
  have hh := congrArg (OriginalLineFrameUnitTorsor318.ratio D e) h
  simpa only [OriginalLineFrameUnitTorsor318.act_ratio] using hh
/-- An actual equivariant map between these two original unit torsors is
bijective as soon as an actual witness is supplied in the reverse direction.
Neither torsor is assumed inhabited; empty tests are included. -/
theorem bijective (f : I → F) (g : F → I)
    (heq : ∀ (u : Γ(X,⊤)ˣ) (e : I),
      f (OriginalLineIsomUnitTorsor318.act L K u e)=
        OriginalLineFrameUnitTorsor318.act D u (f e)) : Function.Bijective f := by
  constructor
  · intro e d hed
    let u := OriginalLineIsomUnitTorsor318.ratio L K e d
    have hu : OriginalLineIsomUnitTorsor318.act L K u e=d :=
      OriginalLineIsomUnitTorsor318.ratio_act L K e d
    have hh : OriginalLineFrameUnitTorsor318.act D u (f e)=
        OriginalLineFrameUnitTorsor318.act D 1 (f e) := by
      rw [←heq,hu,OriginalLineFrameUnitTorsor318.one_act]
      exact hed.symm
    have h1 : u=1 := frame_action_injective D (f e) hh
    rw [h1,isom_one] at hu
    exact hu
  · intro d
    let e := g d
    let u := OriginalLineFrameUnitTorsor318.ratio D (f e) d
    refine ⟨OriginalLineIsomUnitTorsor318.act L K u e,?_⟩
    rw [heq]
    exact OriginalLineFrameUnitTorsor318.ratio_act D (f e) d
end OriginalEquivariantFrameBijection318
