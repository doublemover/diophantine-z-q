module
public import FiniteLineTargetNeighborhood318
public section
noncomputable section
namespace FiniteLineTargetCover318
open AlgebraicGeometry CategoryTheory TopologicalSpace
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y:Scheme.{u}} (f:X⟶Y) [IsFinite f] (M:X.Modules)
    {κ:Type u} (V:κ→X.Opens) (hc:(⊤:X.Opens)≤⨆i,V i)
    (frames:∀i,SheafOfModules.unit (V i).toScheme.ringCatSheaf≅M.restrict (V i).ι)
include hc frames in
/-- A genuine affine target neighborhood trivializes the original line
on its entire inverse image, even when the source line is not globally free. -/
lemma exists_affine_frame (y:Y):∃U:Y.Opens,y∈U ∧ IsAffineOpen U ∧ Nonempty
    (SheafOfModules.unit (f⁻¹ᵁU).toScheme.ringCatSheaf≅M.restrict (f⁻¹ᵁU).ι):=by
  obtain ⟨U,hU,hy,_⟩:=exists_isAffineOpen_mem_and_subset (show y∈(⊤:Y.Opens) from trivial)
  obtain ⟨a,ha,he⟩:=FiniteLineTargetNeighborhood318.exists_frame f M V hc frames U hU ⟨y,hy⟩
  exact ⟨Y.basicOpen a,ha,hU.basicOpen a,he⟩
/-- An actual target cover, chosen from the preceding proven neighborhoods. -/
@[expose] def neighborhood (y:Y):Y.Opens:=(exists_affine_frame f M V hc frames y).choose
lemma mem_neighborhood (y:Y):y∈neighborhood f M V hc frames y:=
  (exists_affine_frame f M V hc frames y).choose_spec.1
lemma affine_neighborhood (y:Y):IsAffineOpen (neighborhood f M V hc frames y):=
  (exists_affine_frame f M V hc frames y).choose_spec.2.1
@[expose] def frame (y:Y):
    SheafOfModules.unit (f⁻¹ᵁneighborhood f M V hc frames y).toScheme.ringCatSheaf≅
      M.restrict (f⁻¹ᵁneighborhood f M V hc frames y).ι:=
  (exists_affine_frame f M V hc frames y).choose_spec.2.2.some
lemma cover_top:(⊤:Y.Opens)≤⨆y,neighborhood f M V hc frames y:=by
  intro y _
  exact Opens.mem_iSup.mpr ⟨y,mem_neighborhood f M V hc frames y⟩
lemma preimage_cover_top:(⊤:X.Opens)≤⨆y,f⁻¹ᵁneighborhood f M V hc frames y:=by
  intro x _
  exact Opens.mem_iSup.mpr ⟨f x,mem_neighborhood f M V hc frames (f x)⟩
lemma frame_hom_inv (y:Y):
    (frame f M V hc frames y).hom≫(frame f M V hc frames y).inv=𝟙 _ :=
  (frame f M V hc frames y).hom_inv_id
lemma frame_inv_hom (y:Y):
    (frame f M V hc frames y).inv≫(frame f M V hc frames y).hom=𝟙 _ :=
  (frame f M V hc frames y).inv_hom_id
end FiniteLineTargetCover318
