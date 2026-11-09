module
public import OriginalCoverRestrictionCompatibility318
public import ModuleLocalIsomorphism318
public section
noncomputable section
namespace InverseImageBasisIsoGluing318
open AlgebraicGeometry CategoryTheory TopologicalSpace
open ModuleLocalGluing318 OpenSheafTransition318
set_option maxHeartbeats 2600000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M N : X.Modules)
  (e : ∀ U : Y.affineOpens, M.over (f ⁻¹ᵁ U.1) ≅ N.over (f ⁻¹ᵁ U.1))
  (he : ∀ (U V : Y.affineOpens) (h : V.1 ≤ U.1),
    restrictIso (e U) (f.preimage_mono h) = e V)

include he in
/-- The original affine basis refines every base overlap. Pulling those
refinements back proves agreement on every source subopen, without assuming
that the inverse-image opens form a basis of the covering scheme. -/
lemma component_compatible (U V : Y.affineOpens) (Z : X.Opens)
    (hU : Z ≤ f ⁻¹ᵁ U.1) (hV : Z ≤ f ⁻¹ᵁ V.1) (s : Γ(M,Z)) :
    component (e U) Z hU s = component (e V) Z hV s := by
  apply TopCat.Presheaf.IsSheaf.section_ext N.isSheaf
  intro x hx
  have hxUV : f x ∈ (U.1 ⊓ V.1 : Y.Opens) := ⟨hU hx,hV hx⟩
  obtain ⟨_,⟨W,hW,rfl⟩,hxW,hWUV⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hxUV (U.1 ⊓ V.1).isOpen
  let A : Y.affineOpens := ⟨W,hW⟩
  have hAU : A.1 ≤ U.1 := fun y hy => (hWUV hy).1
  have hAV : A.1 ≤ V.1 := fun y hy => (hWUV hy).2
  let Q : X.Opens := Z ⊓ (f ⁻¹ᵁ A.1)
  have hQ : Q ≤ Z := inf_le_left
  have hQA : Q ≤ f ⁻¹ᵁ A.1 := inf_le_right
  refine ⟨Q,hQ,⟨hx,hxW⟩,?_⟩
  change res N hQ (component (e U) Z hU s) = res N hQ (component (e V) Z hV s)
  rw [component_natural,component_natural]
  have hi := congrArg (fun d => component d Q hQA (res M hQ s)) (he U A hAU)
  have hj := congrArg (fun d => component d Q hQA (res M hQ s)) (he V A hAV)
  simp only [component_restrict] at hi hj
  exact hi.trans hj.symm

@[expose] def data : LocalData M N (fun U : Y.affineOpens => f ⁻¹ᵁ U.1) where
  map U Z hZ := (component (e U) Z hZ).toLinearMap
  natural U Z W hZ h s := component_natural (e U) Z W hZ h s
  compatible := component_compatible f M N e he

lemma cover : (⊤ : X.Opens) ≤ iSup (fun U : Y.affineOpens => f ⁻¹ᵁ U.1) :=
  LinePullbackFrames318.preimage_cover f (fun U : Y.affineOpens => U.1)
    (AffineMorphismGlobalLine318.cover (Y:=Y))

/-- Actual global sheaf isomorphism, with an independently glued inverse.
Only proved compatibility on the original affine base basis is required. -/
@[expose] def iso : M ≅ N :=
  ModuleLocalIsomorphism318.iso (data f M N e he) (cover f)
    (fun U Z hZ => (component (e U) Z hZ).bijective)

lemma hom_component (U : Y.affineOpens) (Z : X.Opens)
    (hZ : Z ≤ f ⁻¹ᵁ U.1) (s : Γ(M,Z)) :
    (iso f M N e he).hom.app Z s = component (e U) Z hZ s := by
  have hh := value_subopen (data f M N e he) (cover f) Z Z le_rfl U hZ s
  simpa only [res_self] using hh
end InverseImageBasisIsoGluing318
