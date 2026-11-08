module
public import OpenClutchedLine318
public import ClutchedCoordinateGenerators318
public import ModuleOpenIsoCriterion318
public section
noncomputable section
namespace OpenClutchedTrivialization318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open OpenClutchedLine318
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}}
lemma topIso_restrict {U V:X.Opens} (h:V≤U) (s:Γ(X,U)):
    (X.homOfLE h).appTop (U.topIso.inv s)=
      V.topIso.inv (X.presheaf.map (homOfLE h).op s):=by
  change ((U.topIso.inv≫(X.homOfLE h).appTop) s)=
    ((X.presheaf.map (homOfLE h).op≫V.topIso.inv) s)
  congr 1
  simp only [Scheme.Opens.topIso_inv,Scheme.homOfLE_appTop,←Functor.map_comp]
  congr 1

variable (U V:X.Opens) (a:Γ(X,U⊓V)ˣ)
  (s₀:Γ(X,U)ˣ) (s₁:Γ(X,V)ˣ)
  (hs:X.presheaf.map (homOfLE (show U⊓V≤U from inf_le_left)).op s₀.val=
    X.presheaf.map (homOfLE (show U⊓V≤V from inf_le_right)).op s₁.val*a.val)
include hs in
lemma compatible:
    (leftInclusion U V).appTop (U.topIso.inv s₀.val)=
      (rightInclusion U V).appTop (V.topIso.inv s₁.val)*transition U V a:=by
  rw [leftInclusion,rightInclusion,topIso_restrict,topIso_restrict,hs]
  exact map_mul (U⊓V: X.Opens).topIso.inv.hom _ _
/-- Actual coordinate map from the unit module, retaining the prescribed
unit coefficients on both whole charts. -/
@[expose] def map:ClutchedModule318.unit X⟶line U V a:=
  ClutchedModuleTop318.map U.ι V.ι (leftInclusion U V) (rightInclusion U V)
    (square U V) (transition U V a) (U.topIso.inv s₀.val) (V.topIso.inv s₁.val)
    (compatible U V a s₀ s₁ hs)
lemma first_isIso:IsIso ((Scheme.Modules.restrictFunctor U.ι).map (map U V a s₀ s₁ hs)):=
  ClutchedCoordinateGenerators318.first_isIso U.ι V.ι (leftInclusion U V) (rightInclusion U V)
    (square U V) (transition U V a) _ _ (compatible U V a s₀ s₁ hs)
    (transition_unit U V a) (right_range U V) (s₀.isUnit.map U.topIso.inv.hom)
lemma second_isIso:IsIso ((Scheme.Modules.restrictFunctor V.ι).map (map U V a s₀ s₁ hs)):=
  ClutchedCoordinateGenerators318.second_isIso U.ι V.ι (leftInclusion U V) (rightInclusion U V)
    (square U V) (transition U V a) _ _ (compatible U V a s₀ s₁ hs)
    (left_range U V) (s₁.isUnit.map V.topIso.inv.hom)
lemma isIso (hc:U⊔V=⊤):IsIso (map U V a s₀ s₁ hs):=by
  let C:ULift.{u} Bool→X.Opens:=fun b=>if b.down then V else U
  have hC:⊤ ≤ iSup C:=by
    intro x _
    have hx:x∈U⊔V:=by rw [hc];trivial
    rcases hx with hx|hx
    · exact Opens.mem_iSup.mpr ⟨⟨false⟩,hx⟩
    · exact Opens.mem_iSup.mpr ⟨⟨true⟩,hx⟩
  apply ModuleOpenIsoCriterion318.of_restrictions (map U V a s₀ s₁ hs) C hC
  intro b
  rcases b with ⟨b⟩
  cases b
  · exact first_isIso U V a s₀ s₁ hs
  · exact second_isIso U V a s₀ s₁ hs
/-- A genuine module-sheaf trivialization for a unit coboundary, not an
identification of isomorphism classes or a Picard-group assertion. -/
@[expose] def iso (hc:U⊔V=⊤):ClutchedModule318.unit X≅line U V a:=by
  letI:=isIso U V a s₀ s₁ hs hc
  exact asIso (map U V a s₀ s₁ hs)
lemma iso_hom (hc:U⊔V=⊤):(iso U V a s₀ s₁ hs hc).hom=map U V a s₀ s₁ hs:=rfl
end OpenClutchedTrivialization318
