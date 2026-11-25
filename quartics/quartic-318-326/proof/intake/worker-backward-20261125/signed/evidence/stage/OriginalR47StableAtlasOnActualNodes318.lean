module
public import OriginalR47ActualArithmeticSmoothOpen318
public import OriginalR47ActualBadNodeAt318
public import OriginalR47CurveFiniteActualClosed318
public import OriginalR47RelativeArithmeticRetained318
public section
noncomputable section

namespace OriginalR47StableAtlasOnActualNodes318

open AlgebraicGeometry CategoryTheory Set TopologicalSpace
open OriginalR47RelativeArithmeticRound318 (OnTrait ThickOnTrait)
open OriginalR47ActualArithmeticTermination318 (GenericRead)
open OriginalR47ActualArithmeticSmoothOpen318 (smoothOpen)
open OriginalR47ActualBadNodeAt318 (DoubleNode)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type} [CommRing R] [IsDedekindDomain R]
local notation "S" => Spec (CommRingCat.of R)
local notation "η" => genericPoint S
variable {X : Scheme} (s : X ⟶ S) [IsProper s]
variable (P : S ⟶ X) (hP : P ≫ s = 𝟙 S)

include hP in
/-- Starting from the original old proper stable-map scheme and its
actual paired local charts, derive the finite closed old centre family,
build the relative terminal resolution, and preserve the one whole
retained section. In comparison with the component-generic route this
uses the exact double-origin node window and needs no dimension,
component census, independently supplied finite list, thickness bound,
or selected replacement marked point. -/
theorem on_same_nodes
    (hGeneric : ∀ x : X, s x = η → x ∈ smoothOpen s)
    (good : ∀ x : X, x ∈ smoothOpen s → s x ≠ η → OnTrait s x)
    (nodal : ∀ x : X, x ∉ smoothOpen s → Nonempty (DoubleNode s x)) :
    ∃ (Y : Scheme) (r : Y ⟶ X), IsProper r ∧
      (∀ y : Y, (r ≫ s) y ≠ η → OnTrait (r ≫ s) y) ∧
      (∀ x : X, _root_.IsConnected (r ⁻¹' ({x} : Set X))) ∧
      GenericRead s r ∧ ∃! Q : S ⟶ Y, Q ≫ r = P := by
  classical
  let D : Set X := (smoothOpen s : Set X)ᶜ
  have hD : IsClosed D := (smoothOpen s).2.isClosed_compl
  have hvert (x : X) (hx : x ∈ D) : s x ≠ η := fun h => hx (hGeneric x h)
  have hnode (x : X) (hx : x ∈ D) : DoubleNode s x := Classical.choice (nodal x hx)
  have hclosed (x : X) (hx : x ∈ D) : IsClosed ({x} : Set X) :=
    OriginalR47ActualBadNodeAt318.closed s x (hnode x hx) (hvert x hx)
  have hf : D.Finite := OriginalR47CurveFiniteActualClosed318.support s D hD hvert hclosed
  let Z : Set X := {x ∈ D | ¬ OnTrait s x}
  have hsub : Z ⊆ D := fun _ hx => hx.1
  have hsite (x : Z) : ∃ d, Nonempty (ThickOnTrait s x.val d) :=
    (OriginalR47ActualBadNodeAt318.terminal_or_active s x.val (hnode x.val x.property.1)).resolve_left
      x.property.2
  choose depth Atlas using hsite
  letI : X.IsSeparated := ⟨by rw [← terminal.comp_from s]; infer_instance⟩
  exact OriginalR47RelativeArithmeticRetained318.resolve s P hP Z (hf.subset hsub)
    (fun x hx => hclosed x (hsub hx)) depth Atlas
    (fun x hx hp => by
      by_cases h : x ∈ D
      · exact not_not.mp (fun hn => hx ⟨h,hn⟩)
      · exact good x (not_not.mp (show ¬ (x ∉ smoothOpen s) from h)) hp)
    (fun x hx => hvert x (hsub hx))

end OriginalR47StableAtlasOnActualNodes318

#print axioms OriginalR47StableAtlasOnActualNodes318.on_same_nodes
