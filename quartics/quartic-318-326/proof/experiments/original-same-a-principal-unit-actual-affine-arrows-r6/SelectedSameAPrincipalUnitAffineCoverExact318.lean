module

public import SelectedSameAPrincipalUnitAffineTopRow318
public import SelectedSameAConstantAffineCoverProduced318

/-!
Assemble the actual pushed-forward normalized line row on a genuine
affine atlas of the original surface. The local splits are derived
from the closed-fibre and first-order frame calculations, not given
as cover data. No comparison to the old KS class.
-/

public section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace SelectedSameAPrincipalUnitAffineCoverExact318

open SelectedSameAActualNilpotentLineGluing318 (AdditiveCocycle unitCocycle)
open SelectedSameAConstantPrincipalLine318 (constantScheme constantCocycle markedEpsilon markedEpsilon_sq)
open SelectedSameAPrincipalUnitPushforwardArrows318 (unit V)
open SelectedSameAPrincipalUnitBoundary318
open SelectedSameAConstantAffineCoverProduced318
open SelectedSameAConstantTargetTriangle318 (sp)
open SelectedActualAdditiveStalkLocalExact318

universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {A : Scheme.{u}}
variable (a : A ⟶ Spec (CommRingCat.of k))
variable {I J : Type u} (U : I → A.Opens) (c : AdditiveCocycle U)
variable (hc : (⊤ : A.Opens) ≤ ⨆ i, U i)
variable (M : (constantScheme a).Modules)
variable (f : ∀ i, unit ((V a U i).toScheme) ≅ M.restrict (V a U i).ι)
variable (hframe : LineFrameCocycle318.cocycle M (V a U) f =
  unitCocycle (V a U) (markedEpsilon a) (markedEpsilon_sq a) (constantCocycle a U c))

section GivenAtlas

variable (B : J → Type u) [∀ j, CommRing (B j)] [∀ j, Algebra k (B j)]
variable (j : ∀ t, Spec (CommRingCat.of (B t)) ⟶ A) [∀ t, IsOpenImmersion (j t)]
variable (idx : J → I)
variable (hj : ∀ t, j t ≫ a = sp (algebraMap k (B t)))
variable (hW : ∀ t, (j t).opensRange ≤ U (idx t))
variable (hCover : ∀ x : A, ∃ (t : J) (z : Spec (CommRingCat.of (B t))), j t z = x)

variable [HasSheafify (_root_.Opens.grothendieckTopology (A : TopCat.{u})) AddCommGrpCat.{u}]

include hj hW hCover in
/-- The actual affine atlas supplies the additive short exact row of
the original normalized line. Its D-charts and their frames are
derived from the original atlas; no arbitrary exact-row input. -/
theorem shortExact_of_affine_atlas :
    (additive a U c hc M f hframe).ShortExact := by
  apply short_exact_of_open_splitting (row a U c hc M f hframe)
    (fun t => Spec (CommRingCat.of (B t))) j hCover
  intro t
  let jD := constantAffineMap a (j t) (hj t)
  letI : IsOpenImmersion jD := constant_chart_open a (j t) (hj t)
  have h := constant_chart_pullback a (j t) (hj t)
  exact SelectedSameAPrincipalUnitAffineTopRow318.affine_split a (j t) (hj t)
    U c hc M f hframe (idx t) (hW t) jD h

end GivenAtlas

section ActualAtlas

variable [HasSheafify (_root_.Opens.grothendieckTopology (A : TopCat.{u})) AddCommGrpCat.{u}]

private def chartScalar (W : A.Opens) : k →+* Γ(A,W) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ a.appLE ⊤ W (by simp)).hom

private theorem affine_structure {W : A.Opens} (h : IsAffineOpen W) :
    h.fromSpec ≫ a = sp (chartScalar a W) := by
  have ht := IsAffineOpen.SpecMap_appLE_fromSpec a
    (isAffineOpen_top (Spec (CommRingCat.of k))) h
    (show W ≤ a ⁻¹ᵁ ⊤ by simp)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at ht
  change h.fromSpec ≫ a =
    Spec.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ a.appLE ⊤ W (by simp))
  exact ht.symm

/-- Take the actual affine basis refining the prescribed frame cover;
there is no independent affine atlas or splitting hypothesis. -/
theorem actual_shortExact :
    (additive a U c hc M f hframe).ShortExact := by
  classical
  let J := {W : A.Opens // IsAffineOpen W ∧ ∃ i, W ≤ U i}
  let B (t : J) : Type u := Γ(A,t.1)
  letI : ∀ t : J, CommRing (B t) := fun t => inferInstanceAs (CommRing Γ(A,t.1))
  letI : ∀ t : J, Algebra k (B t) := fun t => (chartScalar a t.1).toAlgebra
  let j (t : J) : Spec (CommRingCat.of (B t)) ⟶ A := t.2.1.fromSpec
  letI : ∀ t : J, IsOpenImmersion (j t) := fun t =>
    inferInstanceAs (IsOpenImmersion t.2.1.fromSpec)
  let idx (t : J) : I := Classical.choose t.2.2
  have hj (t : J) : j t ≫ a = sp (algebraMap k (B t)) := affine_structure a t.2.1
  have hW (t : J) : (j t).opensRange ≤ U (idx t) := by
    change t.2.1.fromSpec.opensRange ≤ U (idx t)
    rw [IsAffineOpen.opensRange_fromSpec]
    exact Classical.choose_spec t.2.2
  have hCover (x : A) : ∃ (t : J) (z : Spec (CommRingCat.of (B t))), j t z = x := by
    have hx : x ∈ (⨆ i, U i) := hc (show x ∈ (⊤ : A.Opens) from trivial)
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    obtain ⟨_, ⟨W, hWa, rfl⟩, hxW, hWI⟩ := A.isBasis_affineOpens.exists_subset_of_mem_open
      hi (U i).2
    let t : J := ⟨W, hWa, ⟨i, hWI⟩⟩
    refine ⟨t, ?_⟩
    change x ∈ Set.range hWa.fromSpec
    rwa [IsAffineOpen.range_fromSpec]
  exact shortExact_of_affine_atlas a U c hc M f hframe B j idx hj hW hCover

theorem actual_signed_coefficient (i j : I) :
    SelectedSameASignedLiftCocycle318.coeff (A : TopCat.{u}) (additive a U c hc M f hframe)
      (actual_shortExact a U c hc M f hframe) U (one a U c hc M f hframe)
      (lift a U c hc M f hframe) (genuine_lift a U c hc M f hframe) i j =
        (show (additive a U c hc M f hframe).X₁.obj.obj (op (U i ⊓ U j)) from c.coeff i j) :=
  coefficient a U c hc M f hframe (actual_shortExact a U c hc M f hframe) i j

universe w
variable [HasExt.{w} (Sheaf (_root_.Opens.grothendieckTopology (A : TopCat.{u})) AddCommGrpCat.{u})]

/-- The forward normalized boundary of the literal one, using the
actual ShortExact produced from the same geometry. -/
@[expose] def actual_boundary_on_one : (additive a U c hc M f hframe).X₁.H 1 :=
  onOne a U c hc M f hframe (actual_shortExact a U c hc M f hframe)

end ActualAtlas

end SelectedSameAPrincipalUnitAffineCoverExact318
