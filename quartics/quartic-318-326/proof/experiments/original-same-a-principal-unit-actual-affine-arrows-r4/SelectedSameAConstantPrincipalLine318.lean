module

public import SelectedSameAActualNilpotentLineGluing318
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
Apply actual nilpotent line gluing to the literal constantScheme thickening
of the fibre and the actual pullbacks of its Zariski coefficients.
The special-fibre transition test uses the same zero generator.
-/

public section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace SelectedSameAConstantPrincipalLine318

universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open SelectedSameAActualNilpotentLineGluing318

section Opens

variable {A Y : Scheme.{u}} (f : Y ⟶ A) {ι : Type u} (U : ι → A.Opens)

abbrev pre (i : ι) : Y.Opens := f ⁻¹ᵁ U i

theorem pairLE (i j : ι) :
    pre f U i ⊓ pre f U j ≤ f ⁻¹ᵁ (U i ⊓ U j) := by
  rw [Scheme.Hom.preimage_inf]

/-- Coefficients on the literal entire inverse-image overlap. -/
@[expose] def pullCoefficient {V : A.Opens} {W : Y.Opens} (e : W ≤ f ⁻¹ᵁ V)
    (b : Γ(A,V)) : Γ(Y,W) :=
  f.appLE V W e b

theorem pullCoefficient_restrict {V V' : A.Opens} {W W' : Y.Opens}
    (e : W ≤ f ⁻¹ᵁ V) (e' : W' ≤ f ⁻¹ᵁ V')
    (hV : V' ≤ V) (hW : W' ≤ W) (b : Γ(A,V)) :
    restrict hW (pullCoefficient f e b) = pullCoefficient f e' (restrict hV b) := by
  have h : f.appLE V W e ≫ Y.presheaf.map (homOfLE hW).op =
      A.presheaf.map (homOfLE hV).op ≫ f.appLE V' W' e' := by
    rw [f.appLE_map, f.map_appLE]
  exact congrArg (fun m : Γ(A,V) ⟶ Γ(Y,W') => m b) h

/-- Additive Čech equations are transported along the actual projection:
the equality on triples is derived, not part of the target data. -/
@[expose] def pullCocycle (c : AdditiveCocycle U) : AdditiveCocycle (pre f U) where
  coeff i j := pullCoefficient f (pairLE f U i j) (c.coeff i j)
  diagonal i := by
    rw [c.diagonal]
    exact map_zero (f.appLE _ _ (pairLE f U i i)).hom
  triple i j k := by
    let V := (U i ⊓ U j) ⊓ U k
    let W := (pre f U i ⊓ pre f U j) ⊓ pre f U k
    have e : W ≤ f ⁻¹ᵁ V := by
      dsimp only [V,W,pre]
      rw [Scheme.Hom.preimage_inf, Scheme.Hom.preimage_inf]
    change restrict inf_le_left (pullCoefficient f (pairLE f U i j) (c.coeff i j)) +
      restrict (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
        (pullCoefficient f (pairLE f U j k) (c.coeff j k)) =
      restrict (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
        (pullCoefficient f (pairLE f U i k) (c.coeff i k))
    rw [pullCoefficient_restrict f (pairLE f U i j) e inf_le_left inf_le_left,
      pullCoefficient_restrict f (pairLE f U j k) e
        (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
        (le_inf (inf_le_left.trans inf_le_right) inf_le_right),
      pullCoefficient_restrict f (pairLE f U i k) e
        (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
        (le_inf (inf_le_left.trans inf_le_left) inf_le_right)]
    unfold pullCoefficient
    rw [← map_add (f.appLE V W e).hom, c.triple]

theorem preCover (hc : (⊤ : A.Opens) ≤ ⨆ i, U i) :
    (⊤ : Y.Opens) ≤ ⨆ i, pre f U i :=
  (f.iSup_preimage_eq_top (U := U) (le_antisymm le_top hc)).ge

end Opens

section Literal

variable {k : Type u} [CommRing k]
variable {A : Scheme.{u}} (a : A ⟶ Spec (CommRingCat.of k))

abbrev D (k : Type u) := TrivSqZeroExt k k
abbrev base (k : Type u) [CommRing k] :
    Spec (CommRingCat.of (D k)) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (D k)))

abbrev constantScheme := pullback a (base k)
abbrev originRed (k : Type u) [CommRing k] :
    Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (D k)) :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)

abbrev reducedConstant : A ⟶ constantScheme a :=
  pullback.lift (𝟙 A) (a ≫ originRed k) (by
    have h : originRed k ≫ base k = 𝟙 _ := by
      rw [← Spec.map_comp, ← Spec.map_id]
      congr 1
    simp only [Category.id_comp, Category.assoc, h, Category.comp_id])

@[expose] def markedEpsilon : Γ(constantScheme a,⊤) :=
  (pullback.snd a (base k)).appTop
    ((Scheme.ΓSpecIso (CommRingCat.of (D k))).inv (TrivSqZeroExt.inr (1 : k)))

theorem markedEpsilon_sq : markedEpsilon a * markedEpsilon a = 0 := by
  unfold markedEpsilon
  rw [← map_mul, ← map_mul, TrivSqZeroExt.inr_mul_inr, map_zero, map_zero]

theorem markedEpsilon_killed :
    (reducedConstant a).appTop (markedEpsilon a) = 0 := by
  let E := Scheme.ΓSpecIso (CommRingCat.of (D k))
  let E' := Scheme.ΓSpecIso (CommRingCat.of k)
  let r := CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom
  let p := pullback.snd a (base k)
  have h₁ : p.appTop ≫ (reducedConstant a).appTop = (originRed k).appTop ≫ a.appTop := by
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop]
    have hleg : reducedConstant a ≫ p = a ≫ originRed k :=
      pullback.lift_snd _ _ _
    exact congrArg (fun q : A ⟶ Spec (CommRingCat.of (D k)) => q.appTop) hleg
  have h₂ : E.inv ≫ (originRed k).appTop = r ≫ E'.inv :=
    (Scheme.ΓSpecIso_inv_naturality r).symm
  have h₃ : E.inv ≫ (p.appTop ≫ (reducedConstant a).appTop) =
      r ≫ (E'.inv ≫ a.appTop) := by
    rw [h₁, ← Category.assoc, h₂, Category.assoc]
  have hx := congrArg (fun m => m (TrivSqZeroExt.inr (1 : k) : D k)) h₃
  change (reducedConstant a).appTop (markedEpsilon a) = _ at hx
  refine hx.trans ?_
  change a.appTop (E'.inv ((TrivSqZeroExt.inr (1 : k) : D k).fst)) = 0
  simp only [TrivSqZeroExt.fst_inr, map_zero]

variable {ι : Type u} (U : ι → A.Opens) (c : AdditiveCocycle U)

abbrev constantCocycle := pullCocycle (pullback.fst a (base k)) U c

/-- The actual invertible module sheaf on the actual constantScheme A_D.
No chosen affine coordinates or fold from an unrelated model are used. -/
@[expose] def principalLine (hc : (⊤ : A.Opens) ≤ ⨆ i, U i) :
    LineSheafClass318.Line (constantScheme a) :=
  line (pre (pullback.fst a (base k)) U) (markedEpsilon a) (markedEpsilon_sq a)
    (constantCocycle a U c) (preCover (pullback.fst a (base k)) U hc)

end Literal

end SelectedSameAConstantPrincipalLine318
