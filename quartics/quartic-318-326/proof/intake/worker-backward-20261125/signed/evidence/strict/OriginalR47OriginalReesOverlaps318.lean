module
public import OriginalR47IsolatedAffineCentres318
public import OriginalR47ReesCentreFreeProjection318
import all OriginalR47IsolatedAffineCentres318
public section
noncomputable section

namespace OriginalR47GlobalCentreRees318

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open OriginalR47IsolatedCentreCover318 OriginalAffineReesBlowup318
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

universe u
variable {X : Scheme.{u}} (Z : Set X) (hZ : Z.Finite)
variable (hC : ∀ x ∈ Z, IsClosed ({x} : Set X))
variable (pick : ∀ z : Z, Centre Z z)

local notation "J" => Idx Z hZ hC pick
local notation "openAt" => idxOpen Z hZ hC pick

/-- Both arrows are the genuine old opens. This is the exact map used
by the locally directed cover, before the colimit is constructed. -/
@[expose] def oldStep {i j : J} (h : i ⟶ j) : (openAt i).toScheme ⟶ (openAt j).toScheme :=
  X.homOfLE (show idxOpen Z hZ hC pick i ≤ idxOpen Z hZ hC pick j from leOfHom h)

@[reassoc (attr := simp)]
theorem oldStep_over {i j : J} (h : i ⟶ j) :
    oldStep Z hZ hC pick h ≫ (openAt j).ι = (openAt i).ι :=
  Scheme.homOfLE_ι X _

@[simp] theorem oldStep_id (i : J) :
    oldStep Z hZ hC pick (𝟙 i) = 𝟙 ((openAt i).toScheme) := by
  apply (cancel_mono ((openAt i).ι)).mp
  rw [oldStep_over, Category.id_comp]

@[simp] theorem oldStep_comp {i j k : J} (f : i ⟶ j) (g : j ⟶ k) :
    oldStep Z hZ hC pick (f ≫ g) =
      oldStep Z hZ hC pick f ≫ oldStep Z hZ hC pick g := by
  apply (cancel_mono ((openAt k).ι)).mp
  simp only [Category.assoc, oldStep_over]

variable {Z} in
abbrev A (z : Z) := Γ(X, (pick z).U)

variable {Z} in
abbrev affineArrow (z : Z) : Spec (A pick z) ⟶ X :=
  (pick z).affine.isoSpec.inv ≫ (pick z).U.ι

variable {Z} in
abbrev marked (z : Z) : Spec (A pick z) :=
  (pick z).affine.isoSpec.hom ⟨z.val,(pick z).here⟩

variable {Z} in
theorem marked_read (z : Z) : affineArrow pick z (marked pick z) = z.val := by
  change ((pick z).affine.isoSpec.hom ≫ (pick z).affine.isoSpec.inv ≫
    (pick z).U.ι) ⟨z.val, (pick z).here⟩ = z.val
  simp only [Iso.hom_inv_id_assoc, Scheme.Opens.ι_apply]

include hC in
theorem marked_max (z : Z) : (marked pick z).asIdeal.IsMaximal := by
  apply (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp
  have hs : (affineArrow pick z) ⁻¹' ({z.val} : Set X) = {marked pick z} := by
    ext x
    change affineArrow pick z x = z.val ↔ _
    rw [← marked_read pick z, Set.mem_singleton_iff]
    exact (affineArrow pick z).isOpenEmbedding.injective.eq_iff
  exact hs ▸ (hC z.val z.property).preimage (affineArrow pick z).continuous

@[expose] def piece : J → Scheme.{u}
  | .outside V _ => V.toScheme
  | .hit z => blowup (marked pick z).asIdeal

@[expose] def over : (i : J) → piece Z hZ hC pick i ⟶ (openAt i).toScheme
  | .outside V _ => 𝟙 V.toScheme
  | .hit z => projection (marked pick z).asIdeal ≫ (pick z).affine.isoSpec.inv

theorem step_exists {i j : J} (h : i ⟶ j) :
    ∃ f : piece Z hZ hC pick i ⟶ piece Z hZ hC pick j,
      IsPullback f (over Z hZ hC pick i) (over Z hZ hC pick j) (oldStep Z hZ hC pick h) := by
  cases i with
  | outside V hV =>
    cases j with
    | outside W hW =>
      let t : V.toScheme ⟶ W.toScheme := oldStep Z hZ hC pick h
      change ∃ f : V.toScheme ⟶ W.toScheme, IsPullback f (𝟙 V.toScheme) (𝟙 W.toScheme) t
      exact ⟨t, IsPullback.of_vert_isIso ⟨(Category.comp_id t).trans (Category.id_comp t).symm⟩⟩
    | hit z =>
      let iso := (pick z).affine.isoSpec
      let f := oldStep Z hZ hC pick h ≫ iso.hom
      let : (marked pick z).asIdeal.IsMaximal := marked_max Z hC pick z
      have avoid (v : V.toScheme) : f v ≠ marked pick z := by
        intro hv
        have ht : affineArrow pick z (f v) = V.ι v := by
          change (oldStep Z hZ hC pick h ≫ iso.hom ≫ iso.inv ≫ (pick z).U.ι) v = V.ι v
          rw [iso.hom_inv_id_assoc, oldStep_over]
        have hv' : V.ι v = z.val := ht.symm.trans ((congrArg (affineArrow pick z) hv).trans
          (marked_read pick z))
        have outside : V.ι v ∈ off Z hZ hC := hV (show V.ι v ∈ V from v.property)
        unfold off at outside
        exact outside (hv'.symm ▸ z.property)
      obtain ⟨k,hk⟩ := OriginalR47ReesCentreFreeProjection318.outside_point (marked pick z) f avoid
      refine ⟨k, hk.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) iso.symm ?_ ?_ ?_ ?_⟩
      · exact (Category.comp_id k).trans (Category.id_comp k).symm
      · simp only [over, Iso.refl_hom, Category.id_comp, Category.comp_id]
      · change projection (marked pick z).asIdeal ≫ iso.inv =
          projection (marked pick z).asIdeal ≫ (pick z).affine.isoSpec.inv
        rfl
      · simp only [f, Iso.symm_hom, Iso.refl_hom, Category.id_comp,
          Category.assoc, Iso.hom_inv_id, Category.comp_id]
  | hit z =>
    cases j with
    | outside V hV =>
      exact (not_hit_le_outside Z hZ hC pick z V hV (leOfHom h)).elim
    | hit w =>
      have he := hit_le_hit Z hZ hC pick z w (leOfHom h)
      subst w
      have hh : h = 𝟙 _ := Subsingleton.elim _ _
      subst h
      exact ⟨𝟙 _, by rw [oldStep_id]; exact IsPullback.of_id_fst⟩

/-- The overlap arrow is uniquely fixed on an outside open. On a hit
open the only possible next hit is the same selected old affine. -/
@[expose] def step {i j : J} (h : i ⟶ j) :
    piece Z hZ hC pick i ⟶ piece Z hZ hC pick j := by
  cases i with
  | outside V hV => exact (step_exists Z hZ hC pick h).choose
  | hit z =>
    cases j with
    | outside V hV =>
      exact (not_hit_le_outside Z hZ hC pick z V hV (leOfHom h)).elim
    | hit w =>
      have he := hit_le_hit Z hZ hC pick z w (leOfHom h)
      subst w
      exact 𝟙 _

theorem step_cartesian {i j : J} (h : i ⟶ j) :
    IsPullback (step Z hZ hC pick h) (over Z hZ hC pick i)
      (over Z hZ hC pick j) (oldStep Z hZ hC pick h) := by
  cases i with
  | outside V hV =>
    exact (step_exists Z hZ hC pick h).choose_spec
  | hit z =>
    cases j with
    | outside V hV =>
      exact (not_hit_le_outside Z hZ hC pick z V hV (leOfHom h)).elim
    | hit w =>
      have he := hit_le_hit Z hZ hC pick z w (leOfHom h)
      subst w
      have hh : h = 𝟙 _ := Subsingleton.elim _ _
      subst h
      rw [oldStep_id]
      exact IsPullback.of_id_fst

private theorem outside_unique (V : X.Opens) (hV : V ≤ off Z hZ hC)
    {j : J} (h : Idx.outside V hV ⟶ j) (g : V.toScheme ⟶ piece Z hZ hC pick j)
    (hg : g ≫ over Z hZ hC pick j = oldStep Z hZ hC pick h) : g = step Z hZ hC pick h := by
  have H := step_cartesian Z hZ hC pick h
  change IsPullback (step Z hZ hC pick h) (𝟙 V.toScheme)
    (over Z hZ hC pick j) (oldStep Z hZ hC pick h) at H
  let t : V.toScheme ⟶ V.toScheme := H.lift g (𝟙 _) (by rw [hg,Category.id_comp])
  let f : V.toScheme ⟶ piece Z hZ hC pick j := step Z hZ hC pick h
  have h₁ : t ≫ f = g := H.lift_fst _ _ _
  have e : t ≫ (𝟙 V.toScheme) = 𝟙 V.toScheme := H.lift_snd _ _ _
  have h₂ : t = 𝟙 V.toScheme := (Category.comp_id t).symm.trans e
  have h₃ : (𝟙 V.toScheme) ≫ f = g := h₂ ▸ h₁
  exact ((Category.id_comp f).symm.trans h₃).symm

theorem step_id (i : J) : step Z hZ hC pick (𝟙 i) = 𝟙 _ := by
  cases i with
  | outside V hV =>
    symm
    apply outside_unique Z hZ hC pick V hV
    change (𝟙 V.toScheme) ≫ (𝟙 V.toScheme) = oldStep Z hZ hC pick (𝟙 (Idx.outside V hV))
    exact (Category.id_comp (𝟙 V.toScheme)).trans
      (oldStep_id Z hZ hC pick (Idx.outside V hV : J)).symm
  | hit z => rfl

theorem step_comp {i j k : J} (f : i ⟶ j) (g : j ⟶ k) :
    step Z hZ hC pick (f ≫ g) = step Z hZ hC pick f ≫ step Z hZ hC pick g := by
  cases i with
  | outside V hV =>
    symm
    apply outside_unique Z hZ hC pick V hV
    rw [Category.assoc,(step_cartesian Z hZ hC pick g).w,
      ← Category.assoc,(step_cartesian Z hZ hC pick f).w]
    let f₀ : V.toScheme ⟶ (openAt j).toScheme := oldStep Z hZ hC pick f
    let g₀ := oldStep Z hZ hC pick g
    change ((𝟙 V.toScheme) ≫ f₀) ≫ g₀ = oldStep Z hZ hC pick (f ≫ g)
    exact (congrArg (fun t => t ≫ g₀) (Category.id_comp f₀)).trans
      (oldStep_comp Z hZ hC pick f g).symm
  | hit z =>
    cases j with
    | outside V hV =>
      exact (not_hit_le_outside Z hZ hC pick z V hV (leOfHom f)).elim
    | hit w =>
      have he := hit_le_hit Z hZ hC pick z w (leOfHom f)
      subst w
      cases k with
      | outside V hV =>
        exact (not_hit_le_outside Z hZ hC pick z V hV (leOfHom g)).elim
      | hit t =>
        have he := hit_le_hit Z hZ hC pick z t (leOfHom g)
        subst t
        simp only [show f = 𝟙 _ from Subsingleton.elim _ _,
          show g = 𝟙 _ from Subsingleton.elim _ _, Category.id_comp, step_id]

/-- A functor of the actual Rees pieces and exact overlap maps. The
global gluing module will use this literally, without reselecting a
point, affine chart, outside open, or map. -/
@[expose] def pieceFunctor : J ⥤ Scheme.{u} where
  obj := piece Z hZ hC pick
  map := fun {i j} h => step Z hZ hC pick (i:=i) (j:=j) h
  map_id := step_id Z hZ hC pick
  map_comp := step_comp Z hZ hC pick

end OriginalR47GlobalCentreRees318

#print axioms OriginalR47GlobalCentreRees318.oldStep_over
#print axioms OriginalR47GlobalCentreRees318.marked_max
#print axioms OriginalR47GlobalCentreRees318.step_cartesian
#print axioms OriginalR47GlobalCentreRees318.step_comp
#print axioms OriginalR47GlobalCentreRees318.pieceFunctor
