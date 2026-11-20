module
public import SelectedJOneValuativeSections318
import all SelectedJOneExactMinorLoss318
public section
noncomputable section
open AlgebraicGeometry CategoryTheory NumberField
open SelectedJOneValuativeSections318 SelectedJOneExactMinorLoss318

namespace SelectedJOneSectionBaseChange318
universe u
variable {L L' : Type u} [Field L] [Field L'] [NumberField L] [NumberField L']
variable [Algebra L L'] (v : FinitePlace L) (w : FinitePlace L')
variable [over : w.maximalIdeal.asIdeal.LiesOver v.maximalIdeal.asIdeal]

/-- The norm changes by the literal local e·f power across the same
number-field inclusion. It is not an equality of the unscaled norms. -/
include over in
theorem norm_map (x : L) :
    w (algebraMap L L' x) =
      (v x)^(w.maximalIdeal.asIdeal.ramificationIdx (𝓞 L) *
        w.maximalIdeal.asIdeal.inertiaDeg (𝓞 L)) := by
  have hv : (FinitePlace.equivHeightOneSpectrum (K:=L)).symm v.maximalIdeal = v := by
    rw [← FinitePlace.equivHeightOneSpectrum_apply,Equiv.symm_apply_apply]
  have hw : (FinitePlace.equivHeightOneSpectrum (K:=L')).symm w.maximalIdeal = w := by
    rw [← FinitePlace.equivHeightOneSpectrum_apply,Equiv.symm_apply_apply]
  simpa only [hv,hw] using
    (FinitePlace.equivHeightOneSpectrum_symm_apply_algebraMap v.maximalIdeal w.maximalIdeal x)

/-- Exactly the e·f weight, derived before any [L:Q] summation. -/
include over in
theorem logNorm_map (x : L) :
    -Real.log (w (algebraMap L L' x)) =
      (↑(w.maximalIdeal.asIdeal.ramificationIdx (𝓞 L) *
        w.maximalIdeal.asIdeal.inertiaDeg (𝓞 L)):ℝ)*(-Real.log (v x)) := by
  rw [norm_map v w,Real.log_pow]
  ring

local notation "O" => ↥(trait v)
local notation "O'" => ↥(trait w)
local notation "S" => Spec (CommRingCat.of O)
local notation "S'" => Spec (CommRingCat.of O')
local notation "G" => Spec (CommRingCat.of L)
local notation "G'" => Spec (CommRingCat.of L')

/-- Actual map of embedded localizations, induced by the given
number-field embedding at genuine lying-over places. -/
include over in
@[expose] def localMap : O →+* O' where
  toFun x := ⟨algebraMap L L' (x:L),by
    change algebraMap L L' (x:L) ∈ (trait w).toSubring
    rw [trait_subring]
    change w (algebraMap L L' (x:L)) ≤ 1
    rw [norm_map v w]
    have hx : (x:L) ∈ (trait v).toSubring := x.property
    rw [trait_subring] at hx
    exact pow_le_one₀ (apply_nonneg v _) hx⟩
  map_zero' := by apply Subtype.ext; exact map_zero _
  map_one' := by apply Subtype.ext; exact map_one _
  map_add' x y := by apply Subtype.ext; exact map_add _ _ _
  map_mul' x y := by apply Subtype.ext; exact map_mul _ _ _

@[expose] def onGeneric : G' ⟶ G :=
  Spec.map (CommRingCat.ofHom (algebraMap L L'))

include over in
@[expose] def onTrait : S' ⟶ S :=
  Spec.map (CommRingCat.ofHom (localMap v w))

theorem generic_naturality :
    genericInclusion w ≫ onTrait v w = onGeneric ≫ genericInclusion v := by
  simp only [genericInclusion,onTrait,onGeneric,← Spec.map_comp] <;>
    congr 1 <;> apply CommRingCat.hom_ext <;> apply RingHom.ext <;> intro x <;> rfl

/-- Comparison with the SAME chosen generic point. A morphism of the
actual models over the actual localization map is necessary; this
does not identify an arbitrary ramified base-change as regular. -/
theorem selected_section_comp {Z Z' : Scheme.{u}}
    (f : Z ⟶ S) [IsSeparated f] (f' : Z' ⟶ S')
    (compare : Z' ⟶ Z) (base : compare ≫ f = f' ≫ onTrait v w)
    (P : G ⟶ Z) (P' : G' ⟶ Z')
    (generic : P' ≫ compare = onGeneric ≫ P)
    (s : S ⟶ Z) (s' : S' ⟶ Z')
    (hs : genericInclusion v ≫ s = P) (hs' : genericInclusion w ≫ s' = P')
    (hfs : s ≫ f = 𝟙 S) (hfs' : s' ≫ f' = 𝟙 S') :
    s' ≫ compare = onTrait v w ≫ s := by
  have hp : (onGeneric ≫ P) ≫ f = genericInclusion w ≫ onTrait v w := by
    rw [Category.assoc,← hs,Category.assoc,hfs,Category.comp_id,generic_naturality]
  let Q : ValuativeCommSq f :=
    { R := O', K := L', i₁ := onGeneric ≫ P, i₂ := onTrait v w, commSq := ⟨hp⟩ }
  letI : Subsingleton Q.commSq.LiftStruct := IsSeparated.valuativeCriterion f Q
  let a : Q.commSq.LiftStruct :=
    ⟨s' ≫ compare,by change genericInclusion w ≫ (s' ≫ compare) = onGeneric ≫ P
                      rw [← Category.assoc,hs',generic],
      by change (s' ≫ compare) ≫ f = onTrait v w
         rw [Category.assoc,base,← Category.assoc,hfs',Category.id_comp]⟩
  let b : Q.commSq.LiftStruct :=
    ⟨onTrait v w ≫ s,by change genericInclusion w ≫ (onTrait v w ≫ s) = onGeneric ≫ P
                         rw [← Category.assoc,generic_naturality,Category.assoc,hs],
      by change (onTrait v w ≫ s) ≫ f = onTrait v w
         rw [Category.assoc,hfs,Category.comp_id]⟩
  exact congrArg CommSq.LiftStruct.l (Subsingleton.elim a b)

/-- Ordered naturality follows pointwise; no replacement of the index
set of the determinant minor and no new choice of a point. -/
theorem selected_order_comp {I : Type*} {Z Z' : Scheme.{u}}
    (f : Z ⟶ S) [IsSeparated f] (f' : Z' ⟶ S')
    (compare : Z' ⟶ Z) (base : compare ≫ f = f' ≫ onTrait v w)
    (P : I → G ⟶ Z) (P' : I → G' ⟶ Z')
    (generic : ∀ i, P' i ≫ compare = onGeneric ≫ P i)
    (s : I → S ⟶ Z) (s' : I → S' ⟶ Z')
    (hs : ∀ i, genericInclusion v ≫ s i = P i)
    (hs' : ∀ i, genericInclusion w ≫ s' i = P' i)
    (hfs : ∀ i, s i ≫ f = 𝟙 S) (hfs' : ∀ i, s' i ≫ f' = 𝟙 S') :
    ∀ i, s' i ≫ compare = onTrait v w ≫ s i := fun i =>
  selected_section_comp v w f f' compare base (P i) (P' i) (generic i) (s i) (s' i)
    (hs i) (hs' i) (hfs i) (hfs' i)

end SelectedJOneSectionBaseChange318

#print axioms SelectedJOneSectionBaseChange318.norm_map
#print axioms SelectedJOneSectionBaseChange318.generic_naturality
#print axioms SelectedJOneSectionBaseChange318.selected_order_comp
