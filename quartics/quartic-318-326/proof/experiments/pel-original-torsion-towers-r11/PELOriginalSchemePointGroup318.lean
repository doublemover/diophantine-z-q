module
public import PELOriginalUniversalSchemeGroupLaws318
public section
noncomputable section
namespace PELOriginalSchemePointGroup318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318
open PELOriginalReducedProjectiveCandidate318 PELOriginalProductChartCover318
open PELOriginalSchemeAdditionOperations318 PELOriginalSchemeGroupUnitInverse318
open PELOriginalUniversalSchemeGroupLaws318
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- The represented functor's genuine points over an arbitrary complex
scheme. In particular, infinitesimal and nonreduced tests are retained. -/
abbrev Points (Y : Scheme) (ρ : Y ⟶ Spec (CommRingCat.of ℂ)) :=
  { f : Y ⟶ candidate τ hτ // f≫π τ hτ=ρ }

variable {Y : Scheme} (ρ : Y ⟶ Spec (CommRingCat.of ℂ))
@[expose] def zero : Points τ hτ Y ρ :=
  ⟨ρ≫zeroPoint τ hτ, by rw [Category.assoc,zero_over,Category.comp_id]⟩
@[expose] def add (f g : Points τ hτ Y ρ) : Points τ hτ Y ρ :=
  ⟨combine τ hτ f.val g.val (f.property.trans g.property.symm),
    (combine_over τ hτ _ _ _).trans f.property⟩
@[expose] def neg (f : Points τ hτ Y ρ) : Points τ hτ Y ρ :=
  ⟨f.val≫inverse τ hτ, by rw [Category.assoc,inverse_over]; exact f.property⟩

lemma constant_zero (f : Points τ hτ Y ρ) :
    f.val≫constantZero τ hτ=(zero τ hτ ρ).val := by
  rw [constantZero,←Category.assoc,f.property]
  rfl

/-- The group operations on ALL scheme-valued points are represented by
the constructed regular addition, original zero section and genuine
projective negation. The axioms come from full scheme equations, not
from complex-point transport. -/
instance pointAddCommGroup : AddCommGroup (Points τ hτ Y ρ) where
  add := add τ hτ ρ
  zero := zero τ hτ ρ
  neg := neg τ hτ ρ
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc f g k := by
    apply Subtype.ext
    exact combine_assoc τ hτ f.val g.val k.val
      (f.property.trans g.property.symm) (g.property.trans k.property.symm)
  add_comm f g := by
    apply Subtype.ext
    exact combine_comm τ hτ f.val g.val (f.property.trans g.property.symm)
  zero_add f := by
    apply Subtype.ext
    change combine τ hτ (zero τ hτ ρ).val f.val _=f.val
    rw [←constant_zero τ hτ ρ f]
    exact combine_zero_left τ hτ f.val
  add_zero f := by
    apply Subtype.ext
    change combine τ hτ f.val (zero τ hτ ρ).val _=f.val
    rw [←constant_zero τ hτ ρ f]
    exact combine_zero_right τ hτ f.val
  neg_add_cancel f := by
    apply Subtype.ext
    exact (combine_inverse_left τ hτ f.val).trans (constant_zero τ hτ ρ f)

/-- Pullback of points along any actual over-C morphism is an additive
homomorphism. No reducedness or finiteness assumption on either test. -/
@[expose] def pull {Z : Scheme} {σ : Z ⟶ Spec (CommRingCat.of ℂ)}
    (k : Z ⟶ Y) (hk : k≫ρ=σ) : Points τ hτ Y ρ →+ Points τ hτ Z σ where
  toFun f := ⟨k≫f.val, by rw [Category.assoc,f.property,hk]⟩
  map_zero' := by
    apply Subtype.ext
    change k≫(ρ≫zeroPoint τ hτ)=σ≫zeroPoint τ hτ
    rw [←Category.assoc,hk]
  map_add' f g := by
    apply Subtype.ext
    exact combine_naturality τ hτ k f.val g.val _ _

lemma pull_identity : pull τ hτ ρ (𝟙 Y) (Category.id_comp ρ)=AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro f
  apply Subtype.ext
  exact Category.id_comp _

lemma pull_comp {Z W : Scheme} {σ : Z ⟶ Spec (CommRingCat.of ℂ)}
    {ω : W ⟶ Spec (CommRingCat.of ℂ)} (k : Z ⟶ Y) (hk : k≫ρ=σ)
    (l : W ⟶ Z) (hl : l≫σ=ω) :
    (pull τ hτ σ l hl).comp (pull τ hτ ρ k hk)=
      pull τ hτ ρ (l≫k) (by rw [Category.assoc,hk,hl]) := by
  apply AddMonoidHom.ext
  intro f
  apply Subtype.ext
  exact (Category.assoc l k f.val).symm
end PELOriginalSchemePointGroup318
