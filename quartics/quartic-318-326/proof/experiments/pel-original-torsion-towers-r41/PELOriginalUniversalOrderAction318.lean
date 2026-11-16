module
public import PELOriginalOrderSchemeLaws318
public import PELOriginalSchemePointGroup318
public section
noncomputable section
namespace PELOriginalUniversalOrderAction318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PELOriginalReducedProjectiveCandidate318 PELOriginalProductChartCover318
open PELOriginalSchemeAdditionOperations318 PELOriginalSchemeGroupUnitInverse318
open PELOriginalSchemePointGroup318 PELOriginalOrderSchemeMorphism318
open PELOriginalOrderSchemeLaws318 PELPrincipalOrderCoordinates318
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- The full scheme group square gives the order action on sums for
EVERY source scheme. No reducedness or finite type of the test is used. -/
theorem postcombine (a : order) {Y : Scheme} (f g : Y ⟶ candidate τ hτ)
    (h : f≫π τ hτ=g≫π τ hτ)
    (h' : (f≫morphism τ hτ a)≫π τ hτ=(g≫morphism τ hτ a)≫π τ hτ) :
    combine τ hτ f g h≫morphism τ hτ a=
      combine τ hτ (f≫morphism τ hτ a) (g≫morphism τ hτ a) h' := by
  let p := pullback.lift f g h
  have he : p≫combine τ hτ
      (pullback.fst (π τ hτ) (π τ hτ)≫morphism τ hτ a)
      (pullback.snd (π τ hτ) (π τ hτ)≫morphism τ hτ a)
      (by simp only [Category.assoc,over_complex]; exact pullback.condition)=
      combine τ hτ (f≫morphism τ hτ a) (g≫morphism τ hτ a) h' := by
    rw [combine_naturality τ hτ p _ _ _ (by
      simp only [Category.assoc,over_complex,←pullback.condition])]
    simp only [p,←Category.assoc,pullback.lift_fst,pullback.lift_snd]
  change (p≫PELOriginalAdditionSchemeMorphism318.addition τ hτ)≫morphism τ hτ a=_
  rw [Category.assoc,morphism_addition,he]

variable {Y : Scheme} (ρ : Y ⟶ Spec (CommRingCat.of ℂ))
/-- Actual additive endomorphism of ALL represented scheme points,
including nilpotent and infinitesimal test schemes. -/
@[expose] def endomorphism (a : order) : AddMonoid.End (Points τ hτ Y ρ) where
  toFun f := ⟨f.val≫morphism τ hτ a,by rw [Category.assoc,over_complex]; exact f.property⟩
  map_zero' := by
    apply Subtype.ext
    change (ρ≫zeroPoint τ hτ)≫morphism τ hτ a=ρ≫zeroPoint τ hτ
    rw [Category.assoc,morphism_zeroPoint]
  map_add' f g := by
    apply Subtype.ext
    exact postcombine τ hτ a f.val g.val _ _

/-- A genuine ring homomorphism from the SAME noncommutative original
order into additive endomorphisms of every represented test group. -/
@[expose] def ringAction : order →+* AddMonoid.End (Points τ hτ Y ρ) where
  toFun := endomorphism τ hτ ρ
  map_zero' := by
    apply AddMonoidHom.ext
    intro f
    apply Subtype.ext
    change f.val≫morphism τ hτ 0=ρ≫zeroPoint τ hτ
    rw [morphism_zero,constantZero,←Category.assoc,f.property]
  map_one' := by
    apply AddMonoidHom.ext
    intro f
    apply Subtype.ext
    change f.val≫morphism τ hτ 1=f.val
    rw [morphism_one,Category.comp_id]
  map_add' a b := by
    apply AddMonoidHom.ext
    intro f
    apply Subtype.ext
    change f.val≫morphism τ hτ (a+b)=combine τ hτ
      (f.val≫morphism τ hτ a) (f.val≫morphism τ hτ b) _
    rw [morphism_add]
    exact combine_naturality τ hτ f.val _ _ _ _
  map_mul' a b := by
    apply AddMonoidHom.ext
    intro f
    apply Subtype.ext
    change f.val≫morphism τ hτ (a*b)=(f.val≫morphism τ hτ b)≫morphism τ hτ a
    rw [Category.assoc,morphism_comp]

/-- Naturality is literal categorical precomposition. Thus the whole
represented group functor, not only its complex points, has this action. -/
theorem naturality {Z : Scheme} {σ : Z ⟶ Spec (CommRingCat.of ℂ)}
    (k : Z ⟶ Y) (hk : k≫ρ=σ) (a : order) :
    (pull τ hτ ρ k hk).comp (endomorphism τ hτ ρ a)=
      (endomorphism τ hτ σ a).comp (pull τ hτ ρ k hk) := by
  apply AddMonoidHom.ext
  intro f
  apply Subtype.ext
  exact (Category.assoc k f.val (morphism τ hτ a)).symm
end PELOriginalUniversalOrderAction318
