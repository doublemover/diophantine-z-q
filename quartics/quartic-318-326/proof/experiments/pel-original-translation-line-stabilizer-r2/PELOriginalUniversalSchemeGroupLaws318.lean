module
public import PELOriginalSchemeGroupAssociativity318
public section
noncomputable section
namespace PELOriginalUniversalSchemeGroupLaws318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits QuaternionicRealPeriod318
open PELOriginalReducedProjectiveCandidate318 PELOriginalProductChartCover318
open PELOriginalProductComplexPoints318 PELOriginalTripleProductReduced318
open PELOriginalSchemeAdditionOperations318 PELOriginalSchemeGroupUnitInverse318
open PELOriginalSchemeGroupAssociativity318
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- Commutativity after every base change of test scheme. No reducedness
or finite-type hypothesis on the arbitrary source Y is used. -/
theorem combine_comm {Y : Scheme} (f g : Y ⟶ candidate τ hτ)
    (h : f≫π τ hτ=g≫π τ hτ) :
    combine τ hτ f g h=combine τ hτ g f h.symm := by
  let p := pullback.lift f g h
  have hp : p≫PELOriginalAdditionSchemeMorphism318.addition τ hτ=combine τ hτ f g h := rfl
  have hs : p≫combine τ hτ (pullback.snd (π τ hτ) (π τ hτ))
      (pullback.fst (π τ hτ) (π τ hτ)) pullback.condition.symm=
      combine τ hτ g f h.symm := by
    rw [combine_naturality τ hτ p _ _ _ (by simp only [Category.assoc,←pullback.condition])]
    simp only [p,pullback.lift_snd,pullback.lift_fst]
  rw [←hs,commutative,hp]

/-- The zero and inverse laws hold on ALL scheme-valued points, not
only complex points or reduced sources. -/
theorem combine_zero_left {Y : Scheme} (f : Y ⟶ candidate τ hτ) :
    combine τ hτ (f≫constantZero τ hτ) f
      (by rw [Category.assoc,constantZero_over])=f := by
  have h := congrArg (fun k => f≫k) (left_unit τ hτ)
  rw [combine_naturality τ hτ f _ _ _ (by simp only [Category.assoc,constantZero_over,Category.id_comp]),
    Category.comp_id,Category.comp_id] at h
  exact h

theorem combine_zero_right {Y : Scheme} (f : Y ⟶ candidate τ hτ) :
    combine τ hτ f (f≫constantZero τ hτ)
      (by rw [Category.assoc,constantZero_over])=f := by
  rw [combine_comm]
  exact combine_zero_left τ hτ f

theorem combine_inverse_right {Y : Scheme} (f : Y ⟶ candidate τ hτ) :
    combine τ hτ f (f≫inverse τ hτ)
      (by rw [Category.assoc,inverse_over])=f≫constantZero τ hτ := by
  have h := congrArg (fun k => f≫k) (right_inverse τ hτ)
  rw [combine_naturality τ hτ f _ _ _ (by simp only [Category.assoc,inverse_over,Category.id_comp]),
    Category.comp_id] at h
  exact h

theorem combine_inverse_left {Y : Scheme} (f : Y ⟶ candidate τ hτ) :
    combine τ hτ (f≫inverse τ hτ) f
      (by rw [Category.assoc,inverse_over])=f≫constantZero τ hτ := by
  rw [combine_comm]
  exact combine_inverse_right τ hτ f

/-- Universal associativity is obtained by precomposing the proved full
triple-product scheme identity with the literal triple lift. This step
is valid on arbitrary nonreduced tests and retains infinitesimal data. -/
theorem combine_assoc {Y : Scheme} (f g k : Y ⟶ candidate τ hτ)
    (hfg : f≫π τ hτ=g≫π τ hτ) (hgk : g≫π τ hτ=k≫π τ hτ) :
    combine τ hτ (combine τ hτ f g hfg) k
      ((combine_over τ hτ f g hfg).trans (hfg.trans hgk))=
    combine τ hτ f (combine τ hτ g k hgk)
      (hfg.trans (combine_over τ hτ g k hgk).symm) := by
  let p : Y ⟶ Triple τ hτ := pullback.lift (pullback.lift f g hfg) k
    (by rw [baseMap,←Category.assoc,pullback.lift_fst]; exact hfg.trans hgk)
  have hfirst : p≫first τ hτ=f := by
    simp only [first,p,←Category.assoc,pullback.lift_fst]
  have hsecond : p≫second τ hτ=g := by
    simp only [second,p,←Category.assoc,pullback.lift_fst,pullback.lift_snd]
  have hthird : p≫third τ hτ=k := pullback.lift_snd _ _ _
  have h12 : p≫firstTwo τ hτ=combine τ hτ f g hfg := by
    rw [firstTwo,combine_naturality τ hτ p _ _ _
      (by rw [hfirst,hsecond]; exact hfg),hfirst,hsecond]
  have h23 : p≫lastTwo τ hτ=combine τ hτ g k hgk := by
    rw [lastTwo,combine_naturality τ hτ p _ _ _
      (by rw [hsecond,hthird]; exact hgk),hsecond,hthird]
  have he := congrArg (fun m => p≫m) (associative τ hτ)
  rw [leftAssociated,combine_naturality τ hτ p _ _ _
    (by rw [h12,hthird,combine_over]; exact hfg.trans hgk),h12,hthird,
    rightAssociated,combine_naturality τ hτ p _ _ _
    (by rw [hfirst,h23,combine_over]; exact hfg),hfirst,h23] at he
  exact he
end PELOriginalUniversalSchemeGroupLaws318
