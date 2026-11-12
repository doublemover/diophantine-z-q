module
public import WholeMorphismOrbitImage318
public section
noncomputable section
namespace WholeMorphismOrbitDescent318
open CategoryTheory
open WholeMorphismOrbitPresheaf318
universe u v w
variable {C : Type u} [Category.{v} C] {Y F H : Cᵒᵖ ⥤ Type w} (φ : Y ⟶ F)
  (a : Y ⟶ H) (ha : ∀ T (z t : Y.obj T),φ.app T z=φ.app T t → a.app T z=a.app T t)
def lift : presheaf φ ⟶ H where
  app T := Quotient.lift (a.app T) (ha T)
  naturality T U f := by
    funext q
    induction q using Quotient.inductionOn with
    | h z => exact ConcreteCategory.congr_hom (a.naturality f) z
lemma factor : quotient φ ≫ lift φ a ha=a := rfl
lemma unique (g : presheaf φ ⟶ H) (hg : quotient φ ≫ g=a) : g=lift φ a ha := by
  ext T q
  induction q using Quotient.inductionOn with
  | h z => exact ConcreteCategory.congr_hom (congrArg (fun k => k.app T) hg) z
/-- No target sheaf, effectivity or represented quotient is needed for
this exact pointwise universal property. -/
lemma iff_unique : (∀ T (z t : Y.obj T),φ.app T z=φ.app T t → a.app T z=a.app T t) ↔
    ∃! g : presheaf φ ⟶ H,quotient φ ≫ g=a := by
  constructor
  · intro h
    exact ⟨lift φ a h,factor φ a h,fun g hg => unique φ a h g hg⟩
  · rintro ⟨g,hg,_⟩ T z t h
    have hq := (quotient_eq_iff φ T z t).mpr h
    have hz := ConcreteCategory.congr_hom (congrArg (fun k => k.app T) hg) z
    have ht := ConcreteCategory.congr_hom (congrArg (fun k => k.app T) hg) t
    exact hz.symm.trans ((congrArg (g.app T) hq).trans ht)
end WholeMorphismOrbitDescent318
