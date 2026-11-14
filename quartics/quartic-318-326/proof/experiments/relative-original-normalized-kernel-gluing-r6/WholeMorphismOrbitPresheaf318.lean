module
public import ContactOriginalAutomorphismCommutativity318
public section
noncomputable section
namespace WholeMorphismOrbitPresheaf318
open CategoryTheory Opposite
universe u v w
variable {C : Type u} [Category.{v} C] {Y F : Cᵒᵖ ⥤ Type w} (φ : Y ⟶ F)
/-- The literal pointwise relation, before any local saturation. -/
def relation (T : Cᵒᵖ) : Setoid (Y.obj T) where
  r z t := φ.app T z=φ.app T t
  iseqv := ⟨fun _ => rfl,fun h => h.symm,fun h k => h.trans k⟩
def Object (T : Cᵒᵖ) := Quotient (relation φ T)
lemma restriction_relation {T U : Cᵒᵖ} (f : T ⟶ U) {z t : Y.obj T}
    (h : φ.app T z=φ.app T t) : φ.app U (Y.map f z)=φ.app U (Y.map f t) := by
  have hz := ConcreteCategory.congr_hom (φ.naturality f) z
  have ht := ConcreteCategory.congr_hom (φ.naturality f) t
  exact hz.trans ((congrArg (F.map f) h).trans ht.symm)
def presheaf : Cᵒᵖ ⥤ Type w where
  obj := Object φ
  map f := Quotient.map (Y.map f) (fun _ _ h => restriction_relation φ f h)
  map_id T := by
    funext q
    induction q using Quotient.inductionOn with
    | h z => exact congrArg (Quotient.mk (relation φ T))
        (ConcreteCategory.congr_hom (Y.map_id T) z)
  map_comp f g := by
    funext q
    induction q using Quotient.inductionOn with
    | h z => exact congrArg (Quotient.mk (relation φ _))
        (ConcreteCategory.congr_hom (Y.map_comp f g) z)
def quotient : Y ⟶ presheaf φ where
  app T := Quotient.mk (relation φ T)
  naturality _ _ _ := rfl
def inclusion : presheaf φ ⟶ F where
  app T := Quotient.lift (φ.app T) (fun _ _ h => h)
  naturality T U f := by
    funext q
    induction q using Quotient.inductionOn with
    | h z => exact ConcreteCategory.congr_hom (φ.naturality f) z
lemma factor : quotient φ ≫ inclusion φ=φ := rfl
lemma quotient_surjective (T : Cᵒᵖ) : Function.Surjective ((quotient φ).app T) :=
  fun q => Quotient.exists_rep q
lemma quotient_eq_iff (T : Cᵒᵖ) (z t : Y.obj T) :
    (quotient φ).app T z=(quotient φ).app T t ↔ φ.app T z=φ.app T t :=
  ⟨Quotient.exact,Quotient.sound⟩
lemma inclusion_injective (T : Cᵒᵖ) : Function.Injective ((inclusion φ).app T) := by
  intro z t
  induction z using Quotient.inductionOn with
  | h z =>
    induction t using Quotient.inductionOn with
    | h t => exact Quotient.sound
end WholeMorphismOrbitPresheaf318
