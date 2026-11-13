module
public import FiniteFamilyAvoidanceEquiv318
public section
noncomputable section
namespace ProperEmptyFamilyOpen318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {Z B : Scheme.{u}} (p : Z ⟶ B) [UniversallyClosed p]

/-- The actual open where the entire proper family is empty, not merely where
chosen rational points are absent. -/
abbrev locus : B.Opens := FiniteFamilyAvoidanceOpen318.locus p (𝟙 Z) ⊥

lemma supported_iff (T : Scheme.{u}) (f : T ⟶ B) :
    FiniteFamilyAvoidanceFactor318.Supported p (𝟙 Z) ⊥ f ↔ IsEmpty ↑(pullback p f) := by
  constructor
  · intro h
    exact ⟨fun z => h z⟩
  · intro h z
    exact h.false z

/-- Genuine all-scheme representability of the empty-family condition by an open. -/
@[expose] def points (T : Scheme.{u}) : (T ⟶ (locus p).toScheme) ≃
    {f : T ⟶ B // IsEmpty ↑(pullback p f)} where
  toFun g := ⟨g ≫ (locus p).ι,(supported_iff p T _).mp
    (FiniteFamilyAvoidanceFactor318.supported_comp p (𝟙 Z) ⊥ g)⟩
  invFun f := FiniteFamilyAvoidanceFactor318.factor p (𝟙 Z) ⊥ f.val
    ((supported_iff p T f.val).mpr f.property)
  left_inv g := by
    apply (cancel_mono (locus p).ι).mp
    exact FiniteFamilyAvoidanceFactor318.factor_into p (𝟙 Z) ⊥ _ _
  right_inv f := Subtype.ext (FiniteFamilyAvoidanceFactor318.factor_into p (𝟙 Z) ⊥ _ _)

lemma factor_iff {T : Scheme.{u}} (f : T ⟶ B) :
    (∃ g : T ⟶ (locus p).toScheme,g ≫ (locus p).ι=f) ↔ IsEmpty ↑(pullback p f) := by
  constructor
  · rintro ⟨g,rfl⟩
    exact (points p T g).property
  · intro h
    exact ⟨(points p T).symm ⟨f,h⟩,
      congrArg Subtype.val ((points p T).apply_symm_apply ⟨f,h⟩)⟩

lemma natural {T U : Scheme.{u}} (g : T ⟶ (locus p).toScheme) (h : U ⟶ T) :
    (points p U (h ≫ g)).val=h ≫ (points p T g).val := Category.assoc _ _ _
end ProperEmptyFamilyOpen318
