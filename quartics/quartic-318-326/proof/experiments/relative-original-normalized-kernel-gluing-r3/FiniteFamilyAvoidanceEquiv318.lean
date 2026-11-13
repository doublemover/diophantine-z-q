module
public import FiniteFamilyAvoidanceFactor318
public section
noncomputable section
namespace FiniteFamilyAvoidanceEquiv318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FiniteFamilyAvoidanceOpen318 FiniteFamilyAvoidanceFactor318
universe u
variable {Z B X : Scheme.{u}} (p : Z ⟶ B) [UniversallyClosed p]
  (q : Z ⟶ X) (U : X.Opens) (T : Scheme.{u})
/-- The avoidance subfunctor on ALL scheme tests is represented by the
actual open complement of the finite closed image. -/
@[expose] def equivalence : (T ⟶ (locus p q U).toScheme) ≃ {f : T ⟶ B // Supported p q U f} where
  toFun g := ⟨g ≫ (locus p q U).ι,supported_comp p q U g⟩
  invFun f := factor p q U f.val f.property
  left_inv g := by
    apply (cancel_mono (locus p q U).ι).mp
    exact factor_into p q U _ _
  right_inv f := Subtype.ext (factor_into p q U _ _)
/-- Uniqueness is genuine morphism equality through the open immersion. -/
lemma factor_unique (f : T ⟶ B) (h : Supported p q U f)
    (g : T ⟶ (locus p q U).toScheme) (hg : g ≫ (locus p q U).ι=f) :
    g=factor p q U f h := by
  apply (cancel_mono (locus p q U).ι).mp
  exact hg.trans (factor_into p q U f h).symm
end FiniteFamilyAvoidanceEquiv318
