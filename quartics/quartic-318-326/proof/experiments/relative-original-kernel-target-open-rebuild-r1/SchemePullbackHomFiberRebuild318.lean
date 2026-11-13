module
public import SchemeOpenRangePullbackRebuild318
public section
noncomputable section
namespace SchemePullbackHomFiberRebuild318
open CategoryTheory CategoryTheory.Limits
universe u v
variable {C : Type u} [Category.{v} C] {N S V Z : C}
  {j : N ⟶ S} {m : N ⟶ V} {n : S ⟶ Z} {i : V ⟶ Z}
/-- Compatible morphisms from an arbitrary test object, not a set of
geometric points. The two original projections are retained literally. -/
abbrev Compatible (n : S ⟶ Z) (i : V ⟶ Z) (T : C) :=
  {q : (T ⟶ S) × (T ⟶ V) // q.1 ≫ n=q.2 ≫ i}
variable (H : IsPullback j m n i)
def equivalence (T : C) : (T ⟶ N) ≃ Compatible n i T where
  toFun a := ⟨(a ≫ j,a ≫ m),by
    simpa only [Category.assoc] using congrArg (fun f => a ≫ f) H.w⟩
  invFun q := H.lift q.val.1 q.val.2 q.property
  left_inv a := H.hom_ext (H.lift_fst _ _ _) (H.lift_snd _ _ _)
  right_inv q := by
    apply Subtype.ext
    exact Prod.ext (H.lift_fst _ _ _) (H.lift_snd _ _ _)
@[simp] lemma first (T : C) (a : T ⟶ N) :
    (equivalence H T a).val.1=a ≫ j := rfl
@[simp] lemma second (T : C) (a : T ⟶ N) :
    (equivalence H T a).val.2=a ≫ m := rfl
@[reassoc] lemma inverse_first (T : C) (q : Compatible n i T) :
    (equivalence H T).symm q ≫ j=q.val.1 := H.lift_fst _ _ _
@[reassoc] lemma inverse_second (T : C) (q : Compatible n i T) :
    (equivalence H T).symm q ≫ m=q.val.2 := H.lift_snd _ _ _
def restrict {T T' : C} (f : T' ⟶ T) (q : Compatible n i T) : Compatible n i T' :=
  ⟨(f ≫ q.val.1,f ≫ q.val.2),by
    simpa only [Category.assoc] using congrArg (fun a => f ≫ a) q.property⟩
lemma natural {T T' : C} (f : T' ⟶ T) (a : T ⟶ N) :
    equivalence H T' (f ≫ a)=restrict f (equivalence H T a) := by
  apply Subtype.ext
  exact Prod.ext (Category.assoc _ _ _) (Category.assoc _ _ _)
lemma inverse_natural {T T' : C} (f : T' ⟶ T) (q : Compatible n i T) :
    (equivalence H T').symm (restrict f q)=f ≫ (equivalence H T).symm q := by
  apply H.hom_ext
  · rw [inverse_first,Category.assoc,inverse_first];rfl
  · rw [inverse_second,Category.assoc,inverse_second];rfl
end SchemePullbackHomFiberRebuild318
