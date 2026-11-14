module
public import ContactSchemeHilbertFunctorial318
public import Mathlib.AlgebraicGeometry.Limits
public section
noncomputable section
namespace SchemeSigmaFamilyCartesian318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {J : Type u} (X Y : J → Scheme.{u}) (f : ∀ j, X j ⟶ Y j)
@[expose] def map : (∐ X) ⟶ ∐ Y := Sigma.desc (fun j => f j ≫ Sigma.ι Y j)
@[reassoc] lemma into_map (j : J) : Sigma.ι X j ≫ map X Y f=f j ≫ Sigma.ι Y j := Sigma.ι_desc _ _
/-- Literal component squares for the actual disjoint-union family. -/
lemma cartesian (i : J) : IsPullback (Sigma.ι X i) (f i) (map X Y f) (Sigma.ι Y i) := by
  apply IsPullback.flip
  refine IsOpenImmersion.isPullback _ _ _ _ (by rw [into_map]) ?_
  apply le_antisymm
  · rintro x ⟨y,hxy⟩
    obtain ⟨⟨j,z⟩,rfl⟩ := (Scheme.sigmaMk X).surjective x
    rw [Scheme.sigmaMk_mk] at hxy ⊢
    have hm : map X Y f (Sigma.ι X j z)=Sigma.ι Y j (f j z) :=
      congrArg (fun k : X j ⟶ ∐ Y => k z) (into_map X Y f j)
    have he : Sigma.ι Y i y=Sigma.ι Y j (f j z) := hxy.trans hm
    have hij : i=j := congrArg Sigma.fst ((Scheme.sigmaι_eq_iff Y i j y (f j z)).mp he)
    subst j
    exact ⟨z,rfl⟩
  · rintro _ ⟨x,rfl⟩
    exact ⟨f i x,(congrArg (fun k : X i ⟶ ∐ Y => k x) (into_map X Y f i)).symm⟩
end SchemeSigmaFamilyCartesian318
