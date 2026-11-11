module
public import RankOneAffineProjectiveMorphism318
public section
noncomputable section
namespace RankOneAffinePointAction318
open AlgebraicGeometry CategoryTheory
open RankOneAffineColumnCover318 RankOneAffineProjectiveMorphism318
variable {ι κ A : Type*} [Finite ι] [CommRing A] [Algebra ℂ A]
  [Algebra.FiniteType ℂ A] [_root_.IsReduced A]
variable (w : ι → κ → A)

@[expose] def liftedPoint (rs : ι × κ) (f : A →ₐ[ℂ] ℂ) (hf : f (w rs.1 rs.2)≠0) :
    EntryRing w rs →ₐ[ℂ] ℂ :=
  { IsLocalization.Away.lift (w rs.1 rs.2) (g := f.toRingHom) (isUnit_iff_ne_zero.mpr hf) with
    commutes' := by
      intro c
      rw [IsScalarTower.algebraMap_apply ℂ A (EntryRing w rs),IsLocalization.Away.lift_eq]
      exact f.commutes c }

lemma lifted_base (rs : ι × κ) (f : A →ₐ[ℂ] ℂ) (hf : f (w rs.1 rs.2)≠0) :
    baseEvaluation w rs (liftedPoint w rs f hf)=f := by
  ext a
  exact IsLocalization.Away.lift_eq (isUnit_iff_ne_zero.mpr hf) a

/-- Every whole affine complex point has its exact column class under
the genuine globally glued morphism, for ANY entry nonzero at that
point. The actual localization lift and all base maps are retained. -/
theorem point_action
    (hspan : Ideal.span (Set.range (fun rs : ι × κ => w rs.1 rs.2))=⊤)
    (hw : ∀ i j s t, w i s*w j t=w i t*w j s)
    (f : A →ₐ[ℂ] ℂ) (rs : ι × κ) (hf : f (w rs.1 rs.2)≠0) :
    Spec.map (CommRingCat.ofHom f.toRingHom)≫morphism w hspan hw=
      ComplexProjectiveSchemePoint318.point (fun i => f (w i rs.2)) ⟨rs.1,hf⟩ := by
  have hb := base_point w rs (liftedPoint w rs f hf)
  rw [lifted_base] at hb
  rw [←hb,Category.assoc,entry_morphism,local_point_action,lifted_base]

/-- A specified Segre-value formula identifies the first factor as an
actual Spec(C) morphism. No choice of a nonzero output coordinate is
left as an endpoint premise: the unit entry ideal produces it. -/
theorem segre_action
    (hspan : Ideal.span (Set.range (fun rs : ι × κ => w rs.1 rs.2))=⊤)
    (hw : ∀ i j s t, w i s*w j t=w i t*w j s)
    (f : A →ₐ[ℂ] ℂ) (a : ι → ℂ) (b : κ → ℂ) (ha : ∃ i,a i≠0)
    (he : ∀ i s, f (w i s)=a i*b s) :
    Spec.map (CommRingCat.ofHom f.toRingHom)≫morphism w hspan hw=
      ComplexProjectiveSchemePoint318.point a ha := by
  obtain ⟨rs,hrs⟩ := AffineComplexProjectiveVector318.evaluation_nonzero
    (fun rs : ι × κ => w rs.1 rs.2) hspan f
  have hcol : ∃ i,a i*b rs.2≠0 := ⟨rs.1,by rwa [he] at hrs⟩
  rw [point_action w hspan hw f rs hrs]
  have hv : (fun i => f (w i rs.2))=fun i => a i*b rs.2 := funext (fun i => he i rs.2)
  simpa only [hv] using RankOneProjectiveColumns318.scheme_segre_column a b ha rs.2 hcol
end RankOneAffinePointAction318
