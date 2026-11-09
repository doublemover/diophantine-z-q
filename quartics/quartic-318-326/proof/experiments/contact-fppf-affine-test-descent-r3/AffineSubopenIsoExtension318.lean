module
public import AffineChartLocalPairs318
public section
noncomputable section
namespace AffineSubopenIsoExtension318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace ModuleLocalGluing318
open OpenSheafTransition318
set_option maxHeartbeats 2600000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} {A B : X.Modules} (Z : X.Opens)

/-- Original affine common-subopen isos, with the actual over-open
restriction law; no data on non-affine subopens is assumed. -/
structure Data where
  app : ∀ (W : X.affineOpens), W.1 ≤ Z → A.over W.1 ≅ B.over W.1
  natural : ∀ (W V : X.affineOpens) (hW : W.1 ≤ Z) (h : V.1 ≤ W.1),
    restrictIso (app W hW) h = app V (h.trans hW)

abbrev image (T : Z.toScheme.affineOpens) : X.affineOpens :=
  ⟨Z.ι ''ᵁ T.1, T.2.image_of_isOpenImmersion Z.ι⟩
lemma image_le (T : Z.toScheme.affineOpens) : (image Z T).1 ≤ Z := by
  simpa using Z.ι.image_le_opensRange T.1
lemma image_mono (T S : Z.toScheme.affineOpens) (h : S.1 ≤ T.1) :
    (image Z S).1 ≤ (image Z T).1 := by
  intro x hx
  obtain ⟨y,hy,rfl⟩ := hx
  exact ⟨y,h hy,rfl⟩

variable (D : Data (A:=A) (B:=B) Z)

/-- The scalar on the restricted sheaf is pulled back by the original
appIso inverse. The component map is linear for precisely this action. -/
@[expose] def component (T : Z.toScheme.affineOpens) :
    Γ(A.restrict Z.ι,T.1) ≃ₗ[Γ(Z.toScheme,T.1)] Γ(B.restrict Z.ι,T.1) where
  toEquiv := (OpenSheafTransition318.component (D.app (image Z T) (image_le Z T))
    (image Z T).1 le_rfl).toEquiv
  map_add' := (OpenSheafTransition318.component (D.app (image Z T) (image_le Z T))
    (image Z T).1 le_rfl).map_add
  map_smul' a s := by
    change OpenSheafTransition318.component (D.app (image Z T) (image_le Z T))
        (image Z T).1 le_rfl ((Z.ι.appIso T.1).inv a • s) =
      (Z.ι.appIso T.1).inv a • OpenSheafTransition318.component
        (D.app (image Z T) (image_le Z T)) (image Z T).1 le_rfl s
    exact (OpenSheafTransition318.component (D.app (image Z T) (image_le Z T))
      (image Z T).1 le_rfl).map_smul _ _

lemma component_natural (T S : Z.toScheme.affineOpens) (h : S.1 ≤ T.1)
    (s : Γ(A.restrict Z.ι,T.1)) :
    res (B.restrict Z.ι) h (component Z D T s) =
      component Z D S (res (A.restrict Z.ι) h s) := by
  change res B (image_mono Z T S h)
      (OpenSheafTransition318.component (D.app (image Z T) (image_le Z T)) (image Z T).1 le_rfl s) =
    OpenSheafTransition318.component (D.app (image Z S) (image_le Z S)) (image Z S).1 le_rfl
      (res A (image_mono Z T S h) s)
  rw [OpenSheafTransition318.component_natural]
  have he := congrArg (fun e => OpenSheafTransition318.component e (image Z S).1 le_rfl
      (res A (image_mono Z T S h) s))
    (D.natural (image Z T) (image Z S) (image_le Z T) (image_mono Z T S h))
  simpa only [OpenSheafTransition318.component_restrict] using he

@[expose] def basisData : AffineBasisModuleIsomorphisms318.IsoData
    (A.restrict Z.ι) (B.restrict Z.ι) where
  app := component Z D
  natural := component_natural Z D

/-- Original ambient affine-subopen isos extend to an actual iso on the
entire original open subscheme, even when it is not affine. -/
@[expose] def iso : A.restrict Z.ι ≅ B.restrict Z.ι :=
  AffineBasisModuleIsomorphisms318.iso (basisData Z D)

lemma iso_affine (T : Z.toScheme.affineOpens) (s : Γ(A.restrict Z.ι,T.1)) :
    (iso Z D).hom.app T.1 s =
      OpenSheafTransition318.component (D.app (image Z T) (image_le Z T)) (image Z T).1 le_rfl s :=
  AffineBasisModuleIsomorphisms318.iso_affine (basisData Z D) T s
end AffineSubopenIsoExtension318
