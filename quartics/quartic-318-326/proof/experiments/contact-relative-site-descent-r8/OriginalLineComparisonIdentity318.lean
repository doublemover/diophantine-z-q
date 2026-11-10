module
public import OriginalLineComparisonComposition318
public section
noncomputable section
namespace OriginalLineComparisonIdentity318
open AlgebraicGeometry CategoryTheory LineSheafClass318 OriginalLineAffineBaseChange318
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : CommRingCat.{u}) (L : Line (Spec R))

lemma canonicalIso_adjoint :
    (tilde.adjunction (R := R)).homEquiv _ _ L.object.fromTildeΓ =
      𝟙 (OriginalLineAffineModel318.sections R L) := by
  rw [Adjunction.homEquiv_unit]
  exact (tilde.adjunction (R := R)).right_triangle_components L.object

/-- Categorical cancellation is proved before specializing to the original
sheaf categories, keeping their concrete instance terms out of the proof. -/
lemma comparison_cancellation {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (G : C ⥤ C) (P : D ⥤ D)
    (a : F ⋙ P ≅ G ⋙ F) (p : P ≅ 𝟭 D) (q : G ≅ 𝟭 C)
    (N : C) (M : D) (f : F.obj N ⟶ M)
    (h : a.hom.app N ≫ F.map (q.hom.app N) = p.hom.app (F.obj N)) :
    (a.inv.app N ≫ P.map f) ≫ p.hom.app M = F.map (q.hom.app N) ≫ f := by
  rw [Category.assoc, p.hom.naturality, ← h]
  simp only [Functor.id_map,Category.assoc]
  change (a.app N).inv ≫ (a.app N).hom ≫ F.map (q.hom.app N) ≫ f = _
  exact (a.app N).inv_hom_id_assoc _

/-- The actual identity comparison retains the original line's counit. -/
lemma sheaf_identity :
    (sheafIso (𝟙 R) L).hom ≫ (TildePullbackIdentity318.pullbackId R).hom.app L.object =
      (tilde.functor R).map ((ModuleCat.extendScalarsId R).hom.app
        (OriginalLineAffineModel318.sections R L)) ≫ L.object.fromTildeΓ := by
  rw [sheafIso_counit]
  exact comparison_cancellation (tilde.functor R) _ _
    (TildePullback318.pullbackIso (𝟙 R))
    (TildePullbackIdentity318.pullbackId R) (ModuleCat.extendScalarsId R)
    (OriginalLineAffineModel318.sections R L) L.object L.object.fromTildeΓ
    (TildePullbackIdentity318.identity_app R (OriginalLineAffineModel318.sections R L))

/-- The whole adjunction identity calculation is proved generically before
specialization, so kernel checking does not repeatedly normalize concrete
localization/module instances through each naturality rewrite. -/
lemma adjoint_comparison_identity {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G)
    (Z : C) (M N : D) (b : F.obj Z ⟶ N) (p : N ⟶ M)
    (q : Z ⟶ G.obj M) (c : F.obj (G.obj M) ⟶ M)
    (s : Z ⟶ G.obj N) (hb : a.homEquiv Z N b = s)
    (hc : a.homEquiv (G.obj M) M c = 𝟙 (G.obj M))
    (h : b ≫ p = F.map q ≫ c) : s ≫ G.map p = q := by
  calc
    s ≫ G.map p = a.homEquiv Z M (b ≫ p) := by
      rw [a.homEquiv_naturality_right,hb]
    _ = a.homEquiv Z M (F.map q ≫ c) := congrArg (a.homEquiv Z M) h
    _ = q ≫ a.homEquiv (G.obj M) M c := a.homEquiv_naturality_left q c
    _ = q := by rw [hc,Category.comp_id]

/-- Faithful detection by the SAME original counit avoids specializing a
homEquiv equality through the concrete localization instances. -/
lemma counit_comparison_identity {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) [F.Faithful] (G : D ⥤ C) (c : G ⋙ F ⟶ 𝟭 D)
    (Z : C) (M N : D) [Mono (c.app M)]
    (s : Z ⟶ G.obj N) (p : N ⟶ M) (q : Z ⟶ G.obj M)
    (b : F.obj Z ⟶ N) (hs : F.map s ≫ c.app N = b)
    (h : b ≫ p = F.map q ≫ c.app M) : s ≫ G.map p = q := by
  apply F.map_injective
  apply (cancel_mono (c.app M)).mp
  rw [Functor.map_comp,Category.assoc]
  have hn := c.naturality p
  change F.map (G.map p) ≫ c.app M = c.app N ≫ p at hn
  rw [hn,← Category.assoc,hs]
  exact h

/-- Exact identity for the original affine line global sections. -/
lemma sections_identity :
    (sectionsIso (𝟙 R) L).hom ≫
      moduleSpecΓFunctor.map ((TildePullbackIdentity318.pullbackId R).hom.app L.object) =
        (ModuleCat.extendScalarsId R).hom.app (OriginalLineAffineModel318.sections R L) :=
  counit_comparison_identity (tilde.functor R) moduleSpecΓFunctor
    Scheme.Modules.fromTildeΓNatTrans (extendedSections (𝟙 R) L)
    L.object (LineSheafPullback318.line (Spec.map (𝟙 R)) L).object
    (sectionsIso (𝟙 R) L).hom ((TildePullbackIdentity318.pullbackId R).hom.app L.object)
    ((ModuleCat.extendScalarsId R).hom.app (OriginalLineAffineModel318.sections R L))
    (sheafIso (𝟙 R) L).hom
    (OriginalLineComparisonComposition318.sectionsIso_counit (𝟙 R) L)
    (sheaf_identity R L)

end OriginalLineComparisonIdentity318
