module
public import ActualDescentBaseChangeDiagram318
public section
noncomputable section
namespace SheafArrowBaseChange318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 2000000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {U U' D D' T : Scheme.{u}} (a : U' ⟶ U) (q : D' ⟶ D)

/-- Both original paths around the actual scheme square give the
specified endpoint comparison for pulling back a descent overlap. -/
@[expose] def endpoint (p : D ⟶ U) (r : D' ⟶ U') (h : q ≫ p = r ≫ a) :
    Scheme.Modules.pullback a ⋙ Scheme.Modules.pullback r ≅
      Scheme.Modules.pullback p ⋙ Scheme.Modules.pullback q :=
  PullbackPathComposition318.iso r a (r ≫ a) rfl ≪≫
    (PullbackPathComposition318.iso q p (r ≫ a) h).symm

/-- Rebase an original sheaf overlap along its genuine scheme square. -/
@[expose] def overlap (M : U.Modules) (p₀ p₁ : D ⟶ U) (r₀ r₁ : D' ⟶ U')
    (h₀ : q ≫ p₀ = r₀ ≫ a) (h₁ : q ≫ p₁ = r₁ ≫ a)
    (τ : (Scheme.Modules.pullback p₀).obj M ⟶ (Scheme.Modules.pullback p₁).obj M) :
    (Scheme.Modules.pullback r₀).obj ((Scheme.Modules.pullback a).obj M) ⟶
      (Scheme.Modules.pullback r₁).obj ((Scheme.Modules.pullback a).obj M) :=
  (endpoint a q p₀ r₀ h₀).hom.app M ≫ (Scheme.Modules.pullback q).map τ ≫
    (endpoint a q p₁ r₁ h₁).inv.app M

lemma overlap_identity (M : U.Modules) (p : D ⟶ U) (r : D' ⟶ U') (h : q ≫ p = r ≫ a) :
    overlap a q M p p r r h h (𝟙 _) = 𝟙 _ := by
  simp only [overlap, Functor.map_id, Category.id_comp, Iso.hom_inv_id_app]

lemma overlap_composition (M : U.Modules) (p₀ p₁ p₂ : D ⟶ U) (r₀ r₁ r₂ : D' ⟶ U')
    (h₀ : q ≫ p₀ = r₀ ≫ a) (h₁ : q ≫ p₁ = r₁ ≫ a) (h₂ : q ≫ p₂ = r₂ ≫ a)
    (τ : (Scheme.Modules.pullback p₀).obj M ⟶ (Scheme.Modules.pullback p₁).obj M)
    (σ : (Scheme.Modules.pullback p₁).obj M ⟶ (Scheme.Modules.pullback p₂).obj M) :
    overlap a q M p₀ p₁ r₀ r₁ h₀ h₁ τ ≫ overlap a q M p₁ p₂ r₁ r₂ h₁ h₂ σ =
      overlap a q M p₀ p₂ r₀ r₂ h₀ h₂ (τ ≫ σ) := by
  simp only [overlap, Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc]

/-- The endpoint comparison commutes with one further actual pullback.
Both equalities are the original named-path associativity theorem. -/
lemma endpoint_composition (M : U.Modules) (p : D ⟶ U) (r : D' ⟶ U')
    (h : q ≫ p = r ≫ a) (z : T ⟶ D') (v : T ⟶ U') (hz : z ≫ r = v)
    (zq : T ⟶ D) (hzq : z ≫ q = zq) (hc : zq ≫ p = v ≫ a) :
    (PullbackPathComposition318.iso z r v hz).hom.app ((Scheme.Modules.pullback a).obj M) ≫
        (endpoint a zq p v hc).hom.app M =
      (Scheme.Modules.pullback z).map ((endpoint a q p r h).hom.app M) ≫
        (PullbackPathComposition318.iso z q zq hzq).hom.app ((Scheme.Modules.pullback p).obj M) := by
  have hva : z ≫ (r ≫ a) = v ≫ a := by rw [← Category.assoc, hz]
  have hleft := PullbackPathComposition318.assoc z r a v (r ≫ a) (v ≫ a) hz rfl rfl hva M
  have hright := PullbackPathComposition318.assoc z q p zq (r ≫ a) (v ≫ a) hzq h hc hva M
  apply (cancel_mono ((PullbackPathComposition318.iso zq p (v ≫ a) hc).hom.app M)).mp
  simp only [endpoint, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.map_comp, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [hright]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id, Category.id_comp]
  exact hleft

/-- Normalized original edge pullback commutes with this rebase. The
result keeps the literal composite zq and the original endpoint paths. -/
lemma successive (M : U.Modules) (p₀ p₁ : D ⟶ U) (r₀ r₁ : D' ⟶ U')
    (h₀ : q ≫ p₀ = r₀ ≫ a) (h₁ : q ≫ p₁ = r₁ ≫ a)
    (z : T ⟶ D') (v₀ v₁ : T ⟶ U') (hz₀ : z ≫ r₀ = v₀) (hz₁ : z ≫ r₁ = v₁)
    (zq : T ⟶ D) (hzq : z ≫ q = zq)
    (hc₀ : zq ≫ p₀ = v₀ ≫ a) (hc₁ : zq ≫ p₁ = v₁ ≫ a)
    (τ : (Scheme.Modules.pullback p₀).obj M ⟶ (Scheme.Modules.pullback p₁).obj M) :
    SheafPathTransport318.transport ((Scheme.Modules.pullback a).obj M) z r₀ r₁ v₀ v₁ hz₀ hz₁
        (overlap a q M p₀ p₁ r₀ r₁ h₀ h₁ τ) =
      overlap a zq M p₀ p₁ v₀ v₁ hc₀ hc₁ τ := by
  let F := Scheme.Modules.pullback z
  let c := PullbackPathComposition318.iso z q zq hzq
  let x₀ := ((PullbackPathComposition318.iso z r₀ v₀ hz₀).app
    ((Scheme.Modules.pullback a).obj M)).symm ≪≫ F.mapIso ((endpoint a q p₀ r₀ h₀).app M)
  let x₁ := ((PullbackPathComposition318.iso z r₁ v₁ hz₁).app
    ((Scheme.Modules.pullback a).obj M)).symm ≪≫ F.mapIso ((endpoint a q p₁ r₁ h₁).app M)
  have hx₀ : x₀ = (endpoint a zq p₀ v₀ hc₀).app M ≪≫
      (c.app ((Scheme.Modules.pullback p₀).obj M)).symm := by
    apply Iso.ext
    apply (cancel_mono (c.hom.app ((Scheme.Modules.pullback p₀).obj M))).mp
    simp only [x₀, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom,
      Iso.app_inv, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    rw [← endpoint_composition a q M p₀ r₀ h₀ z v₀ hz₀ zq hzq hc₀]
    exact Iso.inv_hom_id_app_assoc _ _ _
  have hx₁ : x₁ = (endpoint a zq p₁ v₁ hc₁).app M ≪≫
      (c.app ((Scheme.Modules.pullback p₁).obj M)).symm := by
    apply Iso.ext
    apply (cancel_mono (c.hom.app ((Scheme.Modules.pullback p₁).obj M))).mp
    simp only [x₁, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom,
      Iso.app_inv, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    rw [← endpoint_composition a q M p₁ r₁ h₁ z v₁ hz₁ zq hzq hc₁]
    exact Iso.inv_hom_id_app_assoc _ _ _
  have h : x₀.hom ≫ F.map ((Scheme.Modules.pullback q).map τ) ≫ x₁.inv =
      (endpoint a zq p₀ v₀ hc₀).hom.app M ≫ (Scheme.Modules.pullback zq).map τ ≫
        (endpoint a zq p₁ v₁ hc₁).inv.app M := by
    rw [hx₀, hx₁]
    simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      Iso.app_hom, Iso.app_inv, Category.assoc]
    rw [← c.inv.naturality_assoc τ, Iso.inv_hom_id_app_assoc]
  simpa only [SheafPathTransport318.transport, overlap, x₀, x₁, Iso.trans_hom,
    Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Iso.app_hom, Iso.app_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, Functor.map_comp, Category.assoc] using h
/-- Rebase after an original normalized edge pullback is the same exact
composite rebase. This is the original successive-transport theorem,
conjugated only by the named new endpoint paths. -/
lemma original_successive {T' : Scheme.{u}} (M : U.Modules)
    (p₀ p₁ : D ⟶ U) (w₀ w₁ : D' ⟶ U) (he₀ : q ≫ p₀ = w₀) (he₁ : q ≫ p₁ = w₁)
    (t : T' ⟶ D') (v₀ v₁ : T' ⟶ U')
    (ht₀ : t ≫ w₀ = v₀ ≫ a) (ht₁ : t ≫ w₁ = v₁ ≫ a)
    (tq : T' ⟶ D) (htq : t ≫ q = tq)
    (hc₀ : tq ≫ p₀ = v₀ ≫ a) (hc₁ : tq ≫ p₁ = v₁ ≫ a)
    (τ : (Scheme.Modules.pullback p₀).obj M ⟶ (Scheme.Modules.pullback p₁).obj M) :
    overlap a t M w₀ w₁ v₀ v₁ ht₀ ht₁
        (SheafPathTransport318.transport M q p₀ p₁ w₀ w₁ he₀ he₁ τ) =
      overlap a tq M p₀ p₁ v₀ v₁ hc₀ hc₁ τ := by
  have h := SheafPathTransport318.successive M q t tq htq p₀ p₁ w₀ w₁
    (v₀ ≫ a) (v₁ ≫ a) he₀ he₁ ht₀ ht₁ hc₀ hc₁ τ
  have hh := congrArg (fun k =>
    (PullbackPathComposition318.iso v₀ a (v₀ ≫ a) rfl).hom.app M ≫ k ≫
      (PullbackPathComposition318.iso v₁ a (v₁ ≫ a) rfl).inv.app M) h
  simpa only [overlap, endpoint, SheafPathTransport318.transport, Iso.trans_hom,
    Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
    Functor.map_comp, Category.assoc] using hh
/-- The actual commuting square of edge maps transports arbitrary overlap
equations across changing covering arrows. No new cocycle law is assumed. -/
lemma edge_square {T' : Scheme.{u}} (M : U.Modules)
    (p₀ p₁ : D ⟶ U) (r₀ r₁ : D' ⟶ U')
    (h₀ : q ≫ p₀ = r₀ ≫ a) (h₁ : q ≫ p₁ = r₁ ≫ a)
    (e : T ⟶ D) (z : T' ⟶ D') (t : T' ⟶ T) (hs : z ≫ q = t ≫ e)
    (w₀ w₁ : T ⟶ U) (v₀ v₁ : T' ⟶ U')
    (he₀ : e ≫ p₀ = w₀) (he₁ : e ≫ p₁ = w₁)
    (hz₀ : z ≫ r₀ = v₀) (hz₁ : z ≫ r₁ = v₁)
    (ht₀ : t ≫ w₀ = v₀ ≫ a) (ht₁ : t ≫ w₁ = v₁ ≫ a)
    (τ : (Scheme.Modules.pullback p₀).obj M ⟶ (Scheme.Modules.pullback p₁).obj M) :
    SheafPathTransport318.transport ((Scheme.Modules.pullback a).obj M) z r₀ r₁ v₀ v₁ hz₀ hz₁
        (overlap a q M p₀ p₁ r₀ r₁ h₀ h₁ τ) =
      overlap a t M w₀ w₁ v₀ v₁ ht₀ ht₁
        (SheafPathTransport318.transport M e p₀ p₁ w₀ w₁ he₀ he₁ τ) := by
  have hc₀ : (t ≫ e) ≫ p₀ = v₀ ≫ a := by rw [Category.assoc, he₀, ht₀]
  have hc₁ : (t ≫ e) ≫ p₁ = v₁ ≫ a := by rw [Category.assoc, he₁, ht₁]
  rw [successive a q M p₀ p₁ r₀ r₁ h₀ h₁ z v₀ v₁ hz₀ hz₁ (t ≫ e) hs hc₀ hc₁,
    original_successive a e M p₀ p₁ w₀ w₁ he₀ he₁ t v₀ v₁ ht₀ ht₁ (t ≫ e) rfl hc₀ hc₁]
end SheafArrowBaseChange318
