module
public import MixedCoverRecovery318
public section
noncomputable section
namespace ActualDescentEvaluationChange318
open AlgebraicGeometry CategoryTheory ActualOverlapDiagram318
open OriginalSchemeDescentData318 ActualDescentTestEvaluation318
set_option maxHeartbeats 2600000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y V Z : Scheme.{u}} {f : X ⟶ Y} (D : Datum f)
  (g : V ⟶ Z) (a : V ⟶ X) (b : Z ⟶ Y) (square : a ≫ f = g ≫ b)

include square in
lemma endpoints : (first g ≫ a) ≫ f = (second g ≫ a) ≫ f := by
  rw [Category.assoc,Category.assoc,square,← Category.assoc,← Category.assoc,edge_condition]

/-- The actual changed overlap, normalized only by its original two
path comparisons, is exactly the original evaluated test pair. -/
lemma overlap : (OriginalSchemeDescentBaseChange318.datum f g a b square D).overlap =
    (PullbackPathComposition318.iso (first g) a (first g ≫ a) rfl).hom.app D.line.object ≫
      map D (first g ≫ a) (second g ≫ a) (endpoints g a b square) ≫
        (PullbackPathComposition318.iso (second g) a (second g ≫ a) rfl).inv.app D.line.object := by
  simp only [OriginalSchemeDescentBaseChange318.datum,OriginalSchemeDescentBaseChange318.overlap,
    SheafArrowBaseChange318.overlap,SheafArrowBaseChange318.endpoint,
    map,SheafPathTransport318.transport,Iso.trans_hom,Iso.trans_inv,Iso.symm_hom,Iso.symm_inv,
    NatTrans.comp_app,Category.assoc] <;> rfl

variable (c : V ⟶ X) (square' : c ≫ f = g ≫ b)
include square square' in
lemma same_base : a ≫ f = c ≫ f := square.trans square'.symm

/-- Changing a lift of the same map over the base produces an actual
morphism of the original descent data. Compatibility is the original
triple law evaluated on the four actual double-cover endpoints. -/
@[expose] def hom : OriginalSchemeDescentBaseChangeMaps318.Hom
    (OriginalSchemeDescentBaseChange318.datum f g a b square D)
    (OriginalSchemeDescentBaseChange318.datum f g c b square' D) where
  sheafHom := map D a c (same_base g a b square c square')
  commutes := by
    let p := first g
    let q := second g
    let ca₀ := (PullbackPathComposition318.iso p a (p ≫ a) rfl).app D.line.object
    let ca₁ := (PullbackPathComposition318.iso q a (q ≫ a) rfl).app D.line.object
    let cc₀ := (PullbackPathComposition318.iso p c (p ≫ c) rfl).app D.line.object
    let cc₁ := (PullbackPathComposition318.iso q c (q ≫ c) rfl).app D.line.object
    let k := map D a c (same_base g a b square c square')
    have hp := ActualDescentEvaluationNaturality318.pullback D a c
      (same_base g a b square c square') p
    have hq := ActualDescentEvaluationNaturality318.pullback D a c
      (same_base g a b square c square') q
    change ca₀.inv ≫ (Scheme.Modules.pullback p).map k ≫ cc₀.hom = _ at hp
    change ca₁.inv ≫ (Scheme.Modules.pullback q).map k ≫ cc₁.hom = _ at hq
    rw [overlap,overlap]
    apply (cancel_epi ca₀.inv).mp
    apply (cancel_mono cc₁.hom).mp
    simp only [ca₀,cc₁,Iso.app_hom,Iso.app_inv,Category.assoc,
      Iso.inv_hom_id_app_assoc,Iso.inv_hom_id_app,Category.comp_id]
    change map D (p ≫ a) (q ≫ a) (endpoints g a b square) ≫
        (ca₁.inv ≫ (Scheme.Modules.pullback q).map k ≫ cc₁.hom) =
      (ca₀.inv ≫ (Scheme.Modules.pullback p).map k ≫ cc₀.hom) ≫
        map D (p ≫ c) (q ≫ c) (endpoints g c b square')
    rw [hp,hq,composition,composition]
end ActualDescentEvaluationChange318
