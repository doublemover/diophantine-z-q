module
public import OpenRestrictionPathCoherence318
public import OpenSchemeTransition318
public section
noncomputable section
namespace LocalChartTransition318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open OpenChartModuleImages318 OpenSheafRestrictionCompatibility318 OpenRestrictionPathCoherence318
set_option maxHeartbeats 1600000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
  (F : ∀ i, (U i).toScheme.Modules)

abbrev Pair (i j : ι) :=
  (F i).restrict (X.homOfLE (show U i ⊓ U j ≤ U i from inf_le_left)) ≅
    (F j).restrict (X.homOfLE (show U i ⊓ U j ≤ U j from inf_le_right))

/-- Original local-chart transition restricted to a common subchart,
using original restriction composition at both local endpoints. -/
@[expose] def edge {i j : ι} (e : Pair U F i j) (V : X.Opens) (h : V ≤ U i ⊓ U j) :
    (F i).restrict (X.homOfLE (h.trans inf_le_left)) ≅
      (F j).restrict (X.homOfLE (h.trans inf_le_right)) :=
  ((collapse h inf_le_left).app (F i)).symm ≪≫
    (Scheme.Modules.restrictFunctor (X.homOfLE h)).mapIso e ≪≫
      (collapse h inf_le_right).app (F j)

/-- The original local pair iso as an actual ambient scheme restriction
iso, through the specified original direct-image subchart recoveries. -/
@[expose] def ambientTransition {i j : ι} (e : Pair U F i j) :
    (ambient U F i).restrict (U i ⊓ U j).ι ≅ (ambient U F j).restrict (U i ⊓ U j).ι :=
  subchartRecovery U F i (U i ⊓ U j) inf_le_left ≪≫ e ≪≫
    (subchartRecovery U F j (U i ⊓ U j) inf_le_right).symm

/-- The original direct-image pair conversion commutes with actual
subchart restriction. This supplies the missing triple normalization join. -/
lemma ambient_restriction {i j : ι} (e : Pair U F i j) (V : X.Opens) (h : V ≤ U i ⊓ U j) :
    schemeRestrict (ambientTransition U F e) h =
      subchartRecovery U F i V (h.trans inf_le_left) ≪≫ edge U F e V h ≪≫
        (subchartRecovery U F j V (h.trans inf_le_right)).symm := by
  rw [← subchartRecovery_comp U F i h inf_le_left,
    ← subchartRecovery_comp U F j h inf_le_right]
  apply Iso.ext
  simp only [schemeRestrict, ambientTransition, edge, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc,
    Iso.hom_inv_id_app_assoc]

/-- Actual local chart module data: original local pair isomorphisms and
original restriction-normalized triple cocycle. No direct-image or over-open
cocycle is an input. -/
structure Data where
  transition : ∀ i j, Pair U F i j
  identity : ∀ i, transition i i = Iso.refl _
  cocycle : ∀ i j k,
    edge U F (transition i j) ((U i ⊓ U j) ⊓ U k) inf_le_left ≪≫
      edge U F (transition j k) ((U i ⊓ U j) ⊓ U k)
        (le_inf (inf_le_left.trans inf_le_right) inf_le_right) =
    edge U F (transition i k) ((U i ⊓ U j) ⊓ U k)
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right)

variable {U F} (D : Data U F)
/-- Actual Fi-only triple equations imply precisely the original ambient
scheme triple equations required downstream by object gluing. -/
@[expose] def ambientData : OpenSchemeTransition318.Data U (ambient U F) where
  transition i j := ambientTransition U F (D.transition i j)
  identity i := by
    apply Iso.ext
    simp only [ambientTransition, D.identity, Iso.trans_hom, Iso.refl_hom,
      Iso.symm_hom, Category.id_comp, Iso.hom_inv_id]
  cocycle i j k := by
    rw [ambient_restriction, ambient_restriction, ambient_restriction]
    apply Iso.ext
    simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc] using
      congrArg (fun e =>
        (subchartRecovery U F i ((U i ⊓ U j) ⊓ U k)
          (inf_le_left.trans inf_le_left)).hom ≫ e.hom ≫
        (subchartRecovery U F k ((U i ⊓ U j) ⊓ U k) inf_le_right).inv)
        (D.cocycle i j k)
end LocalChartTransition318
