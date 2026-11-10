module
public import InjectiveCoverGauge318
public import CocycleRefinementIso318
public section
noncomputable section
namespace InjectiveCoverPointed318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open OriginalStructureInjectivePresentation318 InjectiveCoverCocycle318 DualNumberScheme318
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ base R)
    {ι : Type} (U : ι → X.Opens) (hU : (⊤ : X.Opens) ≤ ⨆ i, U i)
@[expose] def thickOpens (i : ι) : (thickening R p).Opens :=
  (pullback.fst p (structureMap R)) ⁻¹ᵁ U i
include hU in
lemma thick_cover : (⊤ : (thickening R p).Opens) ≤ ⨆ i, thickOpens p U i :=
  LinePullbackFrames318.preimage_cover _ _ hU
@[expose] def thickCocycle {t : (Q X).obj.obj (op ⊤)} (a : Lifts X U t) :=
  AdditiveCocycleRefinement318.cocycle (pullback.fst p (structureMap R)) U
    (thickOpens p U) (fun _ => le_rfl) (cocycle a)
@[expose] def deformation {t : (Q X).obj.obj (op ⊤)} (a : Lifts X U t) :
    DualNumberScheme318.Deformation R p :=
  DualNumberInfinitesimalLines318.deformation R p (thickOpens p U) (thick_cover p U hU)
    (thickCocycle p U a)
@[expose] def pointed {t : (Q X).obj.obj (op ⊤)} (a : Lifts X U t) : DualNumberScheme318.Class R p :=
  PointedLineDeformation318.classOf (reduction R p) (deformation p U hU a)
lemma same_cover {t s : (Q X).obj.obj (op ⊤)} (a : Lifts X U t) (b : Lifts X U s)
    (h : boundary X t = boundary X s) : pointed p U hU a = pointed p U hU b := by
  have he : Quotient.mk (AdditiveDeformationClasses318.additiveSetoid X U) (cocycle a) =
      Quotient.mk _ (cocycle b) := Quotient.sound (InjectiveCoverGauge318.related a b h)
  exact congrArg (fun c => AdditiveDeformationClasses318.dualNumberClasses p (thickOpens p U)
    (thick_cover p U hU) (AdditiveCocycleRefinement318.classes
      (pullback.fst p (structureMap R)) U (thickOpens p U) (fun _ => le_rfl) c)) he
variable {κ : Type} (V : κ → X.Opens) (r : κ → ι) (hr : ∀ k, V k ≤ U (r k))
    (hV : (⊤ : X.Opens) ≤ ⨆ k, V k)
lemma units_refine {t : (Q X).obj.obj (op ⊤)} (a : Lifts X U t) :
    UnitCocycleRefinement318.refine
      (InfinitesimalUnitCocycle318.cocycle _ (DualNumberInfinitesimalLines318.epsilon R p)
        (DualNumberInfinitesimalLines318.epsilon_square R p) (thickOpens p U) (thickCocycle p U a))
      (thickOpens p V) r (fun k => (pullback.fst p (structureMap R)).preimage_mono (hr k)) =
    InfinitesimalUnitCocycle318.cocycle _ (DualNumberInfinitesimalLines318.epsilon R p)
      (DualNumberInfinitesimalLines318.epsilon_square R p) (thickOpens p V)
      (thickCocycle p V (InjectiveCoverCocycle318.refine a V r hr)) := by
  apply UnitTransitionCocycle318.Cocycle.ext
  intro k l
  change Units.map (InfinitesimalUnitCocycle318.restrict _ _).toMonoidHom
    (InfinitesimalUnitCocycle318.unit _ _ _ _
      ((pullback.fst p (structureMap R)).appLE _ _ _ (coefficient a (r k) (r l)))) =
    InfinitesimalUnitCocycle318.unit _ _ _ _
      ((pullback.fst p (structureMap R)).appLE _ _ _
        (coefficient (InjectiveCoverCocycle318.refine a V r hr) k l))
  rw [InfinitesimalUnitCocycle318.unit_restrict,
    AdditiveCocycleRefinement318.restrict_appLE, InjectiveCoverCocycle318.refine_coefficient]
/-- Actual cocycle sheaf refinement, followed by the proved special-fiber scalar
correction, preserves the pointed class for every original cover refinement. -/
lemma refinement {t : (Q X).obj.obj (op ⊤)} (a : Lifts X U t) :
    pointed p U hU a = pointed p V hV (InjectiveCoverCocycle318.refine a V r hr) := by
  apply DualNumberPointedKernel318.class_eq_of_iso p
  exact CocycleRefinementIso318.iso (thickOpens p U)
      (InfinitesimalUnitCocycle318.cocycle _ (DualNumberInfinitesimalLines318.epsilon R p)
        (DualNumberInfinitesimalLines318.epsilon_square R p) _ (thickCocycle p U a))
      (thickOpens p V) r (fun k => (pullback.fst p (structureMap R)).preimage_mono (hr k))
      (thick_cover p V hV) ≪≫
    eqToIso (congrArg (CocycleModule318.object (thickOpens p V)) (units_refine p U V r hr a))
/-- Arbitrary covers are compared on their COMPLETE common cover. Equality in
original H1 supplies the coboundary there, with no affine-intersection premise. -/
lemma common_cover {t s : (Q X).obj.obj (op ⊤)} (a : Lifts X U t) (b : Lifts X V s)
    (h : boundary X t = boundary X s) : pointed p U hU a = pointed p V hV b := by
  let W := UnitCocycleRefinement318.common U V
  have hW : (⊤ : X.Opens) ≤ ⨆ k, W k := UnitCocycleRefinement318.common_cover U V hU hV
  calc
    _ = pointed p W hW (InjectiveCoverCocycle318.refine a W Prod.fst (fun _ => inf_le_left)) :=
      refinement p U hU W Prod.fst (fun _ => inf_le_left) hW a
    _ = pointed p W hW (InjectiveCoverCocycle318.refine b W Prod.snd (fun _ => inf_le_right)) :=
      same_cover p W hW _ _ h
    _ = _ := (refinement p V hV W Prod.snd (fun _ => inf_le_right) hW b).symm
end InjectiveCoverPointed318
