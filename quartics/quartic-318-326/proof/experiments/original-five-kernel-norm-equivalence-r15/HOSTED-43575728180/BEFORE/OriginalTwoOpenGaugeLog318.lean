module
public import OriginalOpenExponentialNaturality318
public section
noncomputable section
namespace OriginalTwoOpenGaugeLog318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open DualNumberScheme318 AffineHOnePointedDeformation318
open OriginalHOnePointedSurjection318
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- Normalize a whole forward gauge equation on native section-unit carriers
before specializing the opens and cocycles to the original thickening. -/
private lemma native_forward_gauge {Z : Scheme.{0}} (W : Bool → Z.Opens)
    (c d : UnitTransitionCocycle318.Cocycle (StructureUnitsSheaf318.units Z).obj W)
    (a : ∀ k, Γ(Z,W k)ˣ)
    (ha : ∀ k l, d.transition k l =
      UnitTransitionCocycle318.coboundary (StructureUnitsSheaf318.units Z).obj W a k l *
        c.transition k l)
    (x y : Γ(Z,W false ⊓ W true)ˣ)
    (hx : c.transition false true = x) (hy : d.transition false true = y) :
    y = (Units.map (Z.presheaf.map (homOfLE inf_le_left).op).hom.toMonoidHom (a false) *
      (Units.map (Z.presheaf.map (homOfLE inf_le_right).op).hom.toMonoidHom (a true))⁻¹) * x := by
  have h : (d.transition false true : Γ(Z,W false ⊓ W true)ˣ) =
      (Units.map (Z.presheaf.map (homOfLE inf_le_left).op).hom.toMonoidHom (a false) *
        (Units.map (Z.presheaf.map (homOfLE inf_le_right).op).hom.toMonoidHom (a true))⁻¹) *
          (c.transition false true : Γ(Z,W false ⊓ W true)ˣ) := ha false true
  exact hy.symm.trans (h.trans (congrArg (fun z : Γ(Z,W false ⊓ W true)ˣ =>
    (Units.map (Z.presheaf.map (homOfLE inf_le_left).op).hom.toMonoidHom (a false) *
      (Units.map (Z.presheaf.map (homOfLE inf_le_right).op).hom.toMonoidHom (a true))⁻¹) * z) hx))

variable {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ base R)
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : IsAffineOpen (U ⊓ V))
    (x y : Γ(X,U ⊓ V))
lemma original_reduces : UnitCocyclePointedLine318.ReducesToOne (reduction R p)
    (thickOpens p U V) (originalCocycle p U V x) := by
  intro k l
  apply Units.ext
  change (reduction R p).app _ (1 + InfinitesimalUnitCocycle318.epsilon (thickening R p)
    (DualNumberInfinitesimalLines318.epsilon R p) _ * _) = 1
  rw [map_add, map_one, map_mul, DualNumberInfinitesimalLines318.reduction_epsilon_open,
    zero_mul, add_zero]
variable (a : ∀ k, Γ(thickening R p,thickOpens p U V k)ˣ)
    (ra : ∀ k, Units.map ((reduction R p).app (thickOpens p U V k)).hom.toMonoidHom (a k) = 1)
    (ha : ∀ k l, (originalCocycle p U V y).transition k l =
      UnitTransitionCocycle318.coboundary (StructureUnitsSheaf318.units (thickening R p)).obj
        (thickOpens p U V) a k l * (originalCocycle p U V x).transition k l)
include hU hV hUV ra ha in
/-- The actual reduced unit gauge has an original additive logarithm on both
whole affine opens. Its forward equation is exactly finite-minus-infinity. -/
lemma exists_additive : ∃ b : Γ(X,U), ∃ c : Γ(X,V), y =
    InfinitesimalUnitCocycle318.restrict X inf_le_left b -
      InfinitesimalUnitCocycle318.restrict X inf_le_right c + x := by
  letI : IsAffine U.toScheme := hU
  letI : IsAffine V.toScheme := hV
  letI : IsAffine (U ⊓ V).toScheme := hUV
  let b := OriginalOpenUnitLogarithm318.log R p U (a false)
  let c := OriginalOpenUnitLogarithm318.log R p V (a true)
  have hb : OriginalOpenUnitLogarithm318.exp R p U b = a false :=
    OriginalOpenUnitLogarithm318.exp_log R p U (a false)
      (OriginalOpenExponentialNaturality318.reduced_appLE R p (V := U) (a false) (ra false))
  have hc : OriginalOpenUnitLogarithm318.exp R p V c = a true :=
    OriginalOpenUnitLogarithm318.exp_log R p V (a true)
      (OriginalOpenExponentialNaturality318.reduced_appLE R p (V := V) (a true) (ra true))
  refine ⟨b,c,?_⟩
  apply OriginalOpenUnitLogarithm318.exp_injective R p (U ⊓ V)
  have h := native_forward_gauge (thickOpens p U V)
    (originalCocycle p U V x) (originalCocycle p U V y) a ha
    (OriginalOpenUnitLogarithm318.exp R p (U ⊓ V) x)
    (OriginalOpenUnitLogarithm318.exp R p (U ⊓ V) y)
    ((original_forward p U V x).trans
      (OriginalOpenUnitLogarithm318.exp_original R p (U ⊓ V) x).symm)
    ((original_forward p U V y).trans
      (OriginalOpenUnitLogarithm318.exp_original R p (U ⊓ V) y).symm)
  have rb : Units.map ((thickening R p).presheaf.map
        (homOfLE ((pullback.fst p (structureMap R)).preimage_mono
          (show U ⊓ V ≤ U from inf_le_left))).op).hom.toMonoidHom (a false) =
      OriginalOpenUnitLogarithm318.exp R p (U ⊓ V)
        (InfinitesimalUnitCocycle318.restrict X inf_le_left b) := by
    exact (congrArg (Units.map ((thickening R p).presheaf.map
      (homOfLE ((pullback.fst p (structureMap R)).preimage_mono
        (show U ⊓ V ≤ U from inf_le_left))).op).hom.toMonoidHom) hb.symm).trans
      (OriginalOpenExponentialNaturality318.exp_restrict R p (V := U) (W := U ⊓ V)
        inf_le_left b)
  have rc : Units.map ((thickening R p).presheaf.map
        (homOfLE ((pullback.fst p (structureMap R)).preimage_mono
          (show U ⊓ V ≤ V from inf_le_right))).op).hom.toMonoidHom (a true) =
      OriginalOpenUnitLogarithm318.exp R p (U ⊓ V)
        (InfinitesimalUnitCocycle318.restrict X inf_le_right c) := by
    exact (congrArg (Units.map ((thickening R p).presheaf.map
      (homOfLE ((pullback.fst p (structureMap R)).preimage_mono
        (show U ⊓ V ≤ V from inf_le_right))).op).hom.toMonoidHom) hc.symm).trans
      (OriginalOpenExponentialNaturality318.exp_restrict R p (V := V) (W := U ⊓ V)
        inf_le_right c)
  have h' : OriginalOpenUnitLogarithm318.exp R p (U ⊓ V) y =
      (OriginalOpenUnitLogarithm318.exp R p (U ⊓ V)
        (InfinitesimalUnitCocycle318.restrict X inf_le_left b) *
      (OriginalOpenUnitLogarithm318.exp R p (U ⊓ V)
        (InfinitesimalUnitCocycle318.restrict X inf_le_right c))⁻¹) *
      OriginalOpenUnitLogarithm318.exp R p (U ⊓ V) x :=
    h.trans (congrArg (fun z : Γ(thickening R p,
      (pullback.fst p (structureMap R)) ⁻¹ᵁ (U ⊓ V))ˣ =>
        z * OriginalOpenUnitLogarithm318.exp R p (U ⊓ V) x)
      (congrArg₂ (· * ·) rb (congrArg (fun z => z⁻¹) rc)))
  rw [sub_eq_add_neg, OriginalOpenUnitLogarithm318.exp_add,
    OriginalOpenUnitLogarithm318.exp_add, OriginalOpenExponentialNaturality318.exp_neg]
  exact h'
include hU hV hUV in
/-- Any original module-sheaf isomorphism between old H1 representatives gives
the original additive coboundary. No faithfulness of H1 has been assumed. -/
lemma of_iso (e : CocycleModule318.object (thickOpens p U V) (originalCocycle p U V x) ≅
    CocycleModule318.object (thickOpens p U V) (originalCocycle p U V y)) :
    ∃ b : Γ(X,U), ∃ c : Γ(X,V), y =
      InfinitesimalUnitCocycle318.restrict X inf_le_left b -
        InfinitesimalUnitCocycle318.restrict X inf_le_right c + x := by
  obtain ⟨a,ha⟩ := OriginalLineIsoGauge318.equivalent (thickOpens p U V)
    (originalCocycle p U V x) (originalCocycle p U V y) e
  obtain ⟨b,rb,hb⟩ := SplitReducedGauge318.exists_reduced_gauge (reduction R p)
    (pullback.fst p (structureMap R)) (reduction_fst R p) (thickOpens p U V)
      (OriginalTwoOpenReducedCocycle318.stable p U V) (originalCocycle p U V x) (originalCocycle p U V y)
      (original_reduces p U V x) (original_reduces p U V y) a ha
  exact exists_additive p U V hU hV hUV x y b rb hb
end OriginalTwoOpenGaugeLog318
