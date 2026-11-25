module

public import OriginalActualChartPairEvaluation318
public import OriginalActualRegularMapAtComplexChart318
public import OriginalRetainedAffineChartPointEquiv318

@[expose] public section
noncomputable section

namespace OriginalRetainedMultiplicationInTrueCharts318

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open OriginalRetainedProjectiveAffinePiece318 OriginalRetainedClosedProjectiveEvaluation318
open OriginalRetainedProjectiveAffinePoints318 OriginalRetainedComplexZeroByPasting318
open OriginalRetainedAffineChartPointEquiv318 OriginalActualChartPairEvaluation318
open OriginalActualRegularMapAtComplexChart318
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

variable {κ : Type} [Fintype κ] [DecidableEq κ]
variable {A Y E : Scheme} (a : A ⟶ Y) [GrpObj (Over.mk a)] (P33 : E ⟶ Y) (σ : T ⟶ E)
local notation "G" => fiber a (σ≫P33)
local notation "X" => retainedCarrier a P33 σ
local notation "P" => (Over.mk (𝟙 T) ⟶ G)
variable (embedding : X ⟶ Ambient κ)

variable {i j : κ} (C : Chart a P33 σ embedding i) (D : Chart a P33 σ embedding j)
local notation "B" => (Poly κ i ⧸ C.I)
local notation "B'" => (Poly κ j ⧸ D.I)
local notation "R" => (B⊗[ℂ]B')
local notation "SR" => Spec (CommRingCat.of R)

def chartMorphism {k : κ} (V : Chart a P33 σ embedding k) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℂ (Poly κ k ⧸ V.I)))) ⟶ G :=
  Over.homMk V.j (chosen_chart_base a P33 σ embedding V)

def tensorToPair : SR ⟶ (G⊗G).left :=
  (pullbackSpecIso ℂ B B').inv≫
    ((chartMorphism a P33 σ embedding C) ⊗ₘ (chartMorphism a P33 σ embedding D)).left

def wholeMultiply : SR ⟶ X :=
  tensorToPair a P33 σ embedding C D ≫ (μ[G]).left

variable (r : Rows C.I) (s : Rows D.I)
local notation "p" => OriginalRetainedAffineChartPointEquiv318.evaluate a P33 σ embedding C r
local notation "q" => OriginalRetainedAffineChartPointEquiv318.evaluate a P33 σ embedding D s
local notation "test" => tensorPoint C.I D.I r s
local notation "m" => wholeMultiply a P33 σ embedding C D

/-- The projective chart-pair evaluation has exactly the installed
product pair on the true selected group, not one on a new model. -/
theorem actual_pair : test ≫ tensorToPair a P33 σ embedding C D = (lift p q).left := by
  apply pullback.hom_ext
  · change (test≫tensorToPair a P33 σ embedding C D)≫pullback.fst G.hom G.hom =
      (lift p q).left≫pullback.fst G.hom G.hom
    unfold tensorToPair
    rw [Category.assoc,Category.assoc,Over.tensorHom_left_fst,
      ←Category.assoc,←Category.assoc,projection_fst]
    change firstPoint C.I r≫C.j = _
    rw [←evaluate_left a P33 σ embedding C r]
    exact (congrArg Over.Hom.left (lift_fst p q)).symm
  · change (test≫tensorToPair a P33 σ embedding C D)≫pullback.snd G.hom G.hom =
      (lift p q).left≫pullback.snd G.hom G.hom
    unfold tensorToPair
    rw [Category.assoc,Category.assoc,Over.tensorHom_left_snd,
      ←Category.assoc,←Category.assoc,projection_snd]
    change secondPoint D.I s≫D.j = _
    rw [←evaluate_left a P33 σ embedding D s]
    exact (congrArg Over.Hom.left (lift_snd p q)).symm

theorem original_multiply_read : test ≫ m = (p*q).left := by
  unfold wholeMultiply
  rw [←Category.assoc,actual_pair]
  rfl

variable {k : κ} (V : Chart a P33 σ embedding k)
local notation "BV" => (Poly κ k ⧸ V.I)

/-- For the installed actual multiplication, produce ONE true
localization of the actual tensor ring. All coordinate functions
of the product are exact field evaluations on it. -/
theorem original_mul_localization
    (h : (p*q).left fieldClosedPoint ∈ Set.range V.j) :
    ∃ (w : R) (l : Spec (CommRingCat.of (Localization.Away w)) ⟶ Spec (CommRingCat.of BV)),
      pairRead C.I D.I r s w≠0 ∧ l≫V.j=localizationArrow w≫m := by
  letI : IsOpenImmersion V.j := V.openChart
  have at_map : (point (pairRead C.I D.I r s).toRingHom≫m) fieldClosedPoint ∈ Set.range V.j := by
    change (test≫m) fieldClosedPoint ∈ Set.range V.j
    rw [original_multiply_read]
    exact h
  exact actual_local_ring V.j m (pairRead C.I D.I r s).toRingHom at_map

end OriginalRetainedMultiplicationInTrueCharts318
