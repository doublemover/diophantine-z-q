module
public import PolynomialHeightInterface318
public import GlobalSaturationLogic318
public section
namespace GlobalSaturation318
open ConcreteG8Domain LocalGenerator318 GlobalGeneratorPoints318
open GlobalSaturationHeight318 FiniteGeneratorEnumeration318 WeierstrassCurve.Affine
open CircuitReplay Raw318FinalReplay RawOddAnchorPoints318
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section

/-- The precise small absolute-height to coefficient-box conversion still
needed from the global height theory. The finite search is proved separately. -/
abbrev SmallHeightCoverage := PolynomialHeightInterface318.PolynomialHeightCoverage

theorem small_height_classified (coverage:SmallHeightCoverage) :
    GlobalSaturationLogic318.SmallHeightClassified := by
  intro Q hq
  rcases PolynomialHeightInterface318.small_height_candidates coverage Q hq with rfl|hc
  · left; simp
  · exact candidate_classified Q hc

/-- Actual global square-point generation, after discharging the entire
finite enumeration and all elliptic arithmetic identities. The four global
inputs remain explicit: canonical data, coefficient
height coverage, odd rank-one descent, and dual square-abscissa arithmetic. -/
theorem square_point_generation {H:E.Point→ℝ} (d:CanonicalData H)
    (coverage:SmallHeightCoverage) (rank:GlobalSaturationLogic318.OddRankOneData)
    (dual:GlobalSquareHalving318.DualSquareAbscissa) : RawGroupAnchor318.SquarePointGeneration :=
  GlobalSaturationLogic318.square_point_generation d (small_height_classified coverage) rank dual

/-- Literal final source to odd labels and enormous nonzero scalar index,
conditional on the precise remaining global descent/height facts. No local
norm formula, Kummer orientation, or bounded-search premise remains. -/
theorem source_anchor_from_global_interfaces (w:Assignment)
    (source:Constraints (stage0 ((3:ℚ)^65536)) w)
    {H:E.Point→ℝ} (d:CanonicalData H)
    (coverage:SmallHeightCoverage) (rank:GlobalSaturationLogic318.OddRankOneData)
    (dual:GlobalSquareHalving318.DualSquareAbscissa) :
    ∃(labels:Fin 4→ℤ)(c:ℤ),RootLabels w labels ∧ ScalarLabel w c ∧
      (∀i,Odd (labels i)) ∧ (c=labels 1-1 ∨ c= -labels 1-1) ∧
      (2*3^32767:ℤ)∣c ∧ (2:ℝ)^49151<(c.natAbs:ℝ) :=
  RawGroupAnchor318.source_anchor_from_group_generation w source
    (square_point_generation d coverage rank dual)

end
end GlobalSaturation318
