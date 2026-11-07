module
public import RawScalarOrientation318
public section
namespace RawGroupAnchor318
open CircuitReplay Raw318FinalReplay ConcreteG8Domain LocalGenerator318
open RawOddAnchorPoints318 WeierstrassCurve.Affine
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- The exact remaining inherited global group/squareclass assertion. This is
not proved here. It says that every square-abscissa point on the actual curve
is an integer multiple of the displayed generator, with either ordinate sign. -/
@[expose] def SquarePointGeneration : Prop :=
  ∀(h j:K)(hj:j^2=h^4-D),∃n:ℤ,
    n • P=Point.some (h^2) (h*j) (RootPointAlgebra318.square_point h j hj)

/-- All literal root point reconstruction is discharged. Only the explicit
inherited global group assertion remains to provide the integer labels. -/
theorem source_root_labels (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (hg : SquarePointGeneration) : ∃labels:Fin 4 → ℤ,RootLabels w labels := by
  have hex : ∀i:Fin 4,∃n:ℤ,∃(y:K)(h:E.Nonsingular ((RawAnchorNorm318.root w i)^2) y),
      n • P=Point.some _ y h := by
    intro i
    obtain ⟨j,hj,_⟩ := RawRootPoints318.all_root_factors S w source i
    obtain ⟨n,hn⟩ := hg _ j hj
    exact ⟨n,_,_,hn⟩
  choose labels hlabels using hex
  exact ⟨labels,hlabels⟩

/-- Source-specific closure of the entire 2/3-adic anchor and signed scalar
block, conditional only on the actual global square-point generator theorem. -/
theorem source_anchor_from_group_generation (w : Assignment)
    (source : Constraints (stage0 ((3:ℚ)^65536)) w) (hg : SquarePointGeneration) :
    ∃(labels:Fin 4 → ℤ)(c:ℤ),RootLabels w labels ∧ ScalarLabel w c ∧
      (∀i,Odd (labels i)) ∧ (c=labels 1-1 ∨ c= -labels 1-1) ∧
      (2*3^32767:ℤ)∣c ∧ (2:ℝ)^49151<(c.natAbs:ℝ) := by
  obtain ⟨labels,hlabels⟩ := source_root_labels _ w source hg
  obtain ⟨hodd,c,hscalar,horient,hdiv,hbound⟩ :=
    RawScalarOrientation318.source_anchor_from_root_labels w source labels hlabels
  exact ⟨labels,c,hlabels,hscalar,hodd,horient,hdiv,hbound⟩

end RawGroupAnchor318
