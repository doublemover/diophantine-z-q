module
public import KummerGroup318
public import RawRootPoints318
public import RawScalarKummer318
public import RawAnchorPoints318
public section
namespace RawScalarOrientation318
open CircuitReplay Raw318FinalReplay ConcreteG8Domain LocalGenerator318
open RawOddAnchorPoints318 WeierstrassCurve.Affine
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- The scalar label and its signed orientation are obtained from the literal
Kummer row and the S-root label. No separate scalar group-label premise remains. -/
theorem scalar_label_from_root_labels (S : ℚ) (w : Assignment)
    (source : Constraints (stage0 S) w) (labels : Fin 4 → ℤ)
    (hlabels : RootLabels w labels) :
    ∃c:ℤ,ScalarLabel w c ∧ (c=labels 1-1 ∨ c= -labels 1-1) := by
  have hroot : RawAnchorNorm318.root w 1≠0 := (RawRootPoints318.root1_point S w source).1
  obtain ⟨y,hns,hpt⟩ := hlabels 1
  obtain ⟨j,hj,hy⟩ := RootPointAlgebra318.factor_of_square_point _ y hroot hns
  have hcanonical : labels 1 • P=Point.some ((RawAnchorNorm318.root w 1)^2)
      (RawAnchorNorm318.root w 1*j) (RootPointAlgebra318.square_point _ j hj) := by
    simpa only [hy] using hpt
  obtain ⟨c,yr,hr,hc,horient⟩ := KummerGroup318.scalar_orientation (labels 1)
    (RawAnchorNorm318.root w 1) j (RawAnchorNorm318.scalarRoot w) hj hcanonical
    (RawScalarKummer318.scalar_kummer S w source)
  exact ⟨c,⟨yr,hr,hc⟩,horient⟩

/-- Complete source anchor arithmetic from the four genuine root point labels.
The scalar reconstruction, Kummer exceptional branch, local valuation formulas,
parity, and final exact index divisibility are all discharged. -/
theorem source_anchor_from_root_labels (w : Assignment)
    (source : Constraints (stage0 ((3:ℚ)^65536)) w)
    (labels : Fin 4 → ℤ) (hlabels : RootLabels w labels) :
    (∀i,Odd (labels i)) ∧ ∃c:ℤ,ScalarLabel w c ∧
      (c=labels 1-1 ∨ c= -labels 1-1) ∧
      (2*3^32767:ℤ)∣c ∧ (2:ℝ)^49151<(c.natAbs:ℝ) := by
  obtain ⟨c,hc,horient⟩ := scalar_label_from_root_labels _ w source labels hlabels
  obtain ⟨hodd,hdiv,hbound⟩ := RawAnchorPoints318.source_anchor_from_points w source labels c
    hlabels hc horient
  exact ⟨hodd,c,hc,horient,hdiv,hbound⟩

end RawScalarOrientation318
