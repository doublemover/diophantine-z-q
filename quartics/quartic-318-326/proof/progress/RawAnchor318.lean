module
public import Raw318FinalReplayData
public import SemilocalAnchor318
public import ScalarAnchorBound318
public section
namespace RawAnchor318
open CircuitReplay Raw318FinalReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem anchor_row (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    (w 55)^2+6*(w 56)^2-2*(w 57)^2-
      3*(w 308+4096*S*w 145)^2+2*S^2=0 := by
  have hh : r287 S w=0 := source _
    (List.getElem_mem (l:=stage0 S) (n:=287)
      (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r287] at hh
  linear_combination hh

/-- Exact raw-source anchor soundness; no elliptic or geometric hypothesis. -/
theorem source_semilocal_anchor (S : ℚ) (w : Assignment)
    (source : Constraints (stage0 S) w) (hS : S≠0) :
    0≤padicValRat 2 ((w 308+4096*S*w 145)/S) ∧
    0≤padicValRat 3 ((w 308+4096*S*w 145)/S) :=
  SemilocalAnchor318.scaled_anchor_sound (w 55) (w 56) (w 57)
    (w 308+4096*S*w 145) S hS (anchor_row S w source)

/-- Remaining oddness inputs are now the exact elliptic norm-valuation facts,
not a generic assumed semilocal membership or odd-label certificate. -/
theorem source_odd_labels (S : ℚ) (w : Assignment)
    (source : Constraints (stage0 S) w) (hS : S≠0) (labels : Fin 4 → ℤ)
    (hn : ∀i,labels i≠0) (hbase : 0≤padicValRat 2 (w 308/S))
    (hnorm : padicValRat 2 (4096*w 145)=
      -2*(∑i,(padicValInt 2 (labels i):ℤ))) : ∀i,Odd (labels i) :=
  SemilocalAnchor318.affine_anchor_forces_odd_labels (w 55) (w 56) (w 57)
    (w 308) (w 145) S labels hS hn hbase hnorm (anchor_row S w source)

theorem source_scalar_three (S : ℚ) (w : Assignment)
    (source : Constraints (stage0 S) w) (hS : S≠0)
    (hN : 0≤padicValRat 3 (4096*w 145)) : 0≤padicValRat 3 (w 308/S) :=
  SemilocalAnchor318.affine_anchor_scalar_three (w 55) (w 56) (w 57)
    (w 308) (w 145) S hS hN (anchor_row S w source)


/-- The raw anchor with the final literal S supplies the scalar index bound
once its remaining elliptic 3-adic norm and odd-root norm facts are given. -/
theorem source_scalar_index_bound (w : Assignment)
    (source : Constraints (stage0 ((3:ℚ)^65536)) w)
    (c : ℤ) (hc : c≠0) (heven : Even c) (hnR : w 308≠0)
    (hval : padicValRat 3 (w 308)=2+2*(padicValInt 3 c:ℤ))
    (hN : 0≤padicValRat 3 (4096*w 145)) :
    (2*3^32767:ℤ)∣c ∧ (2:ℝ)^49151<(c.natAbs:ℝ) := by
  apply ScalarAnchorBound318.index_bound c (w 308) hc heven hnR hval
  exact source_scalar_three _ w source (by positivity) hN

/-- Oddness now needs only the concrete elliptic valuation formulas and the
nonidentity labels; conic soundness and scalar-integrality are proved here. -/
theorem source_odd_labels_from_norm_values (w : Assignment)
    (source : Constraints (stage0 ((3:ℚ)^65536)) w)
    (labels : Fin 4 → ℤ) (hn : ∀i,labels i≠0) (c : ℤ) (hnR : w 308≠0)
    (hbaseval : padicValRat 2 (w 308)=3+2*(padicValInt 2 c:ℤ))
    (hnorm : padicValRat 2 (4096*w 145)=
      -2*(∑i,(padicValInt 2 (labels i):ℤ))) : ∀i,Odd (labels i) := by
  apply source_odd_labels _ w source (by positivity) labels hn
  · exact ScalarAnchorBound318.scalar_summand_two_integral c (w 308) hnR hbaseval
  · exact hnorm

end RawAnchor318
