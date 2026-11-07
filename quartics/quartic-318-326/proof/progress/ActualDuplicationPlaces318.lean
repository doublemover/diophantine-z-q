module
public import DuplicationFiniteAbs318
public section
namespace ActualDuplicationPlaces318
open ConcreteG8Domain LocalGenerator318 NumberField RelativeDuplicationHeight318
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Integrality of the two coefficient constants at every actual normalized
finite place, proved directly from i²=2 rather than a place classification. -/
theorem finite_coefficients (w:FinitePlace K) : w D≤1 ∧ w (2:K)≤1 := by
  have hn : IsNonarchimedean (w ·) := FinitePlace.add_le w
  have h2:w (2:K)≤1 := hn.apply_natCast_le_one (map_zero_le w 1) (map_one w)
  have h3:w (3:K)≤1 := hn.apply_natCast_le_one (map_zero_le w 1) (map_one w)
  have hi:w i≤1 := by
    have hh := congrArg (fun x:K => w x) i_square
    rw [map_pow] at hh
    nlinarith [apply_nonneg w i]
  have hdel:w (3-i)≤1 := by
    have hh := (hn (3:K) (-i)).trans (max_le h3 (by simpa only [map_neg_eq_map] using hi))
    simpa only [sub_eq_add_neg] using hh
  refine ⟨?_,h2⟩
  rw [D,map_pow]
  simpa using (sq_le_sq₀ (apply_nonneg w _) (by norm_num)).mpr hdel

/-- Exact pointwise nonarchimedean duplication bounds at the actual finite
places used in Mathlib's global number-field height product. -/
theorem finite_duplication_bounds (w:FinitePlace K) (a b:K) :
    w (2:K)^3*w D^2*(max (w a) (w b))^4≤
      max (w ((a^2+D*b^2)^2)) (w (4*a*b*(a^2-D*b^2))) ∧
    max (w ((a^2+D*b^2)^2)) (w (4*a*b*(a^2-D*b^2)))≤(max (w a) (w b))^4 := by
  have hh := DuplicationFiniteAbs318.absolute_duplication_bounds w.val (FinitePlace.add_le w)
    a b D (finite_coefficients w).1 (finite_coefficients w).2
  exact hh

end ActualDuplicationPlaces318
