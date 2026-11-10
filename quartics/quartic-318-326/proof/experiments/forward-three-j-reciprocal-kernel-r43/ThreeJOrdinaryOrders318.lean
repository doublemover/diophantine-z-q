module
public import ThreeJFiniteFlatRank318
public section
noncomputable section
open Filter Topology
namespace ThreeJOrdinaryOrders318
open ThreeCompactParameter318 ThreeJEllipticOrders318 ThreeJActualFiniteOrders318
set_option maxHeartbeats 1000000

lemma J_hasDerivAt {t : ℂ} (ht : t ≠ 0) :
    HasDerivAt J ((t+243)^2*D t/t^4) t := by
  have hn := ((hasDerivAt_id t).add_const (27:ℂ)).mul
    (((hasDerivAt_id t).add_const (243:ℂ)).pow 3)
  have h := hn.div ((hasDerivAt_id t).pow 3) (pow_ne_zero 3 ht)
  unfold J
  convert h using 1
  · rfl
  · dsimp [D]
    field_simp [ht]
    <;> ring

lemma J_derivative_nonzero {t : ℂ} (ht : t ≠ 0) (h243 : t ≠ -243) (hD : D t ≠ 0) :
    deriv J t ≠ 0 := by
  rw [(J_hasDerivAt ht).deriv]
  exact div_ne_zero (mul_ne_zero (pow_ne_zero 2 (by
    intro h; exact h243 (add_eq_zero_iff_eq_neg.mp h))) hD) (pow_ne_zero 4 ht)

/-- Every remaining finite point has local degree one for the centered
actual rational j function; no unlisted finite branch point remains. -/
theorem ordinary_order {t : ℂ} (ht : t ≠ 0) (h243 : t ≠ -243) (hD : D t ≠ 0) :
    meromorphicOrderAt (fun z => J z-J t) t=1 := by
  have ha : AnalyticAt ℂ (fun z => J z-J t) t := (J_analytic ht).sub analyticAt_const
  have hd : deriv (fun z => J z-J t) t ≠ 0 := by
    rw [((J_hasDerivAt ht).sub_const (J t)).deriv]
    rw [←(J_hasDerivAt ht).deriv]
    exact J_derivative_nonzero ht h243 hD
  rw [ha.meromorphicOrderAt_eq,
    ha.analyticOrderAt_eq_one_of_zero_deriv_ne_zero (sub_self _) hd]
  rfl

@[expose] def finiteOrder (t : ℂ) : ℕ := if t= -243 then 3 else if D t=0 then 2 else 1

/-- Exhaustive finite local degree, including the unramified point -27
over zero and every ordinary value, on the exact existing scheme map. -/
theorem actual_centered_order {t : ℂ} (ht : t ≠ 0) :
    meromorphicOrderAt (fun z => actualFiniteExpression z-J t) t=(finiteOrder t : ℤ) := by
  by_cases h243 : t= -243
  · subst t
    have hj : J (-243)=0 := by norm_num [J]
    simpa [hj,finiteOrder] using actual_order_neg243
  · by_cases hD : D t=0
    · have hj := (elliptic_fiber ht).mpr hD
      simpa [hj,finiteOrder,h243,hD] using actual_order_1728 hD
    · have he : (fun z => actualFiniteExpression z-J t) =ᶠ[𝓝 t] (fun z => J z-J t) := by
        filter_upwards [actualFiniteExpression_eq ht] with z hz
        rw [hz]
      rw [meromorphicOrderAt_congr (he.filter_mono nhdsWithin_le_nhds),ordinary_order ht h243 hD]
      norm_num [finiteOrder,h243,hD]

end ThreeJOrdinaryOrders318
