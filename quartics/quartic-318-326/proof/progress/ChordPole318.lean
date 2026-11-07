module
public import ChordContinuation318
public section
noncomputable section
open Filter Set
open scoped Topology
namespace ChordPole318
open ChordAlgebra318 ChordFlow318 ChordContinuation318
set_option maxHeartbeats 0

/-- The actual chord x-coordinate has a double pole at the inverse point when its ordinate is nonzero. -/
theorem R_order_inverse (L : PeriodPair) (w : ℂ) (hw : w ∉ L.lattice)
    (hb : L.derivWeierstrassP w ≠ 0) :
    meromorphicOrderAt (R L (L.weierstrassP w) (L.derivWeierstrassP w)) (-w) = -2 := by
  have hnw : -w ∉ L.lattice := fun h => hw (neg_mem_iff.mp h)
  let N : ℂ → ℂ := fun z => L.derivWeierstrassP z-L.derivWeierstrassP w
  let D : ℂ → ℂ := fun z => L.weierstrassP z-L.weierstrassP w
  have hn : AnalyticAt ℂ N (-w) := (L.analyticOnNhd_derivWeierstrassP (-w) hnw).sub analyticAt_const
  have hd : AnalyticAt ℂ D (-w) := (L.analyticOnNhd_weierstrassP (-w) hnw).sub analyticAt_const
  have hn0 : N (-w)≠0 := by
    dsimp [N]
    rw [L.derivWeierstrassP_neg]
    intro he
    apply hb
    linear_combination -he/2
  have hD0 : D (-w)=0 := by simp [D]
  have hD1 : deriv D (-w)≠0 := by
    dsimp [D]
    simpa only [deriv_sub_const,L.deriv_weierstrassP,L.derivWeierstrassP_neg,neg_ne_zero] using hb
  have hno : meromorphicOrderAt N (-w)=0 := by
    rw [hn.meromorphicOrderAt_eq,hn.analyticOrderAt_eq_zero.mpr hn0]
    rfl
  have hdo : meromorphicOrderAt D (-w)=1 := by
    rw [hd.meromorphicOrderAt_eq,hd.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hD0 hD1]
    rfl
  let M : ℂ → ℂ := fun z => ChordAlgebra318.slope (L.weierstrassP w) (L.derivWeierstrassP w)
    (L.weierstrassP z) (L.derivWeierstrassP z)
  have hm : MeromorphicAt M (-w) := hn.meromorphicAt.div hd.meromorphicAt
  have hmo : meromorphicOrderAt M (-w)= -1 := by
    change meromorphicOrderAt (N/D) (-w)= -1
    rw [meromorphicOrderAt_div hn.meromorphicAt hd.meromorphicAt,hno,hdo]
    norm_num
  let F : ℂ → ℂ := fun z => (M z)^2/4
  let G : ℂ → ℂ := fun z => -L.weierstrassP z-L.weierstrassP w
  have hfo : meromorphicOrderAt F (-w)= -2 := by
    have he : F=(1/4:ℂ) • (M^2) := by funext z; dsimp [F]; ring
    rw [he,meromorphicOrderAt_const_smul_eq_meromorphicOrderAt (by norm_num : (1/4:ℂ)≠0),
      meromorphicOrderAt_pow hm,hmo]
    rfl
  have hg : AnalyticAt ℂ G (-w) := (L.analyticOnNhd_weierstrassP (-w) hnw).neg.sub analyticAt_const
  have hfg : R L (L.weierstrassP w) (L.derivWeierstrassP w)=F+G := by
    funext z
    dsimp [R,chordX,F,G,M]
    ring
  rw [hfg,meromorphicOrderAt_add_eq_left_of_lt hg.meromorphicAt,hfo]
  rw [hfo]
  exact lt_of_lt_of_le (by decide : (-2:WithTop ℤ)<0) hg.meromorphicOrderAt_nonneg

end ChordPole318
