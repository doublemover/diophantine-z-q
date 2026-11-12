module
public import SelectedQuotientOrders318
public import GlobalReductionCounts318
public section
noncomputable section
namespace SelectedGlobalCoordinateDenominators318
open ConcreteG8Domain
@[expose] def denominator (x : K) : ℕ := x.re.den*x.im.den
lemma positive (x : K) : 0<denominator x := Nat.mul_pos x.re.den_pos x.im.den_pos
variable (p : ℕ) [Fact p.Prime]
/-- A single global rational-coordinate denominator controls BOTH embeddings. -/
lemma embedded_integral (rho : ℚ_[p]) (hr : rho^2=2) (x : K)
    (hd : ¬p∣denominator x) : ‖ConcretePadic318.embedding p rho hr x‖≤1 := by
  have ha : ¬p∣x.re.den := fun h => hd (h.trans (dvd_mul_right _ _))
  have hb : ¬p∣x.im.den := fun h => hd (h.trans (dvd_mul_left _ _))
  have hx : x=pair x.re x.im := by cases x; rfl
  rw [hx,ConcretePadic318.embedding_pair]
  apply (Padic.nonarchimedean _ _).trans
  apply max_le
  · exact Padic.norm_rat_le_one ha
  · rw [norm_mul]
    exact mul_le_one₀ (Padic.norm_rat_le_one hb) (norm_nonneg _)
      (ActualSplitOrbitEntry318.root_integral p rho hr)
end SelectedGlobalCoordinateDenominators318
