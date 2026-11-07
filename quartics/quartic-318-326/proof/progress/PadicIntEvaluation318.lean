module
public import CanonicalRoot318
public import Mathlib.RingTheory.PowerSeries.Substitution
public section
namespace PadicIntEvaluation318
noncomputable section
open scoped Topology
variable (p : ℕ) [Fact p.Prime]

/-- Closed norm balls in Zp are ideals because all scalars have norm at most one. -/
@[expose] noncomputable def ballIdeal (n : ℕ) : Ideal ℤ_[p] where
  carrier := {x | ‖x‖≤1/((n:ℝ)+1)}
  zero_mem' := by simp; positivity
  add_mem' hx hy := (PadicInt.nonarchimedean _ _).trans (max_le hx hy)
  smul_mem' c x hx := by
    change ‖c*x‖≤1/((n:ℝ)+1)
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg x) (PadicInt.norm_le_one c)).trans hx

instance linearTopology : IsLinearTopology ℤ_[p] ℤ_[p] := by
  apply IsLinearTopology.mk_of_hasBasis (R:=ℤ_[p]) (s:=ballIdeal p)
  convert (Metric.nhds_basis_closedBall_inv_nat_succ (x:=(0:ℤ_[p]))) using 1
  ext n x
  simp [ballIdeal,Metric.mem_closedBall,dist_zero_right]

theorem hasEval_of_norm_lt_one (x : ℤ_[p]) (hx : ‖x‖<1) : PowerSeries.HasEval x :=
  tendsto_pow_atTop_nhds_zero_of_norm_lt_one hx

/-- A discrete coefficient copy keeps the coefficient topology separate from
the genuine p-adic topology of the evaluation target. -/
@[expose] def Coeff := ℤ_[p]
instance coeffCommRing : CommRing (Coeff p) := inferInstanceAs (CommRing ℤ_[p])
instance coeffUniformSpace : UniformSpace (Coeff p) := ⊥
instance coeffDiscreteUniformity : DiscreteUniformity (Coeff p) := ⟨rfl⟩

@[expose] def coefficientMap : Coeff p →+* ℤ_[p] :=
  { toFun := fun x => x
    map_one' := rfl
    map_mul' := fun _ _ => rfl
    map_zero' := rfl
    map_add' := fun _ _ => rfl }

theorem coefficientMap_continuous : Continuous (coefficientMap p) := continuous_of_discreteTopology

/-- Evaluation is the actual convergent monomial sum, rather than a purely
formal symbol. -/
theorem evaluation_hasSum (f : PowerSeries (Coeff p)) (x : ℤ_[p]) (hx : ‖x‖<1) :
    HasSum (fun n => coefficientMap p (PowerSeries.coeff n f)*x^n)
      (PowerSeries.eval₂ (coefficientMap p) x f) :=
  PowerSeries.hasSum_eval₂ (coefficientMap_continuous p) (hasEval_of_norm_lt_one p x hx) f

instance coefficientAlgebra : Algebra (Coeff p) ℤ_[p] := (coefficientMap p).toAlgebra

theorem point_hasEval (x : Fin 2 → ℤ_[p]) (hx : ∀i,‖x i‖<1) : MvPowerSeries.HasEval x := by
  refine ⟨fun i => hasEval_of_norm_lt_one p (x i) (hx i),?_⟩
  simp

/-- A genuine evaluation/composition theorem over the actual complete p-adic
integer ring. No convergence or interchange premise is left to the caller. -/
theorem evaluation_subst (f : PowerSeries (Coeff p)) (g : MvPowerSeries (Fin 2) (Coeff p))
    (hg : MvPowerSeries.constantCoeff g=0) (x : Fin 2 → ℤ_[p]) (hx : ∀i,‖x i‖<1) :
    MvPowerSeries.eval₂ (coefficientMap p) x (f.subst g)=
      PowerSeries.eval₂ (coefficientMap p) (MvPowerSeries.eval₂ (coefficientMap p) x g) f := by
  have hs : PowerSeries.HasSubst g := .of_constantCoeff_zero hg
  have h := MvPowerSeries.eval₂_subst hs.const (point_hasEval p x hx) f
  exact h


theorem evaluation_subst_univariate (f g : PowerSeries (Coeff p))
    (hg : PowerSeries.constantCoeff g=0) (x : ℤ_[p]) (hx : ‖x‖<1) :
    PowerSeries.eval₂ (coefficientMap p) x (f.subst g)=
      PowerSeries.eval₂ (coefficientMap p) (PowerSeries.eval₂ (coefficientMap p) x g) f := by
  have hs : PowerSeries.HasSubst g := .of_constantCoeff_zero' hg
  have h := MvPowerSeries.eval₂_subst hs.const (PowerSeries.hasEval (hasEval_of_norm_lt_one p x hx)) f
  exact h

end
end PadicIntEvaluation318
#print axioms PadicIntEvaluation318.evaluation_hasSum

#print axioms PadicIntEvaluation318.evaluation_subst

#print axioms PadicIntEvaluation318.evaluation_subst_univariate
