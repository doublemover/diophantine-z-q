module
public import ActualTZLiteralPairSeparation318
import all ActualTZLiteralProbeSpecialization318
import all ActualTZJointPolynomialForms318
import all ActualTZTwoBlockCoefficients318
public section
noncomputable section
namespace ActualTZLiteralNonlinearDistinct318
open ActualTZLiteralTerminalLift318 ActualTZJointPolynomialForms318 ActualTZTwoBlockCoefficients318
open ActualTZFixedWrapMarkers318 ActualTZLiteralProbeSpecialization318 ActualTZLiteralPairSeparation318
open ActualTZMomentCoefficientMarkers318
open scoped BigOperators

variable {m a b j W : ℕ} {S : Terminal m a b}

private theorem linear_basis (Q : Quadratic m) (i : Fin m) (x : ℤ) :
    (∑ l : Fin m,Q.linear l*basis i x l)=Q.linear i*x := by
  rw [Finset.sum_eq_single i]
  · rw [basis_self]
  · intro l _ hl
    rw [basis_other hl,mul_zero]
  · intro h
    exact (h (Finset.mem_univ i)).elim

private theorem bilinear_basis (Q : Quadratic m) (i l : Fin m) (x y : ℤ) :
    bilinear Q (basis i x) (basis l y)=qCoeff Q i l*x*y := by
  unfold bilinear
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single l,basis_self,basis_self]
    · intro k _ hk
      rw [basis_other hk,mul_zero]
    · intro h
      exact (h (Finset.mem_univ l)).elim
  · intro k _ hk
    simp only [basis_other hk,mul_zero,zero_mul,Finset.sum_const_zero]
  · intro h
    exact (h (Finset.mem_univ i)).elim

private theorem eval_basis (Q : Quadratic m) (i : Fin m) (x : ℤ) :
    eval Q (basis i x)=Q.constTerm+Q.linear i*x+qCoeff Q i i*x*x := by
  rw [eval,linear_basis,bilinear_basis]

private theorem eval_two_basis (Q : Quadratic m) (i l : Fin m) (x y : ℤ) :
    eval Q (basis i x+basis l y)=Q.constTerm+Q.linear i*x+Q.linear l*y+
      qCoeff Q i i*x*x+qCoeff Q i l*x*y+qCoeff Q l i*y*x+qCoeff Q l l*y*y := by
  rw [eval,bilinear_add_left,bilinear_add_right,bilinear_add_right]
  simp only [Pi.add_apply,mul_add,Finset.sum_add_distrib,linear_basis,bilinear_basis]
  ring

private theorem fine_const_separates (c : Fin j) (i i' : Fin b) (ω ω' : Bits a)
    (H : FineDiff (S.nonlinearConst i) (S.nonlinearConst i')) :
    Varies (siteP S (.nonlinear c i ω)-siteP S (.nonlinear c i' ω')) := by
  rcases H with ⟨l,hl⟩|⟨l,t,ht⟩
  · refine of_pair_values S (.nonlinear c i ω) (.nonlinear c i' ω')
      (basis l 1) (basis l (-1)) (fun _ _=>0) (fun _ _=>0) (fun _=>0) (fun _=>0) ?_
    simp only [eOffset,mul_zero,Finset.sum_const_zero,add_zero,sub_zero,
      zero_pow (by decide : (2:ℕ)≠0),zero_add,eval_basis]
    intro h
    apply hl
    linarith
  · by_cases hlt : l=t
    · subst t
      refine of_mixed S (.nonlinear c i ω) (.nonlinear c i' ω')
        (fun x y=>basis l (x+y)) (fun _ _ _ _=>0) (fun _ _ _=>0)
        (2*(qCoeff (S.nonlinearConst i) l l-qCoeff (S.nonlinearConst i') l l))
        (mul_ne_zero (by norm_num) (sub_ne_zero.mpr ht)) ?_
      simp only [mixedProbe,eOffset,mul_zero,Finset.sum_const_zero,add_zero,sub_zero,
        zero_pow (by decide : (2:ℕ)≠0),zero_add,eval_basis] <;> ring
    · have hLe : l≤t := by
        by_contra h
        apply ht
        simp only [qCoeff,if_neg h]
      have hOpp : ¬ t≤l := not_le.mpr (lt_of_le_of_ne hLe hlt)
      have ho₁ : qCoeff (S.nonlinearConst i) t l=0 := by simp only [qCoeff,if_neg hOpp]
      have ho₂ : qCoeff (S.nonlinearConst i') t l=0 := by simp only [qCoeff,if_neg hOpp]
      refine of_mixed S (.nonlinear c i ω) (.nonlinear c i' ω')
        (fun x y=>basis l x+basis t y) (fun _ _ _ _=>0) (fun _ _ _=>0)
        (qCoeff (S.nonlinearConst i) l t-qCoeff (S.nonlinearConst i') l t)
        (sub_ne_zero.mpr ht) ?_
      simp only [mixedProbe,eOffset,mul_zero,Finset.sum_const_zero,add_zero,sub_zero,
        zero_pow (by decide : (2:ℕ)≠0),zero_add,eval_two_basis,ho₁,ho₂] <;> ring

/-- Case 4, distinct nonlinear nodes on the same actual copy.
The fourth alternative reads a genuine upper triangle coefficient
with no artificial antisymmetric or double-counted offdiag term. -/
theorem nonlinear_same_copy_distinct (G : GoodTerminal S W) (c : Fin j)
    (i i' : Fin b) (hi : i≠i') (ω ω' : Bits a) :
    Varies (siteP S (.nonlinear c i ω)-siteP S (.nonlinear c i' ω')) := by
  rcases G.nonlinearDistinct i i' hi with hQ|h0|⟨l,hl⟩|hF
  · refine of_coarse_quadratic S (.nonlinear c i ω) (.nonlinear c i' ω') c
      (S.quadratic i-S.quadratic i') (sub_ne_zero.mpr hQ) ?_
    simp only [quadraticProbe,eOffset,basis_self,nonlinearSlope_zero,mul_zero,
      Finset.sum_const_zero,add_zero,sub_zero] <;> ring
  · by_cases hQ : S.quadratic i=S.quadratic i'
    · refine of_pair_values S (.nonlinear c i ω) (.nonlinear c i' ω')
        (fun _=>0) (fun _=>0) (fun _ _=>0) (fun _ _=>0) (basis c 1) (basis c 0) ?_
      simp only [eOffset,basis_self,nonlinearSlope_zero,mul_zero,Finset.sum_const_zero,
        add_zero,sub_zero, hQ]
      intro h
      apply h0
      linarith
    · refine of_coarse_quadratic S (.nonlinear c i ω) (.nonlinear c i' ω') c
        (S.quadratic i-S.quadratic i') (sub_ne_zero.mpr hQ) ?_
      simp only [quadraticProbe,eOffset,basis_self,nonlinearSlope_zero,mul_zero,
        Finset.sum_const_zero,add_zero,sub_zero] <;> ring
  · refine of_mixed S (.nonlinear c i ω) (.nonlinear c i' ω')
      (fun x _=>basis l x) (fun _ _ _ _=>0) (fun _ y=>basis c y)
      (S.nonlinearSlopeCoeff i l-S.nonlinearSlopeCoeff i' l) (sub_ne_zero.mpr hl) ?_
    simp only [mixedProbe,eOffset,basis_self,nonlinearSlope_basis,mul_zero,
      Finset.sum_const_zero,add_zero,sub_zero] <;> ring
  · exact fine_const_separates c i i' ω ω' hF

/-- All six incomparable physical pair cases, with the same exact
source nodes. Filters may remove entries, but do not reindex the
own axis of a linear face or identify the coarse copies. -/
theorem different_sites (G : GoodTerminal S W) (u v : Site a b j) (h : u≠v) :
    Varies (siteP S u-siteP S v) := by
  cases u with
  | marked ω =>
      cases v with
      | marked ω' =>
          exact marked_marked G ω ω' (fun e=>h (congrArg Site.marked e))
      | linear c i ω' => exact flip _ _ (linear_marked G c i ω' ω)
      | nonlinear c i ω' => exact flip _ _ (nonlinear_marked G c i ω' ω)
  | linear c i ω =>
      cases v with
      | marked ω' => exact linear_marked G c i ω ω'
      | nonlinear d i' ω' => exact flip _ _ (nonlinear_linear G d c i' i ω' ω)
      | linear d i' ω' =>
          by_cases hc : c=d
          · subst d
            by_cases hi : i=i'
            · subst i'
              exact linear_corner G c i ω ω' (fun e=>h (congrArg (Site.linear c i) e))
            · exact linear_same_copy_distinct G c i i' hi ω ω'
          · exact linear_different_copy G c d hc i i' ω ω'
  | nonlinear c i ω =>
      cases v with
      | marked ω' => exact nonlinear_marked G c i ω ω'
      | linear d i' ω' => exact nonlinear_linear G c d i i' ω ω'
      | nonlinear d i' ω' =>
          by_cases hc : c=d
          · subst d
            by_cases hi : i=i'
            · subst i'
              exact nonlinear_corner G c i ω ω' (fun e=>h (congrArg (Site.nonlinear c i) e))
            · exact nonlinear_same_copy_distinct G c i i' hi ω ω'
          · exact nonlinear_different_copy G c d hc i i' ω ω'

theorem literal_marker (G : GoodTerminal S W) (hW : 0<W)
    (u v : Site a b j) (h : u≠v) :
    ∃ z : Axis m a j→₀ℕ,∃ κ : ℤ,z≠0 ∧ κ≠0 ∧
      ∀ n (r r' : ℤ),(physicalP S W n r r' u v).coeff z=κ :=
  fixed_wrap_marker S W hW u v (different_sites G u v h)

end ActualTZLiteralNonlinearDistinct318
