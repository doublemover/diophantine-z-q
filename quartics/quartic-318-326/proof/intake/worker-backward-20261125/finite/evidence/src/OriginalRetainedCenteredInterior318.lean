module

public import OriginalRetainedComplexAffineEquation318
public import OriginalRetainedProjectiveAffinePoints318
public import Mathlib.LinearAlgebra.Pi

@[expose] public section
noncomputable section

namespace OriginalRetainedCenteredInterior318

open OriginalRetainedComplexAffineEquation318 OriginalCenteredAnalyticEquation318
open scoped Topology BigOperators

variable {m : ℕ}
local notation "V" => (Fin 2 → ℂ)
local notation "W" => (Fin m → ℂ)
variable (p : Fin m → Polynomials m) (g : coordinateQuotient p)
variable (J : W ≃ₗ[ℂ] W)

/-- Direct finite coordinate proof; no complex manifold or inverse
function theorem object is needed. -/
theorem linear_on_true_columns_continuous (L : W →ₗ[ℂ] W) :
    Continuous L := by
  have column (v : W) : (∑ i : Fin m, v i • Pi.single i (1:ℂ))=v := by
    ext j
    simp [Pi.single_apply, Pi.smul_apply, smul_eq_mul]
  have same : (fun v : W => L v)=fun v => ∑ i : Fin m, v i • L (Pi.single i (1:ℂ)) := by
    funext v
    simp_rw [←map_smul]
    rw [←map_sum]
    exact congrArg L (column v).symm
  change Continuous (fun v => L v)
  rw [same]
  exact continuous_finsetSum _ (fun i _ => (continuous_apply i).smul continuous_const)

theorem residual_continuous : Continuous (fun z : V×W => residual p J z.1 z.2) := by
  have tuple : Continuous (fun z : V×W => Sum.elim z.1 z.2) := by
    apply continuous_pi
    rintro (i|i)
    · exact (continuous_apply i).comp continuous_fst
    · exact (continuous_apply i).comp continuous_snd
  have pcts : Continuous (fun z : V×W => fun i => eval z.1 z.2 (p i)) := by
    apply continuous_pi
    intro i
    have same : (fun z : V×W => eval z.1 z.2 (p i))=
        fun z : V×W => MvPolynomial.aeval (Sum.elim z.1 z.2) (p i) := by
      funext z
      change MvPolynomial.eval₂Hom (RingHom.id ℂ) _ (p i) =
        MvPolynomial.eval₂Hom (algebraMap ℂ ℂ) _ (p i)
      rw [Algebra.algebraMap_self]
    rw [same]
    exact (OriginalRetainedProjectiveAffinePoints318.eval_continuous (p i)).comp tuple
  exact continuous_snd.sub ((linear_on_true_columns_continuous J.symm.toLinearMap).comp pcts)

theorem centered_residual_zero (h : ∀ i, eval (0:V) (0:W) (p i)=0) :
    residual p J 0 0=0 := by
  have Hz : (fun i => eval (0:V) (0:W) (p i))=(0:W) := funext h
  rw [residual,Hz,map_zero,sub_zero]

/-- Choose ONE smaller radius over the previously verified original
contraction polydisc, with no supplied analytic branch. The returned
auxiliary coordinates agree with every literal zero on the old band. -/
theorem choose_centered_open_branch
    {r₀ ρ q : ℝ} (r₀pos : 0<r₀) (ρpos : 0<ρ) (qnonneg : 0≤q) (qsmall : q<1)
    (origin : ∀ i, eval (0:V) (0:W) (p i)=0)
    (lip_y : ∀ x, ‖x‖≤r₀ → ∀ u v, ‖u‖≤ρ → ‖v‖≤ρ →
      ‖residual p J x u-residual p J x v‖≤q*‖u-v‖)
    (G : Polynomials m) (hg : Ideal.Quotient.mk (relationsIdeal p) G=g)
    (unit : ∀ x u, ‖x‖≤r₀ → ‖u‖≤ρ → eval x u G≠0) :
    ∃ (r : ℝ) (_rpos : 0<r) (y : {x : V // ‖x‖<r}→W)
      (h : ∀ x, ∀ i, eval x.val (y x) (p i)=0),
      (∀ x, evalQ p (h x) g≠0) ∧
      (∀ x, ‖y x‖<ρ) ∧
      (∀ x u, ‖u‖<ρ → (∀ i, eval x.val u (p i)=0) → u=y x) ∧
      Continuous y ∧
      y ⟨0,by simpa only [norm_zero] using _rpos⟩=0 := by
  let R := residual p J
  have r0 : R 0 0=0 := centered_residual_zero p J origin
  have X : Continuous (fun x : V => ‖R x 0‖) :=
    ((residual_continuous p J).comp (continuous_id.prodMk continuous_const)).norm
  let N : Set V := {x | ‖R x 0‖<(1-q)*ρ}
  have Nopen : IsOpen N := isOpen_lt X continuous_const
  have inN : (0:V)∈N := by
    change ‖R 0 0‖<(1-q)*ρ
    rw [r0,norm_zero]
    exact mul_pos (sub_pos.2 qsmall) ρpos
  obtain ⟨d,dp,sub⟩ := Metric.mem_nhds_iff.1 (Nopen.mem_nhds inN)
  let r := min r₀ d/2
  have rpos : 0<r := div_pos (lt_min r₀pos dp) (by norm_num)
  have rlt : r<min r₀ d := by
    change min r₀ d/2<min r₀ d
    linarith only [lt_min r₀pos dp]
  have rle : r≤r₀ := le_trans rlt.le (min_le_left _ _)
  have small (x : V) (hx : ‖x‖≤r) : ‖R x 0‖<(1-q)*ρ :=
    sub (by
      rw [Metric.mem_ball,dist_zero_right]
      exact lt_of_le_of_lt hx (rlt.trans_le (min_le_right _ _)))
  have bound (x : V) (hx : ‖x‖≤r) : ‖R x 0‖≤(1-q)*ρ := (small x hx).le
  have contract (x : V) (hx : ‖x‖≤r) (u v : W)
      (hu : ‖u‖≤ρ) (hv : ‖v‖≤ρ) : ‖R x u-R x v‖≤q*‖u-v‖ :=
    lip_y x (hx.trans rle) u v hu hv
  obtain ⟨Y,Y_zero,onlyY⟩ := zeroChart R ρpos qnonneg qsmall bound contract
  let D := {x : V // ‖x‖<r}
  let y (x : D) := Y x.val
  have yfix (x : D) : y x=R x.val (y x) := sub_eq_zero.1 (Y_zero x.val x.property.le).2
  have ybound (x : D) : ‖y x‖≤ρ := (Y_zero x.val x.property.le).1
  have h (x : D) : ∀ i,eval x.val (y x) (p i)=0 :=
    residual_zero p J x.val (y x) (sub_eq_zero.2 (yfix x))
  refine ⟨r,rpos,y,h,?_,?_,?_,?_,?_⟩
  · intro x
    rw [←hg,evalQ,Ideal.Quotient.lift_mk]
    exact unit x.val (y x) (x.property.le.trans rle) (ybound x)
  · intro x
    have hs : ‖y x‖≤q*‖y x‖+‖R x.val 0‖ := by
      calc
        ‖y x‖ = ‖(R x.val (y x)-R x.val 0)+R x.val 0‖ := by
          rw [sub_add_cancel,←yfix x]
        _ ≤ _ := (norm_add_le _ _).trans (add_le_add_right
          (by simpa only [sub_zero] using contract x.val x.property.le (y x) 0
            (ybound x) (by simpa only [norm_zero] using ρpos.le)) _)
    apply (mul_lt_mul_left₀ (sub_pos.2 qsmall)).1
    rw [sub_mul,one_mul]
    linarith only [hs,small x.val x.property.le]
  · intro x u uinside ueq
    have z : (fun i => eval x.val u (p i))=(0:W) := funext ueq
    apply (onlyY x.val u x.property.le uinside.le).1
    change u-(u-J.symm (fun i => eval x.val u (p i)))=0
    rw [z,map_zero,sub_zero,sub_self]
  · apply Metric.continuous_iff.2
    intro b ε εpos
    let F (x : D) := R x.val (y b)
    have cF : Continuous F :=
      (residual_continuous p J).comp (continuous_subtype_val.prodMk continuous_const)
    obtain ⟨δ,δpos,near⟩ := Metric.continuous_iff.1 cF b ((1-q)*ε)
      (mul_pos (sub_pos.2 qsmall) εpos)
    refine ⟨δ,δpos,?_⟩
    intro x xb
    have hsum : ‖y x-y b‖≤q*‖y x-y b‖+‖F x-F b‖ := by
      calc
        ‖y x-y b‖ =
            ‖(R x.val (y x)-R x.val (y b))+(R x.val (y b)-R b.val (y b))‖ := by
              rw [sub_add_sub_cancel,←yfix x,←yfix b]
        _ ≤ _ := (norm_add_le _ _).trans (add_le_add_right
          (contract x.val x.property.le (y x) (y b) (ybound x) (ybound b)) _)
    have near' := near x xb
    rw [dist_eq_norm] at near' ⊢
    apply (mul_lt_mul_left₀ (sub_pos.2 qsmall)).1
    rw [sub_mul,one_mul]
    linarith only [hsum,near']
  · have hz : (0:V) ∈ {x : V | ‖x‖≤r} := by
      simpa only [Set.mem_setOf_eq,norm_zero] using rpos.le
    exact ((onlyY (0:V) 0 hz (by simpa only [norm_zero] using ρpos.le)).1
      (by rw [r0,sub_zero])).symm

end OriginalRetainedCenteredInterior318
