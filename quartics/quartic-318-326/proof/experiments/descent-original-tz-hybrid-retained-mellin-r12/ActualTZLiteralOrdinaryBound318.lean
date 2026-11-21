module
public import ActualTZLiteralOrdinaryCorrection318
public import ActualTZOrdinaryReferenceCut318
public import ActualTZOrdinaryMomentUniformIndex318
import all ActualTZFiniteMainBand318
import all ActualTZSharedXDivisorCell318
import all ActualTZSharedXDivisorAverage318
public section
noncomputable section
universe u
namespace ActualTZLiteralOrdinaryBound318
open MeasureTheory
open scoped BigOperators Topology
open ActualTZLiteralPhysicalWrapCarrier318 ActualTZSharedXDivisorAverage318 ActualTZPhysicalUnitMass318
open ActualTZSharedXDivisorCell318 ActualTZLiteralOrdinaryCorrection318
open ActualTZOrdinaryReferenceCut318 ActualTZOrdinaryMomentUniformIndex318
open ActualTZLiteralSchwartz318 ActualTZAngularKernelMain318 ActualTZAngularTensorTail318
open ActualTZLiteralLowIntegral318 ActualTZFiniteMainBand318 ActualTZLiteralMellinTensor318

variable {m a b j : ℕ} {I : Type u} [Fintype I] [DecidableEq I]

@[expose] def α (W : ℕ) : ℝ := (Nat.totient W:ℝ)/(W:ℝ)

theorem α_bounds (W : ℕ) (hW : 0<W) : 0≤α W ∧ α W≤1 := by
  have hWp : (0:ℝ)<W := by exact_mod_cast hW
  exact ⟨div_nonneg (by positivity) hWp.le,
    (div_le_one hWp).2 (by exact_mod_cast Nat.totient_le W)⟩

/-- The terminal error on the literal original old shared-x
ordinary moment. The threshold is fixed at (χ,W,η) before the
physical grid, signs, wraps, or its growing finite index. The
collision cost is the genuine finite weighted prefix bound. -/
theorem literal_bound (C : Cutoff) (hχ : (∫ u in (0:ℝ)..1,|deriv C.χ u|^2)=1)
    (B : ℝ) (hB : ∀ t,|C.χ t|≤B) (y : ℕ) (η : ℝ) (hη : 0<η) :
    ∃ L₀≥(1:ℝ),∀ {S : ActualTZJointPolynomialForms318.Terminal m a b}
      (X : Context S I),X.y=y→∀ R>1,L₀≤Real.log R→
      ∀ K : ℕ,
      (∀ p,¬p∣K→∀ r q,ActualTZIntegerGridMarker318.reduced (p:=p) (X.pairPol r q)≠0)→
      ∃ P : ℕ,Real.exp ((Real.log R)^2)≤(P:ℝ) ∧
        (primorial y).primeFactors⊆Nat.primesBelow (P+1) ∧ ⌊R⌋₊<P+1 ∧
        |original X (α (primorial y)) R C.χ-1|≤
          (Real.log R*(2*R*B)^2)^Fintype.card I*lostBound X+
          intervalError X (α (primorial y)) R B+
          (2*(∫ ξ,‖mainDensity C ξ‖ ∂μ I))*correctionBudget X (P+1) K+η+lostBound X := by
  obtain ⟨L₀,h0,hAccept⟩ := accepts_uniform (I:=I) C (primorial y)
    (primorial_pos y) hχ η hη
  refine ⟨L₀,h0,?_⟩
  intro S X hY R hR hL K hK
  rw [←hY] at hAccept ⊢
  let W := primorial X.y
  have hW : 0<W := primorial_pos _
  obtain ⟨P,hP,hWheel,hCut⟩ := reference_exists W hW R
  refine ⟨P,hP,hWheel,hCut,?_⟩
  let J := X.OldGrid×X.Keys
  let w : J→ℝ := fun zr=>mass X zr.1*X.theta zr.1 zr.2
  have hw (zr : J) : 0≤w zr :=
    mul_nonneg (by unfold mass; positivity) (X.theta_bounds zr.1 zr.2).1
  have hUnit : (∑ zr : J,w zr)≤1 := by
    change (∑ zr : X.OldGrid×X.Keys,mass X zr.1*X.theta zr.1 zr.2)≤1
    rw [flatten_one X]
    exact X.mass_total_le
  have hBig :
      |∑ zr : J,w zr*(exactMain C W (X.wrapped zr.1 zr.2) X.base R-1)|≤
        (2*(∫ ξ,‖mainDensity C ξ‖ ∂μ I))*correctionBudget X (P+1) K+η :=
    hAccept R hR hL P hP hWheel hCut J (fun zr=>X.wrapped zr.1 zr.2) (fun _=>X.base)
      (fun _ i=>(X.base_unit i).2.2) w hw hUnit _ (budget_nonneg X P K hK)
      (fun ξ _=>exact_angular X P K hK (Real.log R) (Real.log_pos hR) ξ)
  have hMain : |gridMain X (α W) R C.χ-retainedMass X|≤_ := by
    have he : (∑ zr : J,w zr*(exactMain C W (X.wrapped zr.1 zr.2) X.base R-1))=
        gridMain X (α W) R C.χ-retainedMass X := by
      change (∑ zr : X.OldGrid×X.Keys,(mass X zr.1*X.theta zr.1 zr.2)*
        (exactMain C W (X.wrapped zr.1 zr.2) X.base R-1))=_
      rw [flatten X]
      simp only [avg,gridMain,retainedMass,ActualTZSharedXDivisorCell318.mainCell,exactMain,
        α,W,mul_sub,mul_one,Finset.sum_sub_distrib]
    rw [he] at hBig
    exact hBig
  have hUp (t : ℝ) (ht : 1<t) : C.χ t=0 := C.support t (ht.trans_le (le_abs_self _))
  have hα := α_bounds W hW
  have hBdry := exact_boundary_error X (α W) R C.χ hR hα.1 hα.2 hUp B hB
  have hInt := exact_interval_error X (α W) R C.χ hR hUp B hB
  have hDef := defect_le X
  let A := original X (α W) R C.χ
  let D := clipped X (α W) R C.χ
  let M := gridMain X (α W) R C.χ
  let T := retainedMass X
  have hTel : A-1=(A-D)+(D-M)+(M-T)+(T-1) := by ring
  change |A-1|≤_
  rw [hTel]
  nlinarith only [abs_add_le (A-D) (D-M),abs_add_le ((A-D)+(D-M)) (M-T),
    abs_add_le ((A-D)+(D-M)+(M-T)) (T-1),hBdry,hInt,hMain,hDef]

end ActualTZLiteralOrdinaryBound318
