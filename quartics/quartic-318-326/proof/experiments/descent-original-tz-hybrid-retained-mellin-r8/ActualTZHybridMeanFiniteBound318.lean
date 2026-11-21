module
public import ActualTZHybridMeanCorrection318
public import ActualTZLiteralOrdinaryBound318
import all ActualTZFiniteMainBand318
import all ActualTZHybridMeanCell318
import all ActualTZHybridMeanAverage318
import all ActualTZHybridCanonicalWrap318
import all ActualTZLiteralWrapClipping318
public section
noncomputable section
universe u
namespace ActualTZHybridMeanFiniteBound318
open MeasureTheory
open scoped BigOperators Topology
open ActualTZHybridCanonicalWrap318
open ActualTZHybridMeanAverage318 ActualTZHybridMeanCell318 ActualTZHybridMeanCorrection318
open ActualTZOrdinaryReferenceCut318 ActualTZOrdinaryMomentUniformIndex318 ActualTZLiteralOrdinaryBound318
open ActualTZLiteralSchwartz318 ActualTZAngularKernelMain318 ActualTZAngularTensorTail318
open ActualTZLiteralLowIntegral318 ActualTZFiniteMainBand318 ActualTZLiteralMellinTensor318
open ActualTZLiteralWrapClipping318
variable {I : Type u} [Fintype I] [DecidableEq I]

theorem defect_le {a t s : ℕ} (X : Context a t s I)  :
    |retainedMass X-1|≤lostBound X := by
  have h0 : retainedMass X≤1 := X.retained_mass
  rw [abs_of_nonpos (sub_nonpos.mpr h0),neg_sub]
  have h : 1-retainedMass X=
      ∑ z : X.G,X.mass z*(∑ q : X.Keys,(wrapMass X.n X.size z q-X.θ z q)) := by
    simp only [Finset.sum_sub_distrib,mul_sub,X.full_mass,retainedMass]
  rw [h]
  exact X.lost

private theorem flatten {a t s : ℕ} (X : Context a t s I) (F : X.G→X.Keys→ℝ) :
    (∑ zr : X.G×X.Keys,(X.mass zr.1*X.θ zr.1 zr.2)*F zr.1 zr.2)=avg X X.θ F := by
  simp only [Fintype.sum_prod_type,avg,Finset.mul_sum,mul_assoc]

private theorem flatten_one {a t s : ℕ} (X : Context a t s I) :
    (∑ zr : X.G×X.Keys,X.mass zr.1*X.θ zr.1 zr.2)=retainedMass X := by
  simp only [Fintype.sum_prod_type,retainedMass,Finset.mul_sum]

/-- The terminal error on the literal original old shared-x
ordinary moment. The threshold is fixed at (χ,W,η) before the
physical grid, signs, wraps, or its growing finite index. The
collision cost is the genuine finite weighted prefix bound. -/
theorem finite_bound (C : Cutoff) (hχ : (∫ u in (0:ℝ)..1,|deriv C.χ u|^2)=1)
    (B : ℝ) (hB : ∀ t,|C.χ t|≤B) (y : ℕ) (η : ℝ) (hη : 0<η) :
    ∃ L₀≥(1:ℝ),∀ {a t s : ℕ}
      (X : Context a t s I),X.y=y→∀ R>1,L₀≤Real.log R→
      ∃ P : ℕ,Real.exp ((Real.log R)^2)≤(P:ℝ) ∧
        (primorial y).primeFactors⊆Nat.primesBelow (P+1) ∧ ⌊R⌋₊<P+1 ∧
        |original X (α (primorial y)) R C.χ-1|≤
          (Real.log R*(2*R*B)^2)^Fintype.card I*lostBound X+
          intervalError X (α (primorial y)) R B+
          (2*(∫ ξ,‖mainDensity C ξ‖ ∂μ I))*budget X (P+1)+η+lostBound X := by
  obtain ⟨L₀,h0,hAccept⟩ := accepts_uniform (I:=I) C (primorial y)
    (primorial_pos y) hχ η hη
  refine ⟨L₀,h0,?_⟩
  intro a t s X hY R hR hL
  rw [←hY] at hAccept ⊢
  let W := primorial X.y
  have hW : 0<W := primorial_pos _
  obtain ⟨P,hP,hWheel,hCut⟩ := reference_exists W hW R
  refine ⟨P,hP,hWheel,hCut,?_⟩
  let J := X.G×X.Keys
  let w : J→ℝ := fun zr=>X.mass zr.1*X.θ zr.1 zr.2
  have hw (zr : J) : 0≤w zr :=
    mul_nonneg (by unfold Context.mass; positivity) (X.θ_bounds zr.1 zr.2).1
  have hUnit : (∑ zr : J,w zr)≤1 := by
    change (∑ zr : X.G×X.Keys,X.mass zr.1*X.θ zr.1 zr.2)≤1
    rw [flatten_one X]
    exact X.retained_mass
  have hBig :
      |∑ zr : J,w zr*(exactMain C W (X.wrapped zr.1 zr.2) X.base R-1)|≤
        (2*(∫ ξ,‖mainDensity C ξ‖ ∂μ I))*budget X (P+1)+η :=
    hAccept R hR hL P hP hWheel hCut J (fun zr=>X.wrapped zr.1 zr.2) (fun _=>X.base)
      (fun _ i=>(base_unit X) i) w hw hUnit _ (budget_nonneg X P)
      (fun ξ _=>angular X P (Real.log R) (Real.log_pos hR) ξ)
  have hMain : |gridMain X (α W) R C.χ-retainedMass X|≤_ := by
    have he : (∑ zr : J,w zr*(exactMain C W (X.wrapped zr.1 zr.2) X.base R-1))=
        gridMain X (α W) R C.χ-retainedMass X := by
      change (∑ zr : X.G×X.Keys,(X.mass zr.1*X.θ zr.1 zr.2)*
        (exactMain C W (X.wrapped zr.1 zr.2) X.base R-1))=_
      rw [flatten X]
      simp only [avg,gridMain,retainedMass,ActualTZHybridMeanCell318.mainCell,exactMain,
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

end ActualTZHybridMeanFiniteBound318
