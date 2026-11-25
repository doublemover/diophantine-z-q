module

public import OriginalRetainedEuclideanAtlas318
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section
noncomputable section

namespace OriginalRetainedActualAtlasHausdorff318

open AlgebraicGeometry CategoryTheory
open OriginalRetainedProjectiveAffinePiece318 OriginalRetainedClosedProjectiveEvaluation318
open OriginalRetainedProjectiveAffinePoints318 OriginalRetainedComplexZeroByPasting318
open OriginalRetainedProjectiveRatio318 OriginalRetainedAffineChartPointEquiv318
open OriginalRetainedAffineChartTransitions318 OriginalRetainedEuclideanAtlas318
open scoped Topology BigOperators ComplexConjugate

variable {κ : Type} [Fintype κ] [DecidableEq κ]

def energy (v : κ → ℂ) : ℝ := ∑ i, Complex.normSq (v i)

def projector (v : κ → ℂ) (i j : κ) : ℂ :=
  v i * conj (v j) / (energy v : ℂ)

theorem energy_pos (v : κ → ℂ) (i : κ) (hi : v i≠0) : 0<energy v := by
  exact (Complex.normSq_pos.mpr hi).trans_le
    (Finset.single_le_sum (fun k _ => Complex.normSq_nonneg (v k)) (Finset.mem_univ i))

theorem energy_scale (c : ℂ) (v : κ → ℂ) :
    energy (fun i => c*v i)=Complex.normSq c*energy v := by
  simp only [energy,Complex.normSq_mul,Finset.mul_sum]

theorem projector_scale (v : κ → ℂ) (c : ℂ) (hc : c≠0) :
    projector (fun i => c*v i)=projector v := by
  funext i j
  rw [projector,energy_scale,Complex.ofReal_mul,map_mul]
  have e : (c*v i)*(conj c*conj (v j)) =
      ((Complex.normSq c : ℝ):ℂ)*(v i*conj (v j)) := by
    rw [←Complex.mul_conj]
    ac_rfl
  rw [e,mul_div_mul_left _ _ (Complex.ofReal_ne_zero.2 (Complex.normSq_pos.2 hc).ne')]
  rfl

theorem promote_ratio_scaled (v : κ→ℂ) (j : κ) (hj : v j≠0) :
    promote (ratio v j) = fun k => (v j)⁻¹ * v k := by
  funext k
  by_cases h : k=j
  · subst k
    rw [promote_ith,inv_mul_cancel₀ hj]
  · rw [promote,dif_neg h]
    change v k*(v j)⁻¹=(v j)⁻¹*v k
    exact mul_comm _ _

theorem projector_ratio_recovers (v : κ→ℂ) (k j : κ) (hj : v j≠0) :
    projector v k j / projector v j j = v k / v j := by
  have en : (energy v : ℂ)≠0 := Complex.ofReal_ne_zero.2 (energy_pos v j hj).ne'
  have c : conj (v j)≠0 := map_ne_zero (starRingEnd ℂ) hj
  simp only [projector,div_div_div_cancel_right₀ en]
  rw [mul_comm (v k),mul_comm (v j),mul_div_mul_left _ _ c]

section Actual
variable {A Y E : Scheme} (a : A ⟶ Y) (P33 : E ⟶ Y) (σ : T ⟶ E)
local notation "X" => retainedCarrier a P33 σ
local notation "F" => fiber a (σ≫P33)
local notation "P" => (Over.mk (𝟙 T) ⟶ F)
variable (embedding : X ⟶ Ambient κ) (C : ∀ i, Chart a P33 σ embedding i)
local instance chosenTopology : TopologicalSpace P := euclidean a P33 σ embedding C
local notation "Rowsᵢ" => (fun i => Rows (C i).I)
local notation "addrₐ" => (fun i => OriginalRetainedAffineChartPointEquiv318.evaluate a P33 σ embedding (C i))

/-- Projectors agree via the actual projective overlap, not a
coordinate equality on unrelated Scheme points. -/
theorem chart_independent {i j : κ} (r : Rowsᵢ i) (s : Rowsᵢ j)
    (eq : addrₐ i r=addrₐ j s) :
    projector (promote r.val)=projector (promote s.val) := by
  have nz := (chart_domain a P33 σ embedding (C i) (C j) r).1
    (eq ▸ addr_in_chart a P33 σ embedding C j s)
  let u : Overlap (k:=j) a P33 σ embedding (C i) := ⟨r,nz⟩
  let t := transition a P33 σ embedding (C i) (C j) u
  have ts : t=s := (addr_injective a P33 σ embedding C j)
    ((same_point a P33 σ embedding (C i) (C j) u).trans eq)
  have val : s.val=ratio (promote r.val) j :=
    (congrArg Subtype.val ts).symm.trans (transition_coordinates a P33 σ embedding (C i) (C j) u)
  rw [val,promote_ratio_scaled _ j nz,projector_scale _ _ (inv_ne_zero nz)]

/-- This is one canonical continuous Hausdorff witness calculated
on the literal complex points, independent of the selected chart. -/
def pointProjector (p : P) : κ→κ→ℂ :=
  let u := Classical.choose (all_points_addressed a P33 σ embedding C p)
  projector (promote u.2.val)

theorem pointProjector_chart {i : κ} (r : Rowsᵢ i) :
    pointProjector a P33 σ embedding C (addrₐ i r)=projector (promote r.val) := by
  let u := Classical.choose (all_points_addressed a P33 σ embedding C (addrₐ i r))
  exact chart_independent a P33 σ embedding C u.2 r
    (Classical.choose_spec (all_points_addressed a P33 σ embedding C (addrₐ i r)))

theorem pointProjector_injective :
    Function.Injective (pointProjector a P33 σ embedding C) := by
  intro p q ep
  obtain ⟨⟨i,r⟩,hr⟩ := all_points_addressed a P33 σ embedding C p
  obtain ⟨⟨j,s⟩,hs⟩ := all_points_addressed a P33 σ embedding C q
  change addrₐ i r=p at hr
  change addrₐ j s=q at hs
  rw [←hr,←hs,pointProjector_chart,pointProjector_chart] at ep
  let v := promote r.val
  let w := promote s.val
  have wj : w j≠0 := promote_nonzero s.val
  have vj : v j≠0 := by
    intro hv
    have e := congrFun (congrFun ep j) j
    change projector v j j=projector w j j at e
    have wD : (energy w : ℂ)≠0 := Complex.ofReal_ne_zero.2 (energy_pos w j wj).ne'
    have nonzero : projector w j j≠0 := by
      rw [projector,Complex.mul_conj]
      exact div_ne_zero (Complex.ofReal_ne_zero.2 (Complex.normSq_pos.2 wj).ne') wD
    exact nonzero (e.symm.trans (by simp [projector,hv]))
  let u : Overlap (k:=j) a P33 σ embedding (C i) := ⟨r,vj⟩
  let t := transition a P33 σ embedding (C i) (C j) u
  have ts : t=s := by
    apply Subtype.ext
    rw [show t.val=ratio v j from transition_coordinates a P33 σ embedding (C i) (C j) u,
      ← show ratio w j=s.val from ratio_promote s.val]
    funext k
    have e := congrArg (fun M : κ→κ→ℂ => M k.val j / M j j) ep
    change (projector v k.val j)/(projector v j j)=
      (projector w k.val j)/(projector w j j) at e
    rw [projector_ratio_recovers v _ _ vj,projector_ratio_recovers w _ _ wj] at e
    exact e
  exact hr.symm.trans (((same_point a P33 σ embedding (C i) (C j) u).symm).trans
    (show addrₐ j t=q from ts.symm ▸ hs))

theorem pointProjector_continuous :
    Continuous (pointProjector a P33 σ embedding C) := by
  apply continuous_def.2
  intro U Uo
  apply (open_iff a P33 σ embedding C _).2
  intro i
  change IsOpen ((pointProjector a P33 σ embedding C ∘ addrₐ i) ⁻¹' U)
  have eq : pointProjector a P33 σ embedding C ∘ addrₐ i =
      fun r : Rowsᵢ i => projector (promote r.val) :=
    funext (pointProjector_chart a P33 σ embedding C)
  rw [eq]
  apply Continuous.isOpen_preimage _ U Uo
  have c (j : κ) : Continuous (fun r : Rowsᵢ i => promote r.val j) := by
    by_cases h : j=i
    · subst j
      simpa only [promote_ith] using continuous_const (b:=(1:ℂ))
    · simp only [promote,dif_neg h]
      exact (continuous_apply ⟨j,h⟩).comp continuous_subtype_val
  have e : Continuous (fun r : Rowsᵢ i => (energy (promote r.val) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (continuous_finsetSum Finset.univ (fun j _ => Complex.continuous_normSq.comp (c j)))
  apply continuous_pi
  intro j
  apply continuous_pi
  intro k
  exact ((c j).mul (Complex.continuous_conj.comp (c k))).div₀ e
    (fun r => Complex.ofReal_ne_zero.2
      (energy_pos (promote r.val) i (promote_nonzero r.val)).ne')

/-- The actual q target, not a synthetic quotient, is Hausdorff. -/
theorem actual_hausdorff : T2Space P :=
  T2Space.of_injective_continuous (pointProjector_injective a P33 σ embedding C)
    (pointProjector_continuous a P33 σ embedding C)

end Actual
end OriginalRetainedActualAtlasHausdorff318
