module

public import OriginalRetainedActualCenteredBand318
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Abel

@[expose] public section
noncomputable section

namespace OriginalRetainedOneActualLocalExponential318

open AlgebraicGeometry CategoryTheory
open OriginalRetainedProjectiveAffinePiece318 OriginalRetainedClosedProjectiveEvaluation318
open OriginalRetainedComplexZeroByPasting318 OriginalRetainedEuclideanAtlas318
open scoped Topology

abbrev V := Fin 2→ℂ
abbrev Ball (ρ : ℝ) := {x : V // ‖x‖<ρ}

variable (ρ : ℝ) (l λ : V→V)
variable (t : ℝ)
variable (l0 : l 0=0)
variable (η : ∀ x y, ‖x‖≤ρ → ‖y‖≤ρ →
  ‖(l x-x)-(l y-y)‖≤(1/2:ℝ)*‖x-y‖)
variable (λ_read : ∀ v, ‖v‖≤ρ/2 → ‖λ v‖≤ρ ∧ l (λ v)=v)

include η in
theorem log_distances (x y : V) (hx : ‖x‖≤ρ) (hy : ‖y‖≤ρ) :
    ‖l x-l y‖≤2*‖x-y‖ ∧ ‖x-y‖≤2*‖l x-l y‖ := by
  let d := (l x-x)-(l y-y)
  have a : ‖d‖≤(1/2:ℝ)*‖x-y‖ := η x y hx hy
  have e : l x-l y=(x-y)+d := by dsimp only [d]; abel
  have e' : x-y=(l x-l y)-d := by dsimp only [d]; abel
  constructor
  · rw [e]
    exact (norm_add_le _ _).trans (by linarith only [a,norm_nonneg (x-y)])
  · have b : ‖x-y‖≤‖l x-l y‖+‖d‖ := by
      conv_lhs => rw [e']
      exact norm_sub_le _ _
    linarith only [a,b]

include η λ_read in
theorem inverse_distances (v w : V) (hv : ‖v‖≤ρ/2) (hw : ‖w‖≤ρ/2) :
    ‖λ v-λ w‖≤2*‖v-w‖ := by
  have b := (log_distances ρ l η (λ v) (λ w) (λ_read v hv).1 (λ_read w hw).1).2
  rwa [(λ_read v hv).2,(λ_read w hw).2] at b

include η λ_read l0 in
theorem inverse_strict (v : Ball t) (tsmall : t≤ρ/2) (ρpos : 0<ρ) : ‖λ v.val‖<ρ := by
  have hv := (v.property.trans_le tsmall).le
  have b := (log_distances ρ l η (λ v.val) 0 (λ_read v.val hv).1
    (by simpa only [norm_zero] using ρpos.le)).2
  rw [l0,sub_zero,sub_zero,(λ_read v.val hv).2] at b
  linarith only [b,v.property,tsmall]

include η in
theorem log_continuous_band : Continuous (fun x : Ball ρ => l x.val) := by
  apply LipschitzWith.continuous (K:=2)
  apply LipschitzWith.of_dist_le_mul
  intro u v
  change dist (l u.val) (l v.val)≤2*dist u.val v.val
  simp only [dist_eq_norm]
  exact (log_distances ρ l η u.val v.val u.property.le v.property.le).1

include η λ_read in
theorem inverse_continuous_band (tsmall : t≤ρ/2) : Continuous (fun v : Ball t => λ v.val) := by
  apply LipschitzWith.continuous (K:=2)
  apply LipschitzWith.of_dist_le_mul
  intro u v
  change dist (λ u.val) (λ v.val)≤2*dist u.val v.val
  simp only [dist_eq_norm]
  exact inverse_distances ρ l λ η λ_read u.val v.val
    (u.property.trans_le tsmall).le (v.property.trans_le tsmall).le

def logBand : Set (Ball ρ) := {x | ‖l x.val‖<t}

include η in
theorem logBand_open : IsOpen (logBand ρ l t) :=
  isOpen_lt (log_continuous_band ρ l η).norm continuous_const

include η λ_read l0 in
/-- Exact local inverse on the old chart, with both continuities
deduced from the displacement of the SAME dyadic limit. -/
def inverseHomeo (tsmall : t≤ρ/2) (ρpos : 0<ρ) : Ball t ≃ₜ logBand ρ l t where
  toFun v := ⟨⟨λ v.val,inverse_strict ρ l λ t l0 η λ_read v tsmall ρpos⟩,by
    change ‖l (λ v.val)‖<t
    rwa [(λ_read v.val (v.property.trans_le tsmall).le).2]⟩
  invFun z := ⟨l z.val.val,z.property⟩
  left_inv v := Subtype.ext (λ_read v.val (v.property.trans_le tsmall).le).2
  right_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    have zh := z.val.property.le
    have read := λ_read (l z.val.val) (z.property.trans_le tsmall).le
    have e := (log_distances ρ l η (λ (l z.val.val)) z.val.val read.1 zh).2
    rw [read.2,sub_self,norm_zero,mul_zero] at e
    exact sub_eq_zero.1 (norm_eq_zero.1 (le_antisymm e (norm_nonneg _)))
  continuous_toFun := ((inverse_continuous_band ρ l λ t η λ_read tsmall).subtype_mk _).subtype_mk _
  continuous_invFun := ((log_continuous_band ρ l η).comp continuous_subtype_val).subtype_mk _

section Actual
variable {κ : Type} [Fintype κ] [DecidableEq κ]
variable {A Y E : Scheme} (a : A ⟶ Y) (P33 : E ⟶ Y) (σ : T ⟶ E)
local notation "X" => retainedCarrier a P33 σ
local notation "F" => fiber a (σ≫P33)
local notation "P" => (Over.mk (𝟙 T) ⟶ F)
variable (embedding : X ⟶ Ambient κ) (C : ∀ i, Chart a P33 σ embedding i)
local instance chosenTopology : TopologicalSpace P := euclidean a P33 σ embedding C

variable (U : Set P) (Uopen : IsOpen U)
-- Take the literal R252 localHomeo on the fixed smaller log radius.
variable (old : Ball ρ ≃ₜ U)
def openSlice : Set U := (old.symm : U→Ball ρ) ⁻¹' logBand ρ l t

def actualSmallOpen : Set P := Subtype.val '' openSlice ρ l t a P33 σ embedding C U old

include η Uopen in
theorem actualSmallOpen_isOpen :
    IsOpen (actualSmallOpen ρ l t a P33 σ embedding C U old) := by
  apply Uopen.isOpenMap_subtype_val
  exact old.symm.continuous_toFun.isOpen_preimage _ (logBand_open ρ l t η)

include l0 η λ_read in
/-- The local exponential maps onto an actual open of the exact
retained selected point scheme with the actual R244 topology. -/
def actualLocal (tsmall : t≤ρ/2) (ρpos : 0<ρ) : Ball t ≃ₜ actualSmallOpen ρ l t a P33 σ embedding C U old := by
  let cut := old.symm.subtype
    (p:=openSlice ρ l t a P33 σ embedding C U old)
    (q:=logBand ρ l t) (fun _ => Iff.rfl)
  exact ((inverseHomeo ρ l λ t l0 η λ_read tsmall ρpos).trans cut.symm).trans
    (Topology.IsEmbedding.subtypeVal.homeomorphImage _)

include l0 η λ_read in
/-- Read the existing one global point map via its original local
agreement: this changes neither q nor the original mark. -/
theorem reads_one_original (tsmall : t≤ρ/2) (ρpos : 0<ρ) (q : V→P)
    (same : ∀ v : Ball t, q v.val=
      (old ⟨λ v.val,inverse_strict ρ l λ t l0 η λ_read v tsmall ρpos⟩).val)
    (v : Ball t) :
    ((actualLocal ρ l λ t l0 η λ_read a P33 σ embedding C U old tsmall ρpos) v).val=q v.val :=
  (same v).symm

end Actual
end OriginalRetainedOneActualLocalExponential318
