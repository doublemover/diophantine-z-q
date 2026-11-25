module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Topology.Algebra.Group.Neighborhood
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

@[expose] public section
noncomputable section
namespace OriginalLocalNormalizedExponentialContinuation318
open Set Function Filter
open scoped Topology
abbrev V := Fin 2→ℂ

def shrink (n:ℕ) (z:V):V := ((2:ℝ)^n)⁻¹ • z

theorem shrink_zero (z:V):shrink 0 z=z := by simp [shrink]
theorem shrink_add (n:ℕ) (z w:V):shrink n (z+w)=shrink n z+shrink n w :=
  smul_add _ _ _

theorem shrink_fold (n:ℕ) (z:V):shrink (n+1) z+shrink (n+1) z=shrink n z := by
  simp only [shrink,←add_smul,pow_succ]
  congr 1
  rw [mul_inv_rev]
  ring

theorem norm_shrink (n:ℕ) (z:V): ‖shrink n z‖=‖z‖/(2:ℝ)^n := by
  rw [shrink,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity),div_eq_mul_inv,mul_comm]

theorem norm_shrink_mono {n m:ℕ} (h:n≤m) (z:V): ‖shrink m z‖≤‖shrink n z‖ := by
  rw [norm_shrink,norm_shrink]
  exact div_le_div_of_nonneg_left (norm_nonneg z) (by positivity)
    (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) h)

theorem nat_lt_pow_two (n:ℕ) : (n:ℝ)<(2:ℝ)^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hp:(1:ℝ)≤(2:ℝ)^n := one_le_pow₀ (by norm_num)
    rw [Nat.cast_succ,pow_succ]
    linarith

theorem small_exists (r:ℝ) (hr:0<r) (z:V):∃n:ℕ,‖shrink n z‖<r := by
  obtain ⟨n,hn⟩ := exists_nat_gt (‖z‖/r)
  have hh : ‖z‖/r < (2:ℝ)^n := hn.trans (nat_lt_pow_two n)
  refine ⟨n,?_⟩
  rw [norm_shrink]
  exact (div_lt_iff₀ (by positivity)).mpr
    (by simpa only [mul_comm] using ((div_lt_iff₀ hr).mp hh))

variable {J:Type*} [AddCommGroup J] (r:ℝ) (hr:0<r) (loc:V→J)
  (at_zero:loc 0=0)
  (add_on_ball:∀z w:V,‖z‖<r→‖w‖<r→‖z+w‖<r→loc (z+w)=loc z+loc w)

/-- Dyadic continuation uses existing point multiplication only.
Values of loc outside the retained identity ball are not used. -/
def readAt (n:ℕ) (z:V):J := (2^n:ℕ) • loc (shrink n z)

include add_on_ball in
theorem read_step (n:ℕ) (z:V) (hz:‖shrink n z‖<r):
    readAt loc (n+1) z=readAt loc n z := by
  have half:‖shrink (n+1) z‖<r := (norm_shrink_mono (Nat.le_succ n) z).trans_lt hz
  have fold := shrink_fold n z
  have hin:‖shrink (n+1) z+shrink (n+1) z‖<r := fold.symm ▸ hz
  have h := add_on_ball (shrink (n+1) z) (shrink (n+1) z) half half hin
  rw [fold] at h
  unfold readAt
  rw [pow_succ,mul_nsmul,two_nsmul,←h]

include add_on_ball in
theorem read_independent (z:V) {n m:ℕ} (hnm:n≤m) (hn:‖shrink n z‖<r):
    readAt loc m z=readAt loc n z := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
    exact (read_step r loc add_on_ball m z ((norm_shrink_mono hm z).trans_lt hn)).trans ih

/-- This is a definition on every tangent vector, made from its
unique already fixed local exponential. -/
def globalRead (z:V):J := readAt loc (Nat.find (small_exists r hr z)) z

include add_on_ball in
theorem globalRead_at (z:V) (n:ℕ) (hn:‖shrink n z‖<r):
    globalRead r hr loc z=readAt loc n z :=
  (read_independent r loc add_on_ball z (Nat.find_min' (small_exists r hr z) hn)
    (Nat.find_spec (small_exists r hr z))).symm

include add_on_ball in
theorem globalRead_local (z:V) (hz:‖z‖<r):globalRead r hr loc z=loc z := by
  have h : ‖shrink 0 z‖<r := by simpa only [shrink_zero] using hz
  rw [globalRead_at r hr loc add_on_ball z 0 h]
  simp [readAt,shrink_zero]

include at_zero add_on_ball in
/-- The exponential on the whole normalized Lie space is produced
rather than supplied. The multiplicative target is the actual point
group, expressed additively here. -/
def continueExp : V→+J where
  toFun:=globalRead r hr loc
  map_zero' := (globalRead_local r hr loc add_on_ball 0 (by simpa using hr)).trans at_zero
  map_add' z w := by
    let nz:=Nat.find (small_exists r hr z)
    let nw:=Nat.find (small_exists r hr w)
    let ns:=Nat.find (small_exists r hr (z+w))
    let m:=max nz (max nw ns)
    have hz:‖shrink m z‖<r :=
      (norm_shrink_mono (le_max_left nz (max nw ns)) z).trans_lt (Nat.find_spec (small_exists r hr z))
    have hw:‖shrink m w‖<r :=
      (norm_shrink_mono ((le_max_left nw ns).trans (le_max_right nz (max nw ns))) w).trans_lt
        (Nat.find_spec (small_exists r hr w))
    have hs:‖shrink m (z+w)‖<r :=
      (norm_shrink_mono ((le_max_right nw ns).trans (le_max_right nz (max nw ns))) (z+w)).trans_lt
        (Nat.find_spec (small_exists r hr (z+w)))
    rw [globalRead_at r hr loc add_on_ball z m hz,globalRead_at r hr loc add_on_ball w m hw,
      globalRead_at r hr loc add_on_ball (z+w) m hs]
    have localSum : loc (shrink m (z+w))=loc (shrink m z)+loc (shrink m w) := by
      rw [shrink_add m z w] at hs ⊢
      exact add_on_ball _ _ hz hw hs
    simp only [readAt,localSum,nsmul_add]

include at_zero add_on_ball in
theorem continueExp_local (z:V) (hz:‖z‖<r):continueExp r hr loc at_zero add_on_ball z=loc z :=
  globalRead_local r hr loc add_on_ball z hz

theorem recover_from_shrunk (n:ℕ) (z:V):(2^n:ℕ) • shrink n z=z := by
  have hc : ((2^n:ℕ):ℝ)=(2:ℝ)^n := by norm_num
  rw [←Nat.cast_smul_eq_nsmul ℝ,hc,shrink,smul_smul,mul_inv_cancel₀ (by positivity),one_smul]

include at_zero add_on_ball in
theorem continueExp_unique (F:V→+J) (hF:∀z:V,‖z‖<r→F z=loc z):
    continueExp r hr loc at_zero add_on_ball=F := by
  ext z
  obtain ⟨n,hn⟩:=small_exists r hr z
  change globalRead r hr loc z=F z
  rw [globalRead_at r hr loc add_on_ball z n hn]
  calc
    _ = (2^n:ℕ) • F (shrink n z) :=
      congrArg (fun p:J=>(2^n:ℕ) • p) (hF _ hn).symm
    _ = F ((2^n:ℕ) • shrink n z) := (map_nsmul F _ _).symm
    _ = _ := congrArg F (recover_from_shrunk n z)

section ActualTopology
variable [TopologicalSpace J]

include at_zero add_on_ball in
theorem continueExp_near
    (near:loc '' {z:V | ‖z‖<r}∈𝓝 (0:J)):
    ((continueExp r hr loc at_zero add_on_ball).range : Set J)∈𝓝 (0:J) := by
  refine Filter.mem_of_superset near ?_
  rintro _ ⟨z,hz,rfl⟩
  exact ⟨z,continueExp_local r hr loc at_zero add_on_ball z hz⟩

include at_zero add_on_ball in
theorem continueExp_continuousAt (initial:ContinuousAt loc (0:V)):
    ContinuousAt (continueExp r hr loc at_zero add_on_ball) 0 := by
  have close : ∀ᶠ z:V in 𝓝 0,‖z‖<r :=
    ((Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr)) : Metric.ball (0:V) r∈𝓝 0).mono
      (by intro v hv; simpa only [Metric.mem_ball,dist_zero_right] using hv)
  apply initial.congr_of_eventuallyEq
  exact close.mono fun v hv=>continueExp_local r hr loc at_zero add_on_ball v hv
end ActualTopology
end OriginalLocalNormalizedExponentialContinuation318
