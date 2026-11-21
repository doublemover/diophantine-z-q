module
public import Mathlib
public section
noncomputable section
namespace OriginalInteriorTelescoping318
open scoped BigOperators

/-- The prime on a genuine rational value is counted once, not once per
generator. Functions in the analytic input vanish at composites and powers. -/
def logPrimeRay (ray : ℕ → Prop) (p : ℤ) : ℝ := by
  classical
  exact if 0<p ∧ p.natAbs.Prime ∧ ray p.natAbs then Real.log (p:ℝ) else 0

/-- One genuine reduced residue row of the original prescribed family.
ci holds the step-divisibility-folded, merged coefficients, in any order;
the dummy is not included in ci. -/
structure Row where
  W : ℕ
  n : ℕ
  M : ℕ
  b : ℤ
  c : ℤ
  K : ℤ
  ci : ℕ → ℤ
  k : ℕ
  phiRatio : ℝ
  cut : ℕ
  ray : ℕ → Prop
  mu : ℤ → ℝ

def d (r : Row) (i : ℕ) := r.ci i - r.K
def residue (r : Row) (i : ℕ) : ℤ := 1 + (r.b+d r i*r.c^2-1)%(r.W:ℤ)
def shift (r : Row) (i : ℕ) (m : ℤ) : ℤ :=
  d r i*(r.W:ℤ)*m^2+2*d r i*r.c*m+(r.b+d r i*r.c^2-residue r i)/(r.W:ℤ)
def rep (n : ℕ) (x : ℤ) := 1 + (x-1)%(n:ℤ)
abbrev Dom (r : Row) := Fin r.n × Fin r.M
def arg (r : Row) (i : ℕ) (z : Dom r) : ℤ :=
  rep r.n ((z.1.val:ℤ)+1+shift r i ((z.2.val:ℤ)+1))
def val (r : Row) (i : ℕ) (z : Dom r) := (r.W:ℤ)*arg r i z+residue r i
def f (r : Row) (i : ℕ) (z : Dom r) : ℝ :=
  if (r.cut:ℤ) ≤ arg r i z then r.phiRatio*logPrimeRay r.ray (val r i z) else 0
def mean (r : Row) (i : ℕ) (z : Dom r) : ℝ := r.mu (val r i z)
def dummy (r : Row) (z : Dom r) : ℝ :=
  if 5*r.n ≤ 8*(z.1.val+1) ∧ 4*(z.1.val+1) ≤ 3*r.n then 1 else 0
def mass (r : Row) (g : Dom r → ℝ) := ∑ z : Dom r, dummy r z*g z

/-- Insert one centered prime at a time. The telescoping prefix avoids all
2^k subfamily hypotheses; only k particular bounds are ever consumed. -/
def blend {ι : Type*} (f m : ℕ → ι → ℝ) (k j : ℕ) (z : ι) :=
  ∏ i∈Finset.range k, if i<j then f i z else m i z

theorem blend_step {ι : Type*} (f m : ℕ → ι → ℝ) {k j : ℕ} (hj : j<k) (z : ι) :
    blend f m k (j+1) z-blend f m k j z =
      (f j z-m j z) * (∏ i∈(Finset.range k).erase j, if i<j then f i z else m i z) := by
  classical
  let A := Finset.range k
  have hm : j∈A := Finset.mem_range.mpr hj
  have eqrest : (∏ i∈A.erase j, if i<j+1 then f i z else m i z) =
      ∏ i∈A.erase j, if i<j then f i z else m i z := by
    apply Finset.prod_congr rfl
    intro i hi
    have hne := (Finset.mem_erase.mp hi).1
    by_cases h : i<j <;> simp [h, show i<j+1 ↔ i<j by omega]
  change (∏ i∈A, if i<j+1 then f i z else m i z) -
      (∏ i∈A, if i<j then f i z else m i z) = _
  rw [←Finset.mul_prod_erase A (fun i => if i<j+1 then f i z else m i z) hm,
      ←Finset.mul_prod_erase A (fun i => if i<j then f i z else m i z) hm,
      eqrest]
  simp only [Nat.lt_succ_self,if_true,lt_self_iff_false,if_false]
  ring

/-- THE exact remaining fixed-row analytic input. On the actual family one
takes eps=o(1) and unnormalizes by n*M. The pointed polynomial theorem
only needs its distinguished g_j bound; all other factors here, including
the bounded periodic means and the zero-shift dummy, are allowable cofactors. -/
def MixedBudget (r : Row) (eps : ℝ) : Prop :=
  ∀ j<r.k, |mass r (fun z => (f r j z-mean r j z) *
    ∏ i∈(Finset.range r.k).erase j, if i<j then f r i z else mean r i z)| ≤ eps

theorem total_of_mixed (r : Row) (eps : ℝ) (bud : MixedBudget r eps) :
    |mass r (fun z => ∏ i∈Finset.range r.k, f r i z)-
       mass r (fun z => ∏ i∈Finset.range r.k, mean r i z)| ≤ (r.k:ℝ)*eps := by
  let B (j : ℕ) := mass r (blend (f r) (mean r) r.k j)
  have step (j : ℕ) (hj : j<r.k) : |B (j+1)-B j| ≤ eps := by
    have hh := bud j hj
    dsimp [B,mass]
    rw [←Finset.sum_sub_distrib]
    simpa only [←mul_sub,blend_step _ _ hj] using hh
  have H (j : ℕ) (hj : j ≤ r.k) : |B j-B 0| ≤ (j:ℝ)*eps := by
    induction j with
    | zero => simp
    | succ j ih =>
      have hj' : j<r.k := by omega
      calc
        |B (j+1)-B 0| = |(B (j+1)-B j)+(B j-B 0)| := by congr 1; ring
        _ ≤ |B (j+1)-B j|+|B j-B 0| := abs_add_le _ _
        _ ≤ eps+(j:ℝ)*eps := add_le_add (step j hj') (ih (by omega))
        _ = ((j+1:ℕ):ℝ)*eps := by push_cast; ring
  have last : B r.k = mass r (fun z => ∏ i∈Finset.range r.k, f r i z) := by
    unfold B blend
    apply congrArg (mass r)
    funext z
    apply Finset.prod_congr rfl
    intro i hi
    simp [Finset.mem_range.mp hi]
  have first : B 0 = mass r (fun z => ∏ i∈Finset.range r.k, mean r i z) := by
    simp [B,blend]
  simpa only [last,first] using H r.k le_rfl

/-- The linear-test factor on the cyclic representative, independent of any
quadratic output map. The fixed-field version may take mu to be periodic. -/
def centeredAt (r : Row) (i : ℕ) (a : ℤ) : ℝ :=
  let y := rep r.n a
  let p := (r.W:ℤ)*y+residue r i
  (if (r.cut:ℤ) ≤ y then r.phiRatio*logPrimeRay r.ray p else 0)-r.mu p

/-- The literal power-of-norm cube: x is uniform cyclic, axes consist of
q times differences of independent uniform [J] variables in each direction. -/
def linearCube (r : Row) (i a q J : ℕ) : ℝ :=
  let S := Fin r.n × ((Fin a → Fin J) × (Fin a → Fin J))
  (∑ z : S, ∏ ω : Fin a → Bool, centeredAt r i
    ((z.1.val:ℤ)+1+(q:ℤ)*∑ t : Fin a,
      if ω t then ((z.2.1 t).val:ℤ)-((z.2.2 t).val:ℤ) else 0)) /
    ((r.n:ℝ)*(J:ℝ)^(2*a))

/-- At each actual selector, the field, tau, coefficients and folded scale are
fixed. All widths, incl. the one needed by the model, are explicitly
bounded first; there is no uniform error assumption in the field. -/
def LinearBudget (r : Row) (a qMax jMin jMax : ℕ) (delta : ℝ) : Prop :=
  ∀ i<r.k, ∀ q : ℕ, 1 ≤ q → q ≤ qMax → ∀ J : ℕ, jMin ≤ J → J ≤ jMax →
    |linearCube r i a q J| ≤ delta^ (2^a)

/-- Minimal single analytic bridge on ONLY the supplied fixed family and
actual residue rows. The caller chooses y (small-prime/majorant cutoff)
before the physical size N. The remaining arguments fix its norm order, q
cap and norm-width interval; it can depend on the fixed family. The purported
linear-to-polynomial theorem is represented as a named predicate, not axiomatized.
The justified diagonal parameters are spelled out in INTERIOR-POLYNOMIAL-TRANSFER.md. -/
def FixedFamilyTransfer (Rows : ℕ → ℕ → Set Row) (a : ℕ)
    (qMax : ℕ → ℕ) (jMin jMax : ℕ → ℕ → ℕ) : Prop :=
  ∀ eps : ℝ, 0<eps → ∃ delta : ℝ, 0<delta ∧ ∃ y0 : ℕ, ∀ y≥y0,
    ∃ N0 : ℕ, ∀ N≥N0, ∀ r∈Rows y N,
      LinearBudget r a (qMax y) (jMin y N) (jMax y N) delta →
      MixedBudget r (eps*(r.n:ℝ)*(r.M:ℝ))

/-- Actual donor wheel, exactly the squarefree product used in the published
Tao--Ziegler theorem (not enlarged by any conductor powers). -/
def wheel (y : ℕ) : ℕ := ∏ p∈(Finset.range (y+1)).filter Nat.Prime, p

structure Family where
  /-- Distinct list of already Q²-folded coefficients from the original support. -/
  ci : ℕ → ℤ
  k : ℕ
  K : ℤ
  distinct : ∀ i<k, ∀ j<k, i≠j → ci i≠ci j
  fresh : ∀ i<k, ci i≠K
  tau : ℝ
  htau : 0<tau
  rho : ℝ
  hrho : 0<rho
  ray : ℕ → Prop
  conductor : ℕ
  hconductor : 0<conductor
  fiber : ℤ → ℝ

/-- The actual normalized finite system at cutoff y, physical norm N and
two input residues; it reuses the same field, tau and coefficients throughout. -/
def Family.row (H : Family) (y N : ℕ) (b c : ℤ) : Row :=
  let W := wheel y
  let n := N/W
  let T := ⌊H.tau*Real.sqrt (N:ℝ)⌋₊
  { W := W, n := n, M := T/W-1, b := b, c := c, K := H.K, ci := H.ci, k := H.k,
    phiRatio := (Nat.totient W:ℝ)/(W:ℝ), cut := ⌈(n:ℝ)^H.rho⌉₊, ray := H.ray,
    mu := fun z => H.fiber (z%(H.conductor:ℤ)) }

/-- All allowed rows, not a single compatible residue class. No unit condition
on the dummy base residue; only the genuine prime outputs have unit residues. -/
def Family.rows (H : Family) (y N : ℕ) : Set Row :=
  {r | ∃ b c : ℤ, 1 ≤ b ∧ b ≤ (wheel y:ℤ) ∧ 0 ≤ c ∧ c < (wheel y:ℤ) ∧
    r=H.row y N b c ∧ ∀ i<H.k, Nat.Coprime (residue r i).natAbs (wheel y)}

def ActualDonor (H : Family) (a : ℕ) (qMax : ℕ → ℕ)
    (jMin jMax : ℕ → ℕ → ℕ) : Prop :=
  FixedFamilyTransfer H.rows a qMax jMin jMax

end OriginalInteriorTelescoping318
