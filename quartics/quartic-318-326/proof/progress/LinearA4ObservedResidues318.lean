module
public import LinearA4EulerDensity318
import all LinearA4EulerDensity318
import all LinearA4MixedNormCounts318
public section
noncomputable section

namespace LinearA4ObservedResidues318
open LinearA4GaussianCounts318 LinearA4MixedNormCounts318 LinearA4EulerDensity318
variable {K : Type*} [Field K]
abbrev V (K : Type*) := K × K
def det (a b : V K) : K := a.1*b.2-b.1*a.2
def dot (a x : V K) : K := a.1*x.1+a.2*x.2

def coords (a b v : V K) : V K :=
  (det v b/det a b, det a v/det a b)

theorem coeff_recovery (a b v x : V K) (h : det a b≠0) :
    (coords a b v).1*dot a x+(coords a b v).2*dot b x=dot v x := by
  unfold coords dot
  dsimp only
  field_simp [h]
  unfold det
  ring

theorem coeff_det (a b v w : V K) (h : det a b≠0) :
    det (coords a b v) (coords a b w)=det v w/det a b := by
  have hcross : det v b * det a w - det w b * det a v = det v w * det a b := by
    unfold det
    ring
  change (det v b / det a b) * (det a w / det a b) -
    (det w b / det a b) * (det a v / det a b) = det v w / det a b
  rw [div_mul_div_comm, div_mul_div_comm, ← sub_div, hcross]
  apply (div_eq_div_iff (mul_ne_zero h h) h).mpr
  ring

@[simp] theorem coords_left (a b : V K) (h : det a b≠0) :
    coords a b a=(1,0) := by
  unfold coords
  have z : det a a = 0 := by unfold det; ring
  simp [z,h]

@[simp] theorem coords_right (a b : V K) (h : det a b≠0) :
    coords a b b=(0,1) := by
  unfold coords
  have z : det b b = 0 := by unfold det; ring
  simp [z,h]

/-- q is a genuine linear form, indexed by none. Q² is part of the slope,
not part of the coordinate q in this actual basis. -/
def affine (Q : K) : Option K → V K
  | none => (0,1)
  | some k => (1,k*Q^2)
@[simp] theorem denominator (Q : K) (x : V K) : dot (affine Q none) x=x.2 := by simp [dot,affine]
@[simp] theorem contact (Q k : K) (x : V K) : dot (affine Q (some k)) x=x.1+k*Q^2*x.2 := by simp [dot,affine]

theorem affine_pairwise {Q : K} (hQ : Q≠0) {i j : Option K} (hij : i≠j) :
    det (affine Q i) (affine Q j)≠0 := by
  cases i with
  | none =>
    cases j with
    | none => exact (hij rfl).elim
    | some k => simp [affine,det]
  | some k =>
    cases j with
    | none => simp [affine,det]
    | some l =>
      have hkl : l-k≠0 := sub_ne_zero.mpr (by rintro rfl; exact hij rfl)
      change 1*(l*Q^2)-1*(k*Q^2)≠0
      rw [one_mul,one_mul,← sub_mul]
      exact mul_ne_zero hkl (pow_ne_zero _ hQ)

section Finite
variable [Fintype K] [DecidableEq K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def mixed (Q : K) (slots : (Fin 2 ⊕ ι) → Option K) (j : ι) : V K :=
  coords (affine Q (slots (.inl 0))) (affine Q (slots (.inl 1))) (affine Q (slots (.inr j)))

omit [Fintype K] [DecidableEq K] [Fintype ι] [DecidableEq ι] in
theorem all_coords (Q : K) (slots : (Fin 2 ⊕ ι) → Option K) (hQ : Q≠0)
    (inj : Function.Injective slots) (i : Fin 2 ⊕ ι) :
    coefficients (mixed Q slots) i =
      coords (affine Q (slots (.inl 0))) (affine Q (slots (.inl 1))) (affine Q (slots i)) := by
  have h := affine_pairwise hQ (fun e => (show (Sum.inl (0:Fin 2) : Fin 2 ⊕ ι) ≠ .inl 1 from fun v => (by decide : (0:Fin 2)≠1) (Sum.inl.inj v)) (inj e))
  rcases i with i|i
  · fin_cases i <;> simp [coefficients,h]
  · rfl

/-- The genuine FT/A4 two-observation local bound applies to all remaining
original affine shapes over the good residue fields. Distinctness here is
post-reduction; the finitely many primes where slopes merge belong in the
fixed omitted wheel, not in the asymptotic formula. -/
theorem observed_density (Q : K) (slots : (Fin 2 ⊕ ι) → Option K) (hQ : Q≠0)
    (inj : Function.Injective slots) (hp : ringChar K≠2) (h2 : (2:K)≠0) :
    let p : ℝ := Fintype.card K
    let m : ℝ := Fintype.card ι
    let c : ℝ := χ K
    let g : ℝ := ((badResidues (mixed Q slots)).card:ℝ)/p^4
    |g-(m+2+2*c)/p| ≤ (5*m+6)/p^2 := by
  have h := affine_pairwise hQ (fun e => (show (Sum.inl (0:Fin 2) : Fin 2 ⊕ ι) ≠ .inl 1 from fun v => (by decide : (0:Fin 2)≠1) (Sum.inl.inj v)) (inj e))
  apply actual_density _ hp h2
  · intro j
    unfold mixed coords
    constructor <;> apply div_ne_zero _ h
    · exact affine_pairwise hQ (fun e => by cases inj e)
    · exact affine_pairwise hQ (fun e => by cases inj e)
  · intro i j hij
    rw [all_coords Q slots hQ inj i,all_coords Q slots hQ inj j]
    change det (coords _ _ _) (coords _ _ _)≠0
    rw [coeff_det _ _ _ _ h]
    exact div_ne_zero (affine_pairwise hQ (fun e => hij (inj e))) h

/-- Cramer reconstruction of the genuine residue of the rational key. -/
def keyResidue (a b : V K) (z : Box K) : V K :=
  ((norm z.1*b.2-norm z.2*a.2)/det a b,
   (a.1*norm z.2-b.1*norm z.1)/det a b)

omit [Fintype K] [DecidableEq K] in
/-- Exact two linear readings of the Cramer-reconstructed key residue. -/
theorem key_readback (a b : V K) (z : Box K) (h : det a b≠0) :
    dot a (keyResidue a b z)=norm z.1 ∧ dot b (keyResidue a b z)=norm z.2 := by
  constructor
  · unfold dot keyResidue
    dsimp only
    field_simp [h]
    unfold det
    ring
  · unfold dot keyResidue
    dsimp only
    field_simp [h]
    unfold det
    ring

/-- The indexed union in the density count is exactly the event that at
least one of the original forms vanishes on the observed key residue. -/
theorem membership_original (Q : K) (slots : (Fin 2 ⊕ ι) → Option K) (hQ : Q≠0)
    (inj : Function.Injective slots) (z : Box K) :
    z ∈ badResidues (mixed Q slots) ↔
      ∃ i, dot (affine Q (slots i))
        (keyResidue (affine Q (slots (.inl 0))) (affine Q (slots (.inl 1))) z)=0 := by
  let a := affine Q (slots (.inl 0))
  let b := affine Q (slots (.inl 1))
  have h : det a b≠0 := affine_pairwise hQ
    (fun e => (by decide : (0:Fin 2)≠1) (Sum.inl.inj (inj e)))
  have id (i : Fin 2 ⊕ ι) :
      coeffNorm (coefficients (mixed Q slots) i) z =
        dot (affine Q (slots i)) (keyResidue a b z) := by
    rw [all_coords Q slots hQ inj i]
    change coeffNorm (coords a b _) z = _
    unfold coeffNorm
    rw [← (key_readback a b z h).1,← (key_readback a b z h).2]
    exact coeff_recovery a b _ _ h
  simp only [badResidues,Finset.mem_biUnion,Finset.mem_univ,true_and,fibreSet,Finset.mem_filter,id]
  rfl

end Finite
end LinearA4ObservedResidues318
