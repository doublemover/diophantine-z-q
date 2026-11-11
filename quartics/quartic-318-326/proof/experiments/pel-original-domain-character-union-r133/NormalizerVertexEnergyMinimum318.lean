module
public import NormalizerVertexEnergyBounds318
public section
namespace NormalizerVertexEnergyMinimum318
open NormalizerVertexEnergyBounds318
set_option maxHeartbeats 30000000
set_option maxRecDepth 4096
@[expose] def allowedNorm : Fin 16 → ℕ := ![1,2,3,5,6,7,10,14,15,21,30,35,42,70,105,210]
@[expose] def energy (k : Fin 2) (s r c d : ℤ) : ℤ :=
  if k=0 then energy0 s r c d else energy1 s r c d
@[expose] def threshold (k : Fin 2) (N : ℕ) : ℤ :=
  if k=0 then 20*(N:ℤ) else 28*(N:ℤ)
@[expose] def radiusR (k : Fin 2) (N : ℕ) : ℕ :=
  Nat.sqrt (if k=0 then 20*N/56 else 28*N/60)
@[expose] def radiusC (k : Fin 2) (N : ℕ) : ℕ :=
  Nat.sqrt (if k=0 then 60*N/4 else 196*N/10)
@[expose] def radiusD (k : Fin 2) (N : ℕ) : ℕ :=
  Nat.sqrt (if k=0 then 100*N/56 else 28*N/12)
@[expose] def sign (positive : Bool) (z : ℤ) : ℤ := if positive then z else -z
@[expose] def root (N : ℕ) (r c d : ℤ) : ℤ :=
  (Nat.sqrt (4*(N:ℤ)-210*r^2+5*c^2+42*d^2).toNat : ℤ)

/-- Coordinate radii follow from exact positive-square identities before
any search. They are adapted to each original norm, not uniform guesses. -/
theorem bounds_of_small (k : Fin 2) (N : ℕ) (s r c d : ℤ)
    (h : energy k s r c d<threshold k N) :
    r.natAbs≤radiusR k N ∧ c.natAbs≤radiusC k N ∧ d.natAbs≤radiusD k N := by
  fin_cases k
  · have ⟨hr,hc,hd⟩ := energy0_bounds s r c d
    simp only [energy,threshold,if_pos rfl] at h
    refine ⟨?_,?_,?_⟩
    · exact natAbs_bound r 56 (20*N) (by decide) (by push_cast; linarith)
    · exact natAbs_bound c 4 (60*N) (by decide) (by push_cast; linarith)
    · exact natAbs_bound d 56 (100*N) (by decide) (by push_cast; linarith)
  · have ⟨hr,hc,hd⟩ := energy1_bounds s r c d
    norm_num only [energy,threshold] at h
    refine ⟨?_,?_,?_⟩
    · exact natAbs_bound r 60 (28*N) (by decide) (by push_cast; linarith)
    · exact natAbs_bound c 10 (196*N) (by decide) (by push_cast; linarith)
    · exact natAbs_bound d 12 (28*N) (by decide) (by push_cast; linarith)

theorem sign_choice (z : ℤ) : ∃ b : Bool,sign b (z.natAbs:ℤ)=z := by
  rcases le_total 0 z with hp | hn
  · exact ⟨true,by simp [sign,Int.natCast_natAbs,abs_of_nonneg hp]⟩
  · exact ⟨false,by simp [sign,Int.natCast_natAbs,abs_of_nonpos hn]⟩

/-- The full original norm equation forces the remaining coordinate,
including both possible signs; square-root search loses no integer vector. -/
theorem root_forced (N : ℕ) (s r c d : ℤ)
    (h : s^2+210*r^2-5*c^2-42*d^2=4*(N:ℤ)) :
    root N r c d=(s.natAbs:ℤ) := by
  have he : 4*(N:ℤ)-210*r^2+5*c^2+42*d^2=s^2 := by linarith
  have hn : (s^2).toNat=s.natAbs^2 := by
    apply Int.ofNat_injective
    rw [Int.toNat_of_nonneg (sq_nonneg s)]
    simp only [Int.natCast_pow,Int.natCast_natAbs,sq_abs]
  simp only [root,he,hn,Nat.sqrt_eq']

/-- Exhaustive kernel calculation on the bounded three-coordinate boxes.
Norm positivity/support and the exact norm equation are checked, rather
than replacing the actual group by a finite sample of normalizers. -/
theorem bounded_minimum (i : Fin 16) (k : Fin 2)
    (r : Fin (radiusR k (allowedNorm i)+1))
    (c : Fin (radiusC k (allowedNorm i)+1))
    (d : Fin (radiusD k (allowedNorm i)+1)) (sr sc sd ss : Bool) :
    let R := sign sr (r.val:ℤ)
    let C := sign sc (c.val:ℤ)
    let D := sign sd (d.val:ℤ)
    let S := sign ss (root (allowedNorm i) R C D)
    S^2+210*R^2-5*C^2-42*D^2=4*(allowedNorm i:ℤ) →
      threshold k (allowedNorm i)≤energy k S R C D := by
  revert r c d sr sc sd ss
  fin_cases i <;> fin_cases k <;> decide

/-- All integral original coordinate vectors of any allowed norm satisfy
both representative vertex inequalities. No normalization hypothesis is
needed for this stronger whole-lattice statement. -/
theorem whole_integer_minimum (i : Fin 16) (k : Fin 2) (s r c d : ℤ)
    (h : s^2+210*r^2-5*c^2-42*d^2=4*(allowedNorm i:ℤ)) :
    threshold k (allowedNorm i)≤energy k s r c d := by
  by_contra hn
  have hlt := lt_of_not_ge hn
  obtain ⟨hr,hc,hd⟩ := bounds_of_small k (allowedNorm i) s r c d hlt
  obtain ⟨sr,hsr⟩ := sign_choice r
  obtain ⟨sc,hsc⟩ := sign_choice c
  obtain ⟨sd,hsd⟩ := sign_choice d
  obtain ⟨ss,hss⟩ := sign_choice s
  have hf := root_forced (allowedNorm i) s r c d h
  have hb := bounded_minimum i k ⟨r.natAbs,by omega⟩ ⟨c.natAbs,by omega⟩
    ⟨d.natAbs,by omega⟩ sr sc sd ss
  simp only [hsr,hsc,hsd,hf,hss] at hb
  exact hn (hb h)

theorem positive_divisor_cases (N : ℕ) (hN : 0<N) (hdiv : N∣210) :
    ∃ i : Fin 16,N=allowedNorm i := by
  have hle : N≤210 := Nat.le_of_dvd (by decide) hdiv
  interval_cases N <;> norm_num at hdiv
  all_goals decide
end NormalizerVertexEnergyMinimum318
