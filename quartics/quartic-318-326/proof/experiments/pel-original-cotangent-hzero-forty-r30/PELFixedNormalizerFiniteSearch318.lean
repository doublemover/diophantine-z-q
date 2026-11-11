module
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Tactic
public section
namespace PELFixedNormalizerFiniteSearch318
set_option maxHeartbeats 12000000
set_option maxRecDepth 4096

@[expose] def norm : Fin 5 → ℕ := ![30,42,70,105,210]
/-- Absolute integral triples (r,|a|,|d|), before restoring independent
coordinate signs and the actual original polygon side identifications. -/
@[expose] def rows : Fin 5 → Finset (ℕ × ℕ × ℕ) := ![
  {(2,6,0),(3,6,5),(12,36,10),(13,36,15)},
  {(1,0,1),(13,42,1),(29,84,29),(41,126,29)},
  {(5,14,5),(9,28,5)},
  {(7,21,5),(8,21,10)},
  {(2,0,0),(3,0,5),(26,84,0),(39,84,65),(39,126,5),
   (72,210,70),(73,210,75),(96,294,70),(109,294,135),(109,336,75)}]

/-- Exactly the norm equation, parity of the original order coordinates,
original height bound, and ALL eight first-quadrant polygon rows after
clearing the positive denominator r. No branch-orbit assertion is input. -/
@[expose] def admissible (m r a d : ℕ) : Prop :=
  0<r ∧ 210*r^2≤40000*m ∧ (r+d)%2=0 ∧
  105*r^2=10*a^2+21*d^2+2*m ∧
  130*a≤420*r ∧ 170*a+45*d≤555*r ∧
  430*a+210*d≤1470*r ∧ 10*a+6*d≤35*r ∧
  290*a+210*d≤1050*r ∧ 20*a+17*d≤75*r ∧
  130*a+165*d≤555*r ∧ 3*d≤5*r
instance (m r a d : ℕ) : Decidable (admissible m r a d) :=
by
  unfold admissible
  infer_instance

@[expose] def candidateRoot (m r d : ℕ) : ℕ :=
  Nat.sqrt ((105*r^2-(21*d^2+2*m))/10)

/-- Square-root evaluation is merely an exhaustive-search optimization;
the norm equation forces this value for EVERY nonnegative a. -/
theorem forced_root (m r a d : ℕ) (h : admissible m r a d) :
    candidateRoot m r d=a := by
  have he := h.2.2.2.1
  have hn : (105*r^2-(21*d^2+2*m))/10=a^2 := by omega
  simp only [candidateRoot,hn,Nat.sqrt_eq']

/-- Closed finite kernel calculation over the bounded two-coordinate box.
The third coordinate is forced by the exact norm equation, not bounded
heuristically. There is no native-decide or external arithmetic oracle. -/
theorem bounded_search (i : Fin 5) (r : Fin 201) (d : Fin 334) :
    admissible (norm i) r (candidateRoot (norm i) r d) d →
    (r.val,candidateRoot (norm i) r d,d.val)∈rows i := by
  revert r d
  fin_cases i <;> decide

/-- Complete absolute-coordinate classification for all five norms,
without any primitivity assumption, genus bound or Riemann-Hurwitz input. -/
theorem exhaustive (i : Fin 5) (r a d : ℕ)
    (h : admissible (norm i) r a d) : (r,a,d)∈rows i := by
  have hm : norm i≤210 := by fin_cases i <;> norm_num [norm]
  have hr : r<201 := by nlinarith [h.2.1]
  have hd : d<334 := by have hh := h.2.2.2.2.2.2.2.2.2.2.2; omega
  have hs := bounded_search i ⟨r,hr⟩ ⟨d,hd⟩
  have he := forced_root (norm i) r a d h
  simpa only [he] using hs (by simpa only [he] using h)

/-- Every listed absolute triple satisfies all exact constraints. -/
theorem rows_admissible (i : Fin 5) :
    ∀ t∈rows i, admissible (norm i) t.1 t.2.1 t.2.2 := by
  fin_cases i <;> norm_num [rows,norm,admissible] <;> aesop
end PELFixedNormalizerFiniteSearch318
