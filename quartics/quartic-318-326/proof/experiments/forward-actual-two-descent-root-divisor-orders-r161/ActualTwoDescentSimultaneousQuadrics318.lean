module
public import ActualTwoDescentRationalCover318
public import ActualTwoDescentPointExtraction318
public import ActualPreparedPoleSquarefreeClasses318
public section
noncomputable section
namespace ActualTwoDescentSimultaneousQuadrics318
open ActualTwoDescentRationalCover318 ActualTwoDescentPointExtraction318
open ActualPreparedPoleSquarefreeClasses318 TwoTwistPointRealization318

/-- A single rational point of three explicit quadrics. The third equation
is the SAME-parameter condition, not independent solvability of two covers.
The six nonzero coordinates retain exactly the original Kummer open locus. -/
structure Simultaneous (β θ : ℚ) where
  u : ℚ
  v : ℚ
  r : ℚ
  U : ℚ
  V : ℚ
  R : ℚ
  u_ne : u≠0
  v_ne : v≠0
  r_ne : r≠0
  U_ne : U≠0
  V_ne : V≠0
  R_ne : R≠0
  first : 4*r^2=β^2*u^2+3*β*v^2
  second : 4*R^2=β^2*U^2+3*β*V^2
  shared : β*U^2-V^2=θ*(β*u^2-v^2)

def Simultaneous.parameter {β θ : ℚ} (S : Simultaneous β θ) : ℚ :=
  (β*S.u^2-S.v^2)/4

def Simultaneous.firstCover {β θ : ℚ} (S : Simultaneous β θ) :
    Cover β S.parameter where
  u := S.u
  v := S.v
  r := S.r
  u_ne := S.u_ne
  v_ne := S.v_ne
  r_ne := S.r_ne
  first := by dsimp [Simultaneous.parameter]; ring
  second := by
    dsimp [Simultaneous.parameter]
    nlinarith [S.first]

def Simultaneous.secondCover {β θ : ℚ} (S : Simultaneous β θ) :
    Cover β (S.parameter*θ) where
  u := S.U
  v := S.V
  r := S.R
  u_ne := S.U_ne
  v_ne := S.V_ne
  r_ne := S.R_ne
  first := by
    dsimp [Simultaneous.parameter]
    nlinarith [S.shared]
  second := by
    have he := congrArg (fun q : ℚ => β*q) S.shared
    dsimp [Simultaneous.parameter]
    nlinarith [S.second,he]

/-- No existence is inferred: this is the algebraic elimination of the
common n from two GIVEN rational covers on n and n*theta. -/
def ofCovers {β θ n : ℚ} (P : Cover β n) (Q : Cover β (n*θ)) :
    Simultaneous β θ where
  u := P.u
  v := P.v
  r := P.r
  U := Q.u
  V := Q.v
  R := Q.r
  u_ne := P.u_ne
  v_ne := P.v_ne
  r_ne := P.r_ne
  U_ne := Q.u_ne
  V_ne := Q.v_ne
  R_ne := Q.r_ne
  first := by
    have he := congrArg (fun q : ℚ => β*q) P.first
    nlinarith [he,P.second]
  second := by
    have he := congrArg (fun q : ℚ => β*q) Q.first
    nlinarith [he,Q.second]
  shared := by
    rw [Q.first,P.first]
    ring

/-- Eliminating n is reversible: reconstruction returns the SAME n. -/
@[simp] theorem ofCovers_parameter {β θ n : ℚ}
    (P : Cover β n) (Q : Cover β (n*θ)) :
    (ofCovers P Q).parameter=n := by
  change (β*P.u^2-P.v^2)/4=n
  rw [P.first]
  ring

theorem simultaneous_iff_covers (β θ : ℚ) :
    Nonempty (Simultaneous β θ) ↔
      ∃ n : ℚ, Nonempty (Cover β n) ∧ Nonempty (Cover β (n*θ)) := by
  constructor
  · rintro ⟨S⟩
    exact ⟨S.parameter,⟨S.firstCover⟩,⟨S.secondCover⟩⟩
  · rintro ⟨n,⟨P⟩,⟨Q⟩⟩
    exact ⟨ofCovers P Q⟩

/-- The three quadrics are an exact concrete rational formulation of the
two original beta-class lifts. They do not assert either lift exists. -/
theorem simultaneous_iff_kummer (β θ : ℚ) (hβ : β≠0) :
    Nonempty (Simultaneous β θ) ↔
      ∃ n : ℚ, Nonempty (KummerPoint β n) ∧ Nonempty (KummerPoint β (n*θ)) := by
  constructor
  · rintro ⟨S⟩
    exact ⟨S.parameter,⟨S.firstCover.toKummer⟩,⟨S.secondCover.toKummer⟩⟩
  · rintro ⟨n,⟨P⟩,⟨Q⟩⟩
    exact ⟨ofCovers (ofKummer hβ P) (ofKummer hβ Q)⟩

/-- Construct the literal same-pole realization from concrete rational
coordinates; no Mordell-Weil, Sha, infinitude, or local-global theorem enters. -/
def realization {b : ℚ} (C : Classes b)
    (S : Simultaneous (C.beta:ℚ) (C.theta:ℚ)) : Realization b :=
  actual_realization_of_kummer b C.beta C.theta C.c C.d S.parameter
    (by exact_mod_cast (Nat.ne_of_gt C.beta_pos)) C.c_ne C.d_ne
    C.first_class C.second_class S.firstCover.toKummer S.secondCover.toKummer

/-- Four actual poles retain their original index; the auxiliary n may
differ per pole, while each pole's TWO twists share the reconstructed n. -/
def four_realizations (b : Fin 4 → ℚ) (C : ∀ i, Classes (b i))
    (S : ∀ i, Simultaneous ((C i).beta:ℚ) ((C i).theta:ℚ)) :
    ∀ i, Realization (b i) :=
  fun i => realization (C i) (S i)

end ActualTwoDescentSimultaneousQuadrics318
