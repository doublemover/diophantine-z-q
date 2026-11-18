module
public import ActualTwoDescentSimultaneousQuadrics318
public section
noncomputable section
namespace ActualTwoDescentParametricCover318
open ActualTwoDescentRationalCover318 ActualTwoDescentPointExtraction318
open ActualPreparedPoleSquarefreeClasses318 TwoTwistPointRealization318

def quartic (β t : ℚ) : ℚ := (t^2-β)*(t^2-9*β)

def parameter (β t : ℚ) : ℚ := quartic β t/(4*β)

/-- The open locus is explicit, rather than absorbed into a generic-point
assumption. These conditions ensure exactly the three cover coordinates
are nonzero. They do not assert the simultaneous quartic equation. -/
structure Admissible (β t : ℚ) : Prop where
  parameter_ne : t≠0
  minus_ne : t^2-3*β≠0
  plus_ne : t^2+3*β≠0

/-- The retained beta-cover has this exact rational parametric FAMILY as
n varies. It is not a point construction at an arbitrarily preassigned n. -/
def parametricCover (β t : ℚ) (hβ : β≠0) (ht : Admissible β t) :
    Cover β (parameter β t) where
  u := (t^2-3*β)/β
  v := 2*t
  r := (t^2+3*β)/2
  u_ne := div_ne_zero ht.minus_ne hβ
  v_ne := mul_ne_zero (by norm_num) ht.parameter_ne
  r_ne := div_ne_zero ht.plus_ne (by norm_num)
  first := by
    dsimp [parameter,quartic]
    field_simp [hβ] <;> ring
  second := by
    dsimp [parameter,quartic]
    field_simp [hβ] <;> ring

/-- Scaling the actual rational coordinates scales the original twist n
by precisely k^2, while retaining beta. -/
def scaleCover {β n : ℚ} (k : ℚ) (hk : k≠0) (P : Cover β n) :
    Cover β (k^2*n) where
  u := k*P.u
  v := k*P.v
  r := k*P.r
  u_ne := mul_ne_zero hk P.u_ne
  v_ne := mul_ne_zero hk P.v_ne
  r_ne := mul_ne_zero hk P.r_ne
  first := by
    calc
      β*(k*P.u)^2-(k*P.v)^2=k^2*(β*P.u^2-P.v^2) := by ring
      _=k^2*(4*n) := by rw [P.first]
      _=4*(k^2*n) := by ring
  second := by
    calc
      (k*P.r)^2-β*(k*P.v)^2=k^2*(P.r^2-β*P.v^2) := by ring
      _=k^2*(β*n) := by rw [P.second]
      _=β*(k^2*n) := by ring

/-- The ONE remaining simultaneous rational equation supplies the second
cover on exactly n*theta. Both sides use the same beta quartic. -/
def secondCover (β θ t T k : ℚ) (hβ : β≠0) (hk : k≠0)
    (hT : Admissible β T)
    (hshared : k^2*quartic β T=θ*quartic β t) :
    Cover β (parameter β t*θ) := by
  have hn : k^2*parameter β T=parameter β t*θ := by
    dsimp [parameter]
    calc
      k^2*(quartic β T/(4*β))=(k^2*quartic β T)/(4*β) := by ring
      _=(θ*quartic β t)/(4*β) := by rw [hshared]
      _=quartic β t/(4*β)*θ := by ring
  exact hn ▸ scaleCover k hk (parametricCover β T hβ hT)

/-- Direct rank-free construction at the literal pole from a rational
point of k² F_beta(T)=theta F_beta(t), with the open locus explicit.
This remains a conditional construction, NOT an existence theorem. -/
def realization {b : ℚ} (C : Classes b) (t T k : ℚ)
    (hk : k≠0) (ht : Admissible (C.beta:ℚ) t)
    (hT : Admissible (C.beta:ℚ) T)
    (hshared : k^2*quartic (C.beta:ℚ) T=(C.theta:ℚ)*quartic (C.beta:ℚ) t) :
    Realization b := by
  have hβ : (C.beta:ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt C.beta_pos)
  exact actual_realization_of_kummer b C.beta C.theta C.c C.d
    (parameter C.beta t) hβ C.c_ne C.d_ne C.first_class C.second_class
    (parametricCover C.beta t hβ ht).toKummer
    (secondCover C.beta C.theta t T k hβ hk hT hshared).toKummer

def four_realizations (b : Fin 4 → ℚ) (C : ∀ i, Classes (b i))
    (t T k : Fin 4 → ℚ) (hk : ∀ i, k i≠0)
    (ht : ∀ i, Admissible ((C i).beta:ℚ) (t i))
    (hT : ∀ i, Admissible ((C i).beta:ℚ) (T i))
    (hshared : ∀ i, (k i)^2*quartic ((C i).beta:ℚ) (T i)=
      ((C i).theta:ℚ)*quartic ((C i).beta:ℚ) (t i)) :
    ∀ i, Realization (b i) :=
  fun i => realization (C i) (t i) (T i) (k i) (hk i) (ht i) (hT i) (hshared i)

end ActualTwoDescentParametricCover318
