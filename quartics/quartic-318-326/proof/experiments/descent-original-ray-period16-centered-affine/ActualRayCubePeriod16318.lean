module
public import Mathlib
public section
noncomputable section
namespace ActualRayCubePeriod16318

open scoped BigOperators

@[expose] def axisPeriod (q : ℕ) : ℕ := 16/(Nat.gcd 16 q)

theorem axisPeriod_le (q : ℕ) : axisPeriod q≤16 := Nat.div_le_self _ _

theorem axisPeriod_pos (q : ℕ) : 0<axisPeriod q :=
  Nat.div_gcd_pos_of_pos_left q (by decide)

theorem axisPeriod_mul (q : ℕ) : 16∣q*axisPeriod q := by
  let d := Nat.gcd 16 q
  have h₁ : d*axisPeriod q=16 := by
    rw [Nat.mul_comm]
    exact Nat.div_mul_cancel (Nat.gcd_dvd_left 16 q)
  have h₂ : d*(q/d)=q := by
    rw [Nat.mul_comm]
    exact Nat.div_mul_cancel (Nat.gcd_dvd_right 16 q)
  refine ⟨q/d,?_⟩
  calc
    q*axisPeriod q=(d*(q/d))*axisPeriod q := by rw [h₂]
    _=(d*axisPeriod q)*(q/d) := by ring
    _=_ := by rw [h₁]

theorem scaled_axis {q : ℕ} {t t₀ : ℤ}
    (h : t≡t₀ [ZMOD (axisPeriod q:ℤ)]) :
    (q:ℤ)*t≡(q:ℤ)*t₀ [ZMOD 16] := by
  have hd : (16:ℤ)∣(q:ℤ)*(axisPeriod q:ℤ) := by exact_mod_cast axisPeriod_mul q
  exact Int.ModEq.of_dvd hd (h.mul_left' (q:ℤ))

theorem scaled_axis_reverse {q : ℕ} {t t₀ : ℤ}
    (h : (q:ℤ)*t≡(q:ℤ)*t₀ [ZMOD 16]) :
    t≡t₀ [ZMOD (axisPeriod q:ℤ)] := by
  have h' := Int.ModEq.cancel_left_div_gcd (show (0:ℤ)<16 by decide) h
  rw [show Int.gcd (16:ℤ) (q:ℤ)=Nat.gcd 16 q from Int.gcd_natCast_natCast _ _] at h'
  exact h'

/-- The actual squarefree wheel has exactly one copy of 2. Output
class 17 mod32 thus singles out one canonical x residue mod16. -/
theorem wheel32_argument_unique (V : ℕ) (hc : V.Coprime 2) {x x₀ b : ℤ}
    (h : ((2*V:ℕ):ℤ)*x+b≡((2*V:ℕ):ℤ)*x₀+b [ZMOD 32]) :
    x≡x₀ [ZMOD 16] := by
  have h16 : (16:ℕ).Coprime V := by
    simpa only [show 2^4=(16:ℕ) by decide] using hc.symm.pow_left 4
  have hg : Nat.gcd 32 (2*V)=2 := by
    change Nat.gcd (2*16) (2*V)=2
    rw [Nat.gcd_mul_left,h16.gcd_eq_one,mul_one]
  have hh := Int.ModEq.cancel_left_div_gcd (show (0:ℤ)<32 by decide)
    (Int.ModEq.add_right_cancel' b h)
  rw [show Int.gcd (32:ℤ) ((2*V:ℕ):ℤ)=2 from
    (Int.gcd_natCast_natCast 32 (2*V)).trans hg] at hh
  exact hh

/-- At most ONE residue cell survives the actual norm-17 selector
inside any fixed wrapped affine cell. Comparing two candidate
points, the zero vertex determines x mod16, and each single-axis
vertex determines its t_j mod axisPeriod. -/
theorem surviving_cell_unique {J : Type*} (V q n : ℕ) (hc : V.Coprime 2)
    (b w₀ x x₀ : ℤ) (w t t₀ : J→ℤ)
    (hx : ((2*V:ℕ):ℤ)*(x-w₀*(n:ℤ))+b≡(17:ℤ) [ZMOD 32])
    (hx₀ : ((2*V:ℕ):ℤ)*(x₀-w₀*(n:ℤ))+b≡(17:ℤ) [ZMOD 32])
    (ht : ∀ i,((2*V:ℕ):ℤ)*(x+(q:ℤ)*t i-w i*(n:ℤ))+b≡(17:ℤ) [ZMOD 32])
    (ht₀ : ∀ i,((2*V:ℕ):ℤ)*(x₀+(q:ℤ)*t₀ i-w i*(n:ℤ))+b≡(17:ℤ) [ZMOD 32]) :
    x≡x₀ [ZMOD 16] ∧ ∀ i,t i≡t₀ i [ZMOD (axisPeriod q:ℤ)] := by
  have hx' := (wheel32_argument_unique V hc (hx.trans hx₀.symm)).add_right (w₀*(n:ℤ))
  have hx'' : x≡x₀ [ZMOD 16] := by simpa only [sub_add_cancel] using hx'
  refine ⟨hx'',fun i => ?_⟩
  have hi := (wheel32_argument_unique V hc ((ht i).trans (ht₀ i).symm)).add_right (w i*(n:ℤ))
  have hi' : x+(q:ℤ)*t i≡x₀+(q:ℤ)*t₀ i [ZMOD 16] := by
    simpa only [sub_add_cancel] using hi
  exact scaled_axis_reverse (hx''.add_left_cancel hi')

theorem sum_modEq {J : Type*} (S : Finset J) (F : ℤ) (a b : J→ℤ)
    (h : ∀ j∈S,a j≡b j [ZMOD F]) :
    (∑ j∈S,a j)≡(∑ j∈S,b j) [ZMOD F] := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,Int.ModEq.rfl]
  | @insert j S hj ih =>
    rw [Finset.sum_insert hj,Finset.sum_insert hj]
    exact (h j (Finset.mem_insert_self _ _)).add (ih
      (fun k hk => h k (Finset.mem_insert_of_mem hk)))

@[expose] def vertex {a : ℕ} (n q W : ℕ) (b w x : ℤ) (t : Fin a→ℤ)
    (ω : Fin a→Bool) : ℤ :=
  (W:ℤ)*(x+(q:ℤ)*(∑ j : Fin a,if ω j then t j else 0)-w*(n:ℤ))+b

/-- Exact residue needed by a fixed wrapped affine cube vertex. Only
x mod 16 and the DIFFERENCES h_j−h'_j mod 16/gcd(16,q) are used.
The wrapping integer stays fixed on each convex wrapping cell. -/
theorem vertex_same_conductor {a F W n q : ℕ} (hF : F∣W*16)
    (b w x x₀ : ℤ) (t t₀ : Fin a→ℤ) (ω : Fin a→Bool)
    (hx : x≡x₀ [ZMOD 16]) (ht : ∀ j,t j≡t₀ j [ZMOD (axisPeriod q:ℤ)]) :
    vertex n q W b w x t ω ≡ vertex n q W b w x₀ t₀ ω [ZMOD (F:ℤ)] := by
  have hs : ((q:ℤ)*(∑ j : Fin a,if ω j then t j else 0))≡
      ((q:ℤ)*(∑ j : Fin a,if ω j then t₀ j else 0)) [ZMOD 16] := by
    simp only [Finset.mul_sum]
    apply sum_modEq
    intro j _
    split_ifs with h
    · exact scaled_axis (ht j)
    · exact Int.ModEq.rfl
  have hh := (hx.add hs).sub_right (w*(n:ℤ))
  have hd : (F:ℤ)∣(W:ℤ)*16 := by exact_mod_cast hF
  exact (Int.ModEq.of_dvd hd (hh.mul_left' (W:ℤ))).add_right b

theorem vertex_same_mean {a F W n q : ℕ} (hF : F∣W*16) (μ : ℤ→ℝ)
    (b w x x₀ : ℤ) (t t₀ : Fin a→ℤ) (ω : Fin a→Bool)
    (hx : x≡x₀ [ZMOD 16]) (ht : ∀ j,t j≡t₀ j [ZMOD (axisPeriod q:ℤ)]) :
    μ (vertex n q W b w x t ω%(F:ℤ))=
      μ (vertex n q W b w x₀ t₀ ω%(F:ℤ)) :=
  congrArg μ (vertex_same_conductor hF b w x x₀ t t₀ ω hx ht)

/-- An exact unimodular variable change. The second tuple is retained;
the normalization and the multiplicity of differences do not change. -/
def differenceCoordinates (a : ℕ) :
    ((Fin a→ℤ)×(Fin a→ℤ)) ≃ ((Fin a→ℤ)×(Fin a→ℤ)) where
  toFun H := (fun j => H.1 j-H.2 j,H.2)
  invFun Z := (fun j => Z.1 j+Z.2 j,Z.2)
  left_inv H := Prod.ext (funext fun j => sub_add_cancel (H.1 j) (H.2 j)) rfl
  right_inv Z := Prod.ext (funext fun j => add_sub_cancel_right (Z.1 j) (Z.2 j)) rfl

theorem refinement_card (a q : ℕ) :
    Nat.card (ZMod 16 × (Fin a→ZMod (axisPeriod q)))=16*(axisPeriod q)^a := by
  letI : NeZero (axisPeriod q) := ⟨(axisPeriod_pos q).ne'⟩
  simp only [Nat.card_eq_fintype_card,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,ZMod.card]

end ActualRayCubePeriod16318
