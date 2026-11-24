module
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Tactic
public section

/-! On the complete characteristic-zero generic fibre, without invoking
Riemann–Hurwitz, computing a different, or knowing any twist constants.
The two affine charts may be pulled back along ANY map of smooth curves. -/
namespace OriginalCharacterHorizontal318
open Polynomial
variable {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]

def b (i : Fin 4) : ℚ := ![0,32,76832,-343] i
def P {A : Type*} [CommRing A] (t : A) : A := t*(t-32)*(t-76832)*(t+343)
def G {A : Type*} [CommRing A] (s : A) : A := (1-32*s)*(1-76832*s)*(1+343*s)
def linear0 {A : Type*} [CommRing A] (v : Fin 4 → A) : A :=
  2700000*v 0 - 2470629*v 1 + 5*v 2 - 229376*v 3
def linear1 {A : Type*} [CommRing A] (v : Fin 4 → A) : A :=
  -79060128*v 1 + 384160*v 2 + 78675968*v 3

omit [CharZero K] in
/-- The actual root (not merely a replacement differing by a sign)
belongs to each normal affine ring on which its square is regular. -/
theorem root_mem (R : Subalgebra ℚ K) [IsIntegrallyClosed R] [IsFractionRing R K]
    (z : K) (hz : z^2 ∈ R) : z ∈ R := by
  let a : R := ⟨z^2,hz⟩
  have h : IsIntegral R z := by
    refine ⟨X^2-C a,monic_X_pow_sub_C _ (by decide : 2 ≠ 0),?_⟩
    change aeval z (X^2-C a)=0
    rw [map_sub,map_pow,aeval_X,aeval_C]
    exact sub_self _
  obtain ⟨x,hx⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral h
  rw [←hx]
  exact x.property

omit [CharZero K] in
/-- A polynomial differentiation rule on the actual Kummer identity.
The only inverses used in the finite-chart regular representative are
constants. In particular no branch function is inverted in that chart. -/
private theorem root_read (D : Derivation ℚ K K) (t z : K) (a c : ℚ)
    (hc : algebraMap ℚ K c ≠ 0) (ha : t-algebraMap ℚ K a ≠ 0)
    (hz : z^2=algebraMap ℚ K c*(t-algebraMap ℚ K a)) :
    4*(D z)^2/algebraMap ℚ K c=(D t)^2/(t-algebraMap ℚ K a) := by
  let C := algebraMap ℚ K c
  have hd : 2*z*D z=C*D t := by
    have h := congrArg D hz
    simp only [pow_two,Derivation.leibniz,map_sub,D.map_algebraMap,sub_zero,
      smul_eq_mul] at h
    change 2*z*D z=algebraMap ℚ K c*D t
    linear_combination h
  apply (eq_div_iff ha).2
  apply mul_left_cancel₀ (pow_ne_zero 2 hc)
  calc
    _ = 4*(D z)^2*(algebraMap ℚ K c*(t-algebraMap ℚ K a)) := by field_simp [hc]
    _ = (2*z*D z)^2 := by rw [←hz]; ring
    _ = _ := by rw [hd,mul_pow]

/-- The two unscaled original coefficients on the finite t-chart,
as linear combinations of squares of DIFFERENTIALS OF REGULAR ROOTS.
No assumption about an unramified point or a chosen local parameter. -/
theorem finite_chart (R : Subalgebra ℚ K) [IsIntegrallyClosed R] [IsFractionRing R K]
    (D : Derivation ℚ K K) (dR : ∀ x ∈ R, D x ∈ R) (t : K) (ht : t ∈ R)
    (r : Fin 4 → K) (c : Fin 4 → ℚˣ)
    (h : ∀ i,r i^2=algebraMap ℚ K (c i : ℚ)*(t-algebraMap ℚ K (b i)))
    (hne : ∀ i,t-algebraMap ℚ K (b i) ≠ 0) :
    (D t)^2/P t ∈ R ∧ t*(D t)^2/P t ∈ R := by
  let v : Fin 4 → K := fun i => 4*(D (r i))^2/algebraMap ℚ K (c i : ℚ)
  have ri (i : Fin 4) : r i ∈ R := root_mem R _ (by
    rw [h i]; exact R.mul_mem (R.algebraMap_mem _) (R.sub_mem ht (R.algebraMap_mem _)))
  have vi (i : Fin 4) : v i ∈ R := by
    change 4*(D (r i))^2/algebraMap ℚ K (c i : ℚ) ∈ R
    rw [div_eq_mul_inv,←map_inv₀]
    exact R.mul_mem (R.mul_mem (R.natCast_mem 4) (R.pow_mem (dR _ (ri i)) 2)) (R.algebraMap_mem _)
  have ve (i : Fin 4) : v i=(D t)^2/(t-algebraMap ℚ K (b i)) :=
    root_read D t (r i) _ _ ((map_ne_zero (algebraMap ℚ K)).mpr (c i).ne_zero) (hne i) (h i)
  let L : ℚ := 2276931686400000
  have regs : linear0 v * algebraMap ℚ K L⁻¹ ∈ R ∧ linear1 v * algebraMap ℚ K L⁻¹ ∈ R := by
    constructor
    · apply R.mul_mem _ (R.algebraMap_mem _)
      unfold linear0
      exact R.sub_mem (R.add_mem (R.sub_mem (R.mul_mem (R.natCast_mem 2700000) (vi 0))
        (R.mul_mem (R.natCast_mem 2470629) (vi 1))) (R.mul_mem (R.natCast_mem 5) (vi 2)))
        (R.mul_mem (R.natCast_mem 229376) (vi 3))
    · apply R.mul_mem _ (R.algebraMap_mem _)
      unfold linear1
      exact R.add_mem (R.add_mem (R.mul_mem (R.neg_mem (R.natCast_mem 79060128)) (vi 1))
        (R.mul_mem (R.natCast_mem 384160) (vi 2))) (R.mul_mem (R.natCast_mem 78675968) (vi 3))
  have h0 : t ≠ 0 := by simpa [b] using hne 0
  have h1 : t-32 ≠ 0 := by simpa [b] using hne 1
  have h2 : t-76832 ≠ 0 := by simpa [b] using hne 2
  have h3 : t+343 ≠ 0 := by simpa [b] using hne 3
  have row : linear0 v * algebraMap ℚ K L⁻¹=(D t)^2/P t ∧
      linear1 v * algebraMap ℚ K L⁻¹=t*(D t)^2/P t := by
    constructor <;> simp only [linear0,linear1,ve] <;> norm_num [L,b,P] <;>
      field_simp [h0,h1,h2,h3] <;> ring
  rwa [row.1,row.2] at regs

omit [CharZero K] in
/-- At infinity one regular half-coordinate suffices: z²=(1/t)/c.
Where G(1/t) is a unit these equations contain no division by 1/t.
The numerators vanish to the requisite order even before choosing a
parameter at infinity. -/
theorem infinity_chart (R : Subalgebra ℚ K) [IsIntegrallyClosed R] [IsFractionRing R K]
    (D : Derivation ℚ K K) (dR : ∀ x ∈ R, D x ∈ R) (t : K) (ht : t≠0)
    (hs : t⁻¹ ∈ R) (hG : (G t⁻¹)⁻¹ ∈ R) (hzG : G t⁻¹ ≠ 0) (r : K) (c : ℚˣ)
    (hr : r^2=algebraMap ℚ K (c:ℚ)*t) :
    (D t)^2/P t ∈ R ∧ t*(D t)^2/P t ∈ R := by
  let C := algebraMap ℚ K (c:ℚ)
  have hc : C≠0 := (map_ne_zero (algebraMap ℚ K)).mpr c.ne_zero
  let z := r⁻¹
  have he : z^2=algebraMap ℚ K ((c:ℚ)⁻¹)*t⁻¹ := by
    dsimp [z]; rw [inv_pow,hr,mul_inv_rev,map_inv₀,mul_comm]
  have zreg : z ∈ R := root_mem R z (by rw [he]; exact R.mul_mem (R.algebraMap_mem _) hs)
  have hsz : t⁻¹=C*z^2 := by rw [he,map_inv₀]; change t⁻¹=C*(C⁻¹*t⁻¹); field_simp [hc]
  have hder : -t⁻¹^2*D t=2*C*z*D z := by
    have h := congrArg D hsz
    simp only [Derivation.leibniz_inv,Derivation.leibniz,pow_two,D.map_algebraMap,
      smul_eq_mul,C] at h
    dsimp [C]
    linear_combination h
  have hp : P t=t^4*G t⁻¹ := by unfold P G; field_simp [ht]
  have hh : (t⁻¹)^4*(D t)^2=4*C*t⁻¹*(D z)^2 := by
    calc _ = (-t⁻¹^2*D t)^2 := by ring
         _ = 4*C*(C*z^2)*(D z)^2 := by rw [hder]; ring
         _ = _ := by rw [←hsz]
  have dd : (D t)^2=4*C*(D z)^2*t^3 := by
    calc _ = t^4*((t⁻¹)^4*(D t)^2) := by field_simp [ht]
         _ = _ := by rw [hh]; field_simp [ht]
  have eqt : t*(D t)^2/P t=4*C*(D z)^2*(G t⁻¹)⁻¹ := by
    rw [hp,dd]; field_simp [ht,hzG]
  have eq0 : (D t)^2/P t=t⁻¹*(t*(D t)^2/P t) := by
    rw [←mul_div_assoc,←mul_assoc,inv_mul_cancel₀ ht,one_mul]
  have reg1 : 4*C*(D z)^2*(G t⁻¹)⁻¹ ∈ R :=
    R.mul_mem (R.mul_mem (R.mul_mem (R.natCast_mem 4) (R.algebraMap_mem _))
      (R.pow_mem (dR _ zreg) 2)) hG
  exact ⟨by rw [eq0,eqt]; exact R.mul_mem hs reg1,by rwa [eqt]⟩

end OriginalCharacterHorizontal318
