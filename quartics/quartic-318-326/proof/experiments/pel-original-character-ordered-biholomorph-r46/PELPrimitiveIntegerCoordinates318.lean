module
public import PELNormalizerQuadraticCertificates318
public import Mathlib.Data.Int.GCD
public section
noncomputable section
namespace PELPrimitiveIntegerCoordinates318
open PELPrincipalOrderCoordinates318
open scoped BigOperators
set_option maxHeartbeats 1600000

/-- Full four-coordinate primitive normalization, with an actual integer
Bezout witness. Zero coordinates and arbitrary signs are allowed. -/
theorem primitive_coordinates (a : Coordinates) (ha : a≠0) :
    ∃ (g : ℤ) (b z : Coordinates),g≠0 ∧ (∀ i,a i=g*b i) ∧ ∑ i : Fin 4,z i*b i=1 := by
  let d := Int.gcd (a 0) (a 1)
  let e := Int.gcd (a 2) (a 3)
  let g := Nat.gcd d e
  have hgd : (g:ℤ)∣(d:ℤ) := Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left d e)
  have hge : (g:ℤ)∣(e:ℤ) := Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right d e)
  have hd0 : (d:ℤ)∣a 0 := Int.gcd_dvd_left _ _
  have hd1 : (d:ℤ)∣a 1 := Int.gcd_dvd_right _ _
  have he2 : (e:ℤ)∣a 2 := Int.gcd_dvd_left _ _
  have he3 : (e:ℤ)∣a 3 := Int.gcd_dvd_right _ _
  have hdiv (i : Fin 4) : (g:ℤ)∣a i := by
    fin_cases i
    · exact hgd.trans hd0
    · exact hgd.trans hd1
    · exact hge.trans he2
    · exact hge.trans he3
  choose b hb using hdiv
  have hg : (g:ℤ)≠0 := by
    intro hz
    apply ha
    funext i
    rw [hb i,hz,zero_mul] <;> rfl
  let z : Coordinates := ![
    Nat.gcdA d e*Int.gcdA (a 0) (a 1),
    Nat.gcdA d e*Int.gcdB (a 0) (a 1),
    Nat.gcdB d e*Int.gcdA (a 2) (a 3),
    Nat.gcdB d e*Int.gcdB (a 2) (a 3)]
  have hz : ∑ i : Fin 4,z i*a i=(g:ℤ) := by
    have h0 := Int.gcd_eq_gcd_ab (a 0) (a 1)
    have h1 := Int.gcd_eq_gcd_ab (a 2) (a 3)
    have h2 := Nat.gcd_eq_gcd_ab d e
    change (d:ℤ)=_ at h0
    change (e:ℤ)=_ at h1
    change (g:ℤ)=_ at h2
    simp only [Fin.sum_univ_succ]
    dsimp [z]
    rw [h2,h0,h1]
    ring
  refine ⟨g,b,z,hg,hb,?_⟩
  apply mul_left_cancel₀ hg
  calc
    (g:ℤ)*(∑ i : Fin 4,z i*b i)=∑ i : Fin 4,z i*((g:ℤ)*b i) := by
      simp only [Fin.sum_univ_succ]
      ring
    _ = ∑ i : Fin 4,z i*a i := by simp only [←hb]
    _ = (g:ℤ)*1 := hz.trans (mul_one _).symm
end PELPrimitiveIntegerCoordinates318
