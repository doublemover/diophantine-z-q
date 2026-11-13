module
public import FiniteAnchorIsotropy318
public section
noncomputable section
namespace PadicAnchorUniversality318
open Polynomial
set_option maxHeartbeats 1000000

/-- An actual isotropic p-adic vector whose third coordinate is a unit is
lifted at every p≥5. The derivative−4 excludes exactly the already handled2. -/
theorem isotropic_vector (p : ℕ) [Fact p.Prime] (hp : 5≤p) :
    ∃ x y z : ℚ_[p], z≠0 ∧ x^2+6*y^2-2*z^2=0 := by
  obtain ⟨x,y,hdiv⟩ := FiniteAnchorIsotropy318.integer_lifts p hp
  let F : Polynomial ℤ_[p] := C ((x:ℤ_[p])^2+6*(y:ℤ_[p])^2)-C 2*X^2
  have heval : F.aeval (1:ℤ_[p])=((x^2+6*y^2-2:ℤ):ℤ_[p]) := by
    simp [F]
  have hderiv : F.derivative.aeval (1:ℤ_[p])= -(4:ℤ_[p]) := by
    simp [F] <;> ring
  have hp4 : ¬p∣4 := fun h => by have hh := Nat.le_of_dvd (by norm_num : 0<4) h; omega
  have hcop : Nat.Coprime p 4 := (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr hp4
  have hnorm4 : ‖(4:ℤ_[p])‖=1 := PadicInt.norm_natCast_eq_one_iff.mpr hcop
  have hder : ‖F.derivative.aeval (1:ℤ_[p])‖=1 := by rw [hderiv,norm_neg,hnorm4]
  have hres : ‖F.aeval (1:ℤ_[p])‖<1 := by
    rw [heval]
    exact PadicInt.norm_intCast_lt_one_iff.mpr hdiv
  have hnorm : ‖F.aeval (1:ℤ_[p])‖< ‖F.derivative.aeval (1:ℤ_[p])‖^2 := by
    rw [hder]
    simpa using hres
  obtain ⟨z,hz,hclose,_⟩ := hensels_lemma hnorm
  have hz0 : z≠0 := by
    intro he
    rw [hder] at hclose
    simpa [he] using hclose
  have hc : (x:ℤ_[p])^2+6*(y:ℤ_[p])^2-2*z^2=0 := by simpa [F] using hz
  refine ⟨(x:ℚ_[p]),(y:ℚ_[p]),(z:ℚ_[p]),?_,?_⟩
  · intro he
    apply hz0
    exact PadicInt.ext (by simpa using he)
  · exact_mod_cast hc

/-- Explicit hyperbolic line through the produced isotropic vector. It
represents every target, including targets divisible byp or with p-poles. -/
lemma represent_of_isotropic {F : Type*} [Field F] [CharZero F]
    (x y z c : F) (hz : z≠0) (hq : x^2+6*y^2-2*z^2=0) :
    ∃ X Y Z : F, X^2+6*Y^2-2*Z^2=c := by
  let t := -(c+2)/(4*z)
  have hd : (4:F)*z≠0 := mul_ne_zero (by norm_num) hz
  have ht : 4*z*t= -(c+2) := by dsimp [t]; field_simp [hz]
  refine ⟨t*x,t*y,1+t*z,?_⟩
  linear_combination t^2*hq-ht

/-- Genuine local universality at every prime beyond2,3, not merely the
finite set selected by the source's contact-prime argument. -/
theorem represents (p : ℕ) [Fact p.Prime] (hp : 5≤p) (c : ℚ_[p]) :
    ∃ x y z : ℚ_[p], x^2+6*y^2-2*z^2=c := by
  obtain ⟨x,y,z,hz,hq⟩ := isotropic_vector p hp
  exact represent_of_isotropic x y z c hz hq

end PadicAnchorUniversality318
