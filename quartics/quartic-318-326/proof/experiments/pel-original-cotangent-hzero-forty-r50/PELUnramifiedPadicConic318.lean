module
public import PELUnramifiedFiniteConic318
public import Mathlib.NumberTheory.Padics.Hensel
public section
noncomputable section
namespace PELUnramifiedPadicConic318
open Polynomial
set_option maxHeartbeats 1200000
variable {p : ℕ} [Fact p.Prime]

theorem reduction_zero_iff (x : ℤ_[p]) :
    PadicInt.toZMod x=0 ↔ ‖x‖<1 := by
  rw [←RingHom.mem_ker,PadicInt.ker_toZMod,
    IsLocalRing.mem_maximalIdeal,PadicInt.mem_nonunits]

theorem reduction_ne_norm (x : ℤ_[p]) (hx : PadicInt.toZMod x≠0) : ‖x‖=1 := by
  apply le_antisymm (PadicInt.norm_le_one x)
  exact le_of_not_gt (fun h => hx ((reduction_zero_iff x).mpr h))

/-- A genuine Hensel application to a weighted square. Both the residual
equation and the derivative unit are verified in the actual residue field. -/
theorem lift_weighted_square (A B u : ℤ_[p])
    (hzero : PadicInt.toZMod (A*u^2-B)=0)
    (hderiv : PadicInt.toZMod (2*A*u)≠0) :
    ∃ z : ℤ_[p], A*z^2=B := by
  let F : Polynomial ℤ_[p] := C A*X^2-C B
  have hvalue : F.aeval u=A*u^2-B := by simp [F]
  have hderivative : F.derivative.aeval u=2*A*u := by simp [F] <;> ring
  have hn : ‖F.aeval u‖<‖F.derivative.aeval u‖^2 := by
    rw [hvalue,hderivative,reduction_ne_norm _ hderiv,one_pow]
    exact (reduction_zero_iff _).mp hzero
  obtain ⟨z,hz,_⟩ := hensels_lemma hn
  refine ⟨z,?_⟩
  have : A*z^2-B=0 := by simpa [F] using hz
  exact sub_eq_zero.mp this

/-- At every prime outside210 the ORIGINAL conic has a point in the actual
p-adic integers. The proof chooses a nonzero derivative from the finite point
and holds the other coordinate fixed during its Hensel lift. -/
theorem integral_conic (p : ℕ) [Fact p.Prime] (hp210 : ¬p ∣ 210) :
    ∃ x y : ℤ_[p], x^2+210*y^2=5 := by
  obtain ⟨r,s,hrs,hr|hs⟩ := PELUnramifiedFiniteConic318.finite_smooth_conic p hp210
  · obtain ⟨a,ha⟩ := ZMod.ringHom_surjective (PadicInt.toZMod : ℤ_[p]→+*ZMod p) r
    obtain ⟨b,hb⟩ := ZMod.ringHom_surjective (PadicInt.toZMod : ℤ_[p]→+*ZMod p) s
    have hzero : PadicInt.toZMod (1*a^2-(5-210*b^2))=0 := by
      simp only [map_sub,map_mul,map_pow,map_one,map_ofNat,ha,hb]
      linear_combination hrs
    have hd : PadicInt.toZMod (2*(1:ℤ_[p])*a)≠0 := by
      simpa only [map_mul,map_ofNat,map_one,ha,mul_one] using hr
    obtain ⟨x,hx⟩ := lift_weighted_square 1 (5-210*b^2) a hzero hd
    refine ⟨x,b,?_⟩
    linear_combination hx
  · obtain ⟨a,ha⟩ := ZMod.ringHom_surjective (PadicInt.toZMod : ℤ_[p]→+*ZMod p) r
    obtain ⟨b,hb⟩ := ZMod.ringHom_surjective (PadicInt.toZMod : ℤ_[p]→+*ZMod p) s
    have hzero : PadicInt.toZMod (210*b^2-(5-a^2))=0 := by
      simp only [map_sub,map_mul,map_pow,map_ofNat,ha,hb]
      linear_combination hrs
    have hd : PadicInt.toZMod (2*(210:ℤ_[p])*b)≠0 := by
      simpa only [map_mul,map_ofNat,hb,show (2:ZMod p)*210=420 by norm_num] using hs
    obtain ⟨y,hy⟩ := lift_weighted_square 210 (5-a^2) b hzero hd
    refine ⟨a,y,?_⟩
    linear_combination hy

theorem field_conic (p : ℕ) [Fact p.Prime] (hp210 : ¬p ∣ 210) :
    ∃ x y : ℚ_[p], x^2+210*y^2=5 := by
  obtain ⟨x,y,h⟩ := integral_conic p hp210
  exact ⟨x,y,by exact_mod_cast h⟩
end PELUnramifiedPadicConic318
