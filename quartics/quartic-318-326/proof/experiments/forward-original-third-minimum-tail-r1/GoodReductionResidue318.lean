module
public import SelectedRayEmbeddings318
public import Mathlib.NumberTheory.Padics.RingHoms
public section
noncomputable section
namespace GoodReductionResidue318
open Polynomial
set_option maxHeartbeats 1000000
variable (p : ℕ) [Fact p.Prime]

lemma residue_zero (x : ℤ_[p]) : PadicInt.toZMod x=0 ↔ ‖x‖<1 := by
  rw [←RingHom.mem_ker,PadicInt.ker_toZMod,PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton,←PadicInt.norm_lt_one_iff_dvd]

lemma residue_equal (x y : ℤ_[p]) : PadicInt.toZMod x=PadicInt.toZMod y ↔ ‖x-y‖<1 := by
  rw [←sub_eq_zero,←map_sub,residue_zero]

lemma residue_unit (x : ℤ_[p]) : PadicInt.toZMod x≠0 ↔ ‖x‖=1 := by
  rw [ne_eq,residue_zero]
  exact ⟨fun h => le_antisymm (PadicInt.norm_le_one x) (le_of_not_gt h),
    fun h => by rw [h]; exact lt_irrefl _⟩

lemma smooth_residue {F : Type*} [Field F] (D x y : F) (h2 : (2:F)≠0)
    (hD : D≠0) (hc : y^2=x^3-D*x) : 2*y≠0 ∨ 3*x^2-D≠0 := by
  by_cases hy : y=0
  · right
    intro hg
    have he : 4*D^3=(4*D-3*x^2)*(3*x^2-D)^2+27*y^4 := by
      linear_combination -27*(y^2+x^3-D*x)*hc
    have hz : 4*D^3=0 := by simpa only [hy,hg,zero_pow (by decide : (2:ℕ)≠0),
      zero_pow (by decide : (4:ℕ)≠0),mul_zero,zero_add] using he
    have h4 : (4:F)≠0 := by convert mul_ne_zero h2 h2 using 1 <;> norm_num
    exact (mul_ne_zero h4 (pow_ne_zero 3 hD)) hz
  · exact Or.inl (mul_ne_zero h2 hy)

lemma two_residue_ne (hp : p≠2) : (2:ZMod p)≠0 := by
  intro hz
  have hd := (ZMod.natCast_eq_zero_iff 2 p).mp hz
  have he := (Fact.out : p.Prime).two_le
  have hb := Nat.le_of_dvd (by norm_num : 0<2) hd
  omega

/-- Integral original points at good odd reduction have a unit derivative
in one of the two actual affine charts. -/
theorem derivative_unit (hp : p≠2) (D x y : ℤ_[p]) (hD : ‖D‖=1)
    (hc : y^2=x^3-D*x) : ‖2*y‖=1 ∨ ‖3*x^2-D‖=1 := by
  have hc' := congrArg (PadicInt.toZMod (p:=p)) hc
  simp only [map_pow,map_sub,map_mul] at hc'
  have he := smooth_residue (PadicInt.toZMod D) (PadicInt.toZMod x)
    (PadicInt.toZMod y) (two_residue_ne p hp) ((residue_unit p D).mpr hD) hc'
  simpa only [←residue_unit,map_mul,map_ofNat,map_sub,map_pow] using he

@[expose] def ResidueCurve (D : ℤ_[p]) :=
  {z : ZMod p × ZMod p // z.2^2=z.1^3-PadicInt.toZMod D*z.1}

@[expose] def IntegralCurve (D : ℤ_[p]) :=
  {z : ℤ_[p] × ℤ_[p] // z.2^2=z.1^3-D*z.1}

@[expose] def reduce (D : ℤ_[p]) (z : IntegralCurve p D) : ResidueCurve p D :=
  ⟨(PadicInt.toZMod z.1.1,PadicInt.toZMod z.1.2),by
    have he := congrArg (PadicInt.toZMod (p:=p)) z.2
    simpa only [map_pow,map_sub,map_mul] using he⟩

/-- A simple root of an actual integral polynomial lifts while preserving
its exact residue. This keeps the closeness conclusion of Hensel, rather
than returning an unrelated zero of the same polynomial. -/
theorem hensel_same_residue (F : Polynomial ℤ_[p]) (a : ℤ_[p])
    (hF : PadicInt.toZMod (F.aeval a)=0)
    (hd : PadicInt.toZMod (F.derivative.aeval a)≠0) :
    ∃ b : ℤ_[p], F.aeval b=0 ∧ PadicInt.toZMod b=PadicInt.toZMod a := by
  have hunit := (residue_unit p _).mp hd
  have hnear : ‖F.aeval a‖< ‖F.derivative.aeval a‖^2 := by
    rw [hunit,one_pow]
    exact (residue_zero p _).mp hF
  obtain ⟨b,hb,hclose,_⟩ := hensels_lemma hnear
  refine ⟨b,hb,(residue_equal p b a).mpr ?_⟩
  simpa only [hunit] using hclose

end GoodReductionResidue318
