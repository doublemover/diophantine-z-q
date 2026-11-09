module
public import ReciprocalIntegral318
public import Mathlib.NumberTheory.Padics.Hensel
public section
namespace CanonicalRoot318
variable (p : ℕ) [Fact p.Prime]

theorem exists_root (hp : 19≤p) (w : ℚ_[p]) (hw : ‖w‖<1) :
    ∃ v : ℚ_[p], v^2=1-w ∧ ‖v-1‖<1 := by
  let wi : ℤ_[p] := w.lift hw.le
  let F : Polynomial ℤ_[p] := Polynomial.X^2-Polynomial.C (1-wi)
  have he (v : ℤ_[p]) : F.aeval v=v^2-(1-wi) := by simp [F]
  have hd (v : ℤ_[p]) : F.derivative.aeval v=2*v := by simp [F]; norm_num
  have hn2 : ‖(2:ℤ_[p])‖=1 := by
    rw [←PadicInt.norm_coe]
    exact_mod_cast JTail318.norm_nat_unit p 2 (by decide) (by omega)
  have hh : ‖F.aeval (1:ℤ_[p])‖<‖F.derivative.aeval (1:ℤ_[p])‖^2 := by
    rw [he,hd]
    simp only [one_pow,mul_one,sub_sub_cancel,hn2,one_pow]
    simpa only [←PadicInt.norm_coe,wi,PadicInt.coe_lift] using hw
  obtain ⟨v,hv,hnear,_⟩ := hensels_lemma hh
  refine ⟨(v:ℚ_[p]),?_,?_⟩
  · have hi : v^2=1-wi := sub_eq_zero.mp ((he v).symm.trans hv)
    have hi2 := congrArg (fun x : ℤ_[p] => (x:ℚ_[p])) hi
    simpa [wi] using hi2
  · rw [hd,mul_one,hn2] at hnear
    simpa only [←PadicInt.norm_coe,PadicInt.coe_sub,PadicInt.coe_one] using hnear

theorem sum_ne_zero (hp : 19≤p) (a b : ℚ_[p]) (ha : ‖a-1‖<1) (hb : ‖b-1‖<1) : a+b≠0 := by
  have h2 : ‖(2:ℚ_[p])‖=1 := by simpa using JTail318.norm_nat_unit p 2 (by decide) (by omega)
  have hh : ‖(a-1)+(b-1)‖<1 := (Padic.nonarchimedean _ _).trans_lt (max_lt ha hb)
  intro hz
  have he : (a-1)+(b-1)=-(2:ℚ_[p]) := by linear_combination hz
  rw [he,norm_neg,h2] at hh
  exact (lt_irrefl _ hh)

theorem root_unique (hp : 19≤p) (w a b : ℚ_[p]) (ha : a^2=1-w) (hb : b^2=1-w)
    (ha1 : ‖a-1‖<1) (hb1 : ‖b-1‖<1) : a=b := by
  have hz : (a-b)*(a+b)=0 := by linear_combination ha-hb
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (sum_ne_zero p hp a b ha1 hb1))

/-- The unique root near 1. The default outside the open unit ball is not used. -/
@[expose] noncomputable def root (hp : 19≤p) (w : ℚ_[p]) : ℚ_[p] :=
  if hw : ‖w‖<1 then (exists_root p hp w hw).choose else 1

theorem root_spec (hp : 19≤p) (w : ℚ_[p]) (hw : ‖w‖<1) :
    (root p hp w)^2=1-w ∧ ‖root p hp w-1‖<1 := by
  rw [root,dif_pos hw]
  exact (exists_root p hp w hw).choose_spec

theorem root_zero (hp : 19≤p) : root p hp 0=1 := by
  have hh := root_spec p hp 0 (by norm_num)
  exact root_unique p hp 0 _ 1 hh.1 (by norm_num) hh.2 (by norm_num)


theorem argument_small (w : ℚ_[p]) (r : ℤ) (hr : 1≤r) (hw : w.valuation=4*r) : ‖w‖<1 := by
  rw [Padic.norm_eq_zpow_neg_valuation (HTail318.argument_ne_zero p w r hr hw),hw]
  apply (zpow_lt_one_iff_right₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)).mpr
  omega

theorem root_depth (hp : 19≤p) (w : ℚ_[p]) (r : ℤ) (hr : 1≤r)
    (hw : w.valuation=4*r) : (root p hp w-1).valuation=4*r := by
  let v := root p hp w
  have hv := root_spec p hp w (argument_small p w r hr hw)
  have h2 : ‖(2:ℚ_[p])‖=1 := by simpa using JTail318.norm_nat_unit p 2 (by decide) (by omega)
  have hsum : ‖v+1‖=1 := by
    rw [show v+1=(v-1)+2 by ring]
    rw [Padic.add_eq_max_of_ne (by rw [h2]; exact ne_of_lt hv.2),h2,max_eq_right hv.2.le]
  have he : w=-(v-1)*(v+1) := by linear_combination hv.1
  have hn : ‖w‖=‖v-1‖ := by rw [he,norm_mul,norm_neg,hsum,mul_one]
  have hne : v-1≠0 := by
    intro hz
    rw [hz,norm_zero] at hn
    exact HTail318.argument_ne_zero p w r hr hw (norm_eq_zero.mp hn)
  rw [Padic.norm_eq_zpow_neg_valuation (HTail318.argument_ne_zero p w r hr hw),
    Padic.norm_eq_zpow_neg_valuation hne] at hn
  have hh := (zpow_right_strictMono₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)).injective hn
  change (v-1).valuation=4*r
  exact (neg_injective hh).symm.trans hw

@[expose] noncomputable def factor (hp : 19≤p) (w : ℚ_[p]) : ℚ_[p] :=
  GTail318.G p (root p hp w) w

theorem factor_pade_precision (hp : 19≤p) (w : ℚ_[p]) (r : ℤ) (hr : 1≤r)
    (hw : w=0 ∨ w.valuation=4*r) :
    ((16*r:ℤ):WithTop ℤ)≤Padic.addValuation
      (factor p hp w-Pade21Domains.PG w/Pade21Domains.QG w) := by
  rcases hw with rfl|hw
  · simp only [factor,root_zero]
    rw [SeriesEndpoints318.G_zero_error_top]
    exact le_top
  · exact GPade318.full_G_pade_precision p hp _ w
      (root_spec p hp w (argument_small p w r hr hw)).1 r hr
      (root_depth p hp w r hr hw)



theorem root_eq_or_neg (hp : 19≤p) (w v : ℚ_[p]) (hw : ‖w‖<1) (hv : v^2=1-w) :
    root p hp w=v ∨ root p hp w=-v := by
  have hs := (root_spec p hp w hw).1.trans hv.symm
  exact (sq_eq_sq_iff_eq_or_eq_neg).mp hs

theorem factor_relative_precision (hp : 19≤p) (w : ℚ_[p]) (r : ℤ) (hr : 1≤r)
    (hw : w=0 ∨ w.valuation=4*r) :
    ((4*r:ℤ):WithTop ℤ)≤Padic.addValuation (factor p hp w-1) := by
  rcases hw with rfl|hw
  · simp [factor,root_zero,SeriesEndpoints318.G_zero]
  · exact SeriesUnits318.G_relative_precision p hp _ w
      (root_spec p hp w (argument_small p w r hr hw)).1 r hr
      (root_depth p hp w r hr hw)

theorem factor_unit (hp : 19≤p) (w : ℚ_[p]) (r : ℤ) (hr : 1≤r)
    (hw : w=0 ∨ w.valuation=4*r) : Padic.addValuation (factor p hp w)=0 := by
  have hpos : (0:WithTop ℤ)<((4*r:ℤ):WithTop ℤ) := by
    exact_mod_cast (show (0:ℤ)<4*r by omega)
  have hnear := hpos.trans_le (factor_relative_precision p hp w r hr hw)
  have h1 : Padic.addValuation (1:ℚ_[p])<Padic.addValuation (factor p hp w-1) := by
    simpa only [Padic.addValuation.map_one] using hnear
  simpa only [add_sub_cancel,Padic.addValuation.map_one] using
    Padic.addValuation.map_add_eq_of_lt_left h1

/-- The canonical analytic candidate in the actual z parameter. Group-law
compatibility is not part of this definition or the following precision results. -/
@[expose] noncomputable def primitive (hp : 19≤p) (z w : ℚ_[p]) : ℚ_[p] :=
  z*factor p hp w

theorem primitive_valuation (hp : 19≤p) (z w : ℚ_[p]) (r : ℤ) (hr : 1≤r)
    (hw : w=0 ∨ w.valuation=4*r) :
    Padic.addValuation (primitive p hp z w)=Padic.addValuation z := by
  rw [primitive,Padic.addValuation.map_mul,factor_unit p hp w r hr hw,add_zero]

theorem primitive_error (hp : 19≤p) (z w : ℚ_[p]) (r : ℤ) (hr : 1≤r)
    (hw : w=0 ∨ w.valuation=4*r) :
    Padic.addValuation z+((4*r:ℤ):WithTop ℤ)≤Padic.addValuation (primitive p hp z w-z) := by
  rw [primitive,show z*factor p hp w-z=z*(factor p hp w-1) by ring,Padic.addValuation.map_mul]
  exact add_le_add le_rfl (factor_relative_precision p hp w r hr hw)

theorem primitive_pade_error (hp : 19≤p) (z w : ℚ_[p]) (r : ℤ) (hr : 1≤r)
    (hw : w=0 ∨ w.valuation=4*r) :
    Padic.addValuation z+((16*r:ℤ):WithTop ℤ)≤Padic.addValuation
      (primitive p hp z w-z*(Pade21Domains.PG w/Pade21Domains.QG w)) := by
  rw [primitive,show z*factor p hp w-z*(Pade21Domains.PG w/Pade21Domains.QG w)=
    z*(factor p hp w-Pade21Domains.PG w/Pade21Domains.QG w) by ring,Padic.addValuation.map_mul]
  exact add_le_add le_rfl (factor_pade_precision p hp w r hr hw)


end CanonicalRoot318
#print axioms CanonicalRoot318.exists_root
#print axioms CanonicalRoot318.root_spec
#print axioms CanonicalRoot318.root_zero

#print axioms CanonicalRoot318.root_depth
#print axioms CanonicalRoot318.factor_pade_precision

#print axioms CanonicalRoot318.primitive_valuation
#print axioms CanonicalRoot318.primitive_pade_error
