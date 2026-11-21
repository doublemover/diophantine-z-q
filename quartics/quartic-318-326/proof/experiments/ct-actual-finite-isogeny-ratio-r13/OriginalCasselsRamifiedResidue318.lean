module
public import OriginalCasselsOddTargetValuation318
public import Mathlib.Data.ZMod.Basic
public section

noncomputable section

namespace OriginalCasselsRamifiedResidue318

open OriginalCasselsOddUnitSquare318 OriginalCasselsOddTargetValuation318
open ActualTwoDescentLocalValuationTools318 Polynomial

variable {p : ℕ} [Fact p.Prime]

theorem actual_val_zero_of_unit (A : ℤ_[p]) (hA : IsUnit A) :
    (A:ℚ_[p]).valuation=0 := by
  have hne : (A:ℚ_[p])≠0 := PadicInt.coe_ne_zero.mpr hA.ne_zero
  have hn : ‖(A:ℚ_[p])‖=1 := PadicInt.isUnit_iff.mp hA
  rw [Padic.norm_eq_zpow_neg_valuation hne,←zpow_zero (p:ℝ)] at hn
  have he := (zpow_right_strictMono₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)).injective hn
  omega

/-- On the central ray v_p(x)=v_p(4n)=1 any possible nontrivial
abscissa has an actual unit reduction satisfying z²−z+1=0. -/
theorem actual_ramified_residue
    (n x y : ℚ_[p]) (hn : n≠0) (hx : x≠0)
    (hvn : ((4:ℚ_[p])*n).valuation=1) (hvx : x.valuation=1)
    (he : y^2=x*(x^2-4*n*x+16*n^2)) :
    ∃ Z : ℤ_[p], IsUnit Z ∧ x=(4:ℚ_[p])*n*(Z:ℚ_[p]) ∧
      (PadicInt.toZMod Z)^2-PadicInt.toZMod Z+1=0 := by
  let u := (4:ℚ_[p])*n
  have hu : u≠0 := mul_ne_zero (by norm_num) hn
  have hval : u.valuation=1 := hvn
  have hv : (x/u).valuation=0 := by
    rw [actual_valuation_div _ _ hx hu,hvx,hval,sub_self]
  let Z : ℤ_[p] := ⟨x/u,(actual_norm_one_of_valuation_zero _ (div_ne_zero hx hu) hv).le⟩
  have hZ : IsUnit Z :=
    PadicInt.isUnit_iff.mpr (actual_norm_one_of_valuation_zero _ (div_ne_zero hx hu) hv)
  have hX : x=u*(Z:ℚ_[p]) := by
    change x=u*(x/u)
    field_simp [hu] <;> ring
  refine ⟨Z,hZ,hX,?_⟩
  let A : ℤ_[p] := Z^2-Z+1
  by_contra h
  have ha : PadicInt.toZMod A≠0 := by
    simpa only [A,map_pow,map_sub,map_add,map_one] using h
  have hA : IsUnit A := (residue_nonzero_iff_unit A).mp ha
  have hA0 : (A:ℚ_[p])≠0 := PadicInt.coe_ne_zero.mpr hA.ne_zero
  have hg : x^2-4*n*x+16*n^2=u^2*(A:ℚ_[p]) := by
    rw [show x^2-4*n*x+16*n^2=x^2-u*x+u^2 by dsimp [u]; ring,hX]
    simp only [A,PadicInt.coe_add,PadicInt.coe_sub,PadicInt.coe_one,PadicInt.coe_pow]
    ring
  rw [hg] at he
  have hh := congrArg Padic.valuation he
  rw [Padic.valuation_pow,Padic.valuation_mul hx (mul_ne_zero (pow_ne_zero _ hu) hA0),
    Padic.valuation_mul (pow_ne_zero _ hu) hA0,Padic.valuation_pow,hvx,hval,
    actual_val_zero_of_unit A hA] at hh
  omega

/-- The two roots in the actual finite field are identical or reciprocal.
This gives a single squareclass, not two ramified generators. -/
theorem same_or_inverse_root (r s : ZMod p)
    (hr : r^2-r+1=0) (hs : s^2-s+1=0) :
    r=s ∨ r*s=1 := by
  have hf : (r-s)*(r+s-1)=0 := by linear_combination hr-hs
  rcases mul_eq_zero.mp hf with h|h
  · exact Or.inl (sub_eq_zero.mp h)
  · right
    linear_combination s*h-hs

/-- The actual canonical odd p residue lifts to a root of z²−z+1, not
merely a formally admissible p-adic squareclass. -/
theorem lift_ramified_root (hp : 5≤p) (r : ZMod p) (hr : r^2-r+1=0) :
    ∃ Z : ℤ_[p], IsUnit Z ∧ PadicInt.toZMod Z=r ∧ Z^2-Z+1=0 := by
  let f : Polynomial ℤ_[p] := X^2-X+1
  let a : ℤ_[p] := r.val
  have ha : PadicInt.toZMod a=r := by simp only [a,map_natCast,ZMod.natCast_zmod_val]
  have hF (b : ℤ_[p]) : f.aeval b=b^2-b+1 := by simp [f]
  have hD (b : ℤ_[p]) : f.derivative.aeval b=2*b-1 := by
    simp [f,Polynomial.derivative_pow]
  have hres : PadicInt.toZMod (f.aeval a)=0 := by
    rw [hF,map_add,map_sub,map_pow,map_one,ha]
    exact hr
  have hp3 : (3:ZMod p)≠0 := by
    intro hz
    have hd := (ZMod.natCast_eq_zero_iff 3 p).mp hz
    have he := Nat.le_of_dvd (by decide : 0<3) hd
    omega
  have hd : PadicInt.toZMod (f.derivative.aeval a)≠0 := by
    rw [hD,map_sub,map_mul,map_ofNat,map_one,ha]
    intro hz
    apply hp3
    linear_combination 4*hr-(2*r-1)*hz
  have hdunit : IsUnit (f.derivative.aeval a) := (residue_nonzero_iff_unit _).mp hd
  have hnorm : ‖f.derivative.aeval a‖=1 := by
    rw [PadicInt.norm_def]
    exact PadicInt.isUnit_iff.mp hdunit
  have hh : ‖f.aeval a‖<‖f.derivative.aeval a‖^2 := by
    rw [hnorm,one_pow]
    exact (residue_zero_iff_norm _).mp hres
  obtain ⟨Z,hZ,hnear,_,_⟩ := hensels_lemma (F:=f) (a:=a) hh
  have hrel : PadicInt.toZMod Z=r := by
    have hE : ‖Z-a‖<1 := by simpa only [hnorm] using hnear
    have h := (residue_zero_iff_norm (Z-a)).mpr hE
    rwa [map_sub,ha,sub_eq_zero] at h
  have hr₀ : r≠0 := by
    intro hz
    rw [hz] at hr
    exact (one_ne_zero : (1:ZMod p)≠0) (by simpa using hr)
  have hR0 : PadicInt.toZMod Z≠0 := fun h => hr₀ (hrel.symm.trans h)
  rw [hF] at hZ
  exact ⟨Z,(residue_nonzero_iff_unit _).mp hR0,hrel,hZ⟩

end OriginalCasselsRamifiedResidue318

#print axioms OriginalCasselsRamifiedResidue318.actual_ramified_residue
#print axioms OriginalCasselsRamifiedResidue318.lift_ramified_root
