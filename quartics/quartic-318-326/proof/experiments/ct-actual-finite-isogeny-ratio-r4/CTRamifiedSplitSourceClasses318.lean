module
public import CTOddDominantBinomialSquare318
public import CTOddSelectedTorsionBasis318
import CTOriginalPadicValuationPairs318
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
public section

noncomputable section

namespace CTRamifiedSplitSourceClasses318

open CTOddDominantBinomialSquare318 CTOddSelectedTorsionBasis318
open OriginalCasselsOddUnitCharacter318 OriginalCasselsOddUnitSquare318
open OriginalCasselsOddTargetValuation318 OriginalCasselsRamifiedResidue318
open ActualTwoDescentLocalValuationTools318 ActualTwoDescentPadicValuationPairs318

variable {p : ℕ} [Fact p.Prime]

private theorem square_of_factors (x y w : ℚ_[p]) (hx : x≠0) (hw : w≠0)
    (he : y^2=x*w^2) : ∃ u : ℚ_[p], u≠0 ∧ x=u^2 := by
  have hy : y≠0 := by
    intro h
    rw [h,zero_pow (by decide : (2:ℕ)≠0)] at he
    exact (mul_ne_zero hx (pow_ne_zero _ hw)) he.symm
  refine ⟨y/w,div_ne_zero hy hw,?_⟩
  calc
    x=y^2/w^2 := ((div_eq_iff (pow_ne_zero 2 hw)).mpr he).symm
    _=(y/w)^2 := (div_pow y w 2).symm

/-- On the same original source at a split ramified odd place the
only nonzero-abscissa classes are 1 and [n]. No local Hilbert pairing
or analytic doubling index is assumed. -/
theorem split_ramified_affine_labels (hp : 5≤p) (hp2 : p≠2)
    (n x y : ℚ_[p]) (hn : n≠0) (hv : n.valuation=1) (hx : x≠0)
    (hsplit : IsSquare (PadicInt.toZMod (-3:ℤ_[p])))
    (hY : y^2=x*(x-n)*(x+3*n)) :
    (∃ u : ℚ_[p], u≠0 ∧ x=u^2) ∨ (∃ u : ℚ_[p], u≠0 ∧ x=n*u^2) := by
  have h3 : (3:ℚ_[p])≠0 := by norm_num
  have h3D : ¬p∣3 := fun hd => (by omega : ¬p≤3) (Nat.le_of_dvd (by decide : 0<3) hd)
  have h3V : (3:ℚ_[p]).valuation=0 := by
    change ((3:ℕ):ℚ_[p]).valuation=0
    exact actual_prime_unit_valuation 3 h3D
  have h3n : 3*n≠0 := mul_ne_zero h3 hn
  have h3nV : (3*n).valuation=1 := by
    rw [Padic.valuation_mul h3 hn,h3V,hv,zero_add]
  have h3r : (3:ZMod p)≠0 := fun he => h3D ((ZMod.natCast_eq_zero_iff 3 p).mp he)
  have hNegThreeU : IsUnit (-3:ℤ_[p]) := by
    apply (residue_nonzero_iff_unit (-3:ℤ_[p])).mp
    intro he
    apply h3r
    rw [map_neg,map_ofNat] at he
    exact neg_eq_zero.mp he
  obtain ⟨d,hd,hD⟩ := (unit_square_iff_residue hp2 (-3:ℤ_[p]) hNegThreeU).mpr hsplit
  change PadicInt.Coe.ringHom (-(3:ℤ_[p]))=d^2 at hD
  rw [map_neg,map_ofNat] at hD
  rcases lt_trichotomy x.valuation 1 with hlo | hmid | hhi
  · left
    obtain ⟨u,hu,he⟩ := one_add_square_of_positive hp2 (-(n/x)) (by
      rw [actual_valuation_neg,actual_valuation_div _ _ hn hx,hv]
      omega)
    obtain ⟨v,hv0,hf⟩ := one_add_square_of_positive hp2 ((3*n)/x) (by
      rw [actual_valuation_div _ _ h3n hx,h3nV]
      omega)
    refine square_of_factors x y (x*u*v) hx (mul_ne_zero (mul_ne_zero hx hu) hv0) ?_
    calc
      y^2 = x*(x-n)*(x+3*n) := hY
      _ = x*(x*(1+ -(n/x)))*(x*(1+(3*n)/x)) := by field_simp [hx] <;> ring
      _ = x*(x*u*v)^2 := by rw [he,hf]; ring
  · let u := x/n
    have hu0 : u≠0 := div_ne_zero hx hn
    have huv : u.valuation=0 := by
      change (x/n).valuation=0
      rw [actual_valuation_div _ _ hx hn,hmid,hv,sub_self]
    obtain ⟨U,hU⟩ := actual_integral u huv.ge
    have hUI : IsUnit U := PadicInt.isUnit_iff.mpr (by
      rw [hU]; exact actual_norm_one_of_valuation_zero u hu0 huv)
    have hxU : x=n*(U:ℚ_[p]) := by
      rw [hU]
      change x=n*(x/n)
      field_simp [hn] <;> ring
    let z := PadicInt.toZMod U
    have hz : z=1 ∨ z=-(3:ZMod p) := by
      by_contra he
      have h1 : z≠1 := fun h => he (Or.inl h)
      have h3' : z≠-(3:ZMod p) := fun h => he (Or.inr h)
      have hA : IsUnit (U-1) := (residue_nonzero_iff_unit _).mp (by
        change PadicInt.toZMod (U-1)≠0
        rw [map_sub,map_one]
        exact sub_ne_zero.mpr h1)
      have hB : IsUnit (U+3) := (residue_nonzero_iff_unit _).mp (by
        change PadicInt.toZMod (U+3)≠0
        rw [map_add,map_ofNat]
        exact fun h => h3' (eq_neg_of_add_eq_zero_left h))
      have hAu : ((U-1:ℤ_[p]):ℚ_[p])≠0 := PadicInt.coe_ne_zero.mpr hA.ne_zero
      have hBu : ((U+3:ℤ_[p]):ℚ_[p])≠0 := PadicInt.coe_ne_zero.mpr hB.ne_zero
      have hL : x-n=n*((U-1:ℤ_[p]):ℚ_[p]) := by
        calc
          _ = n*(U:ℚ_[p])-n := congrArg (fun t => t-n) hxU
          _ = _ := by rw [PadicInt.coe_sub,PadicInt.coe_one]; ring
      have hR : x+3*n=n*((U+3:ℤ_[p]):ℚ_[p]) := by
        calc
          _ = n*(U:ℚ_[p])+3*n := congrArg (fun t => t+3*n) hxU
          _ = _ := by
            change n*(U:ℚ_[p])+3*n=n*PadicInt.Coe.ringHom (U+(3:ℤ_[p]))
            rw [map_add,map_ofNat]
            ring
      have hVal := congrArg Padic.valuation hY
      rw [hL,hR,Padic.valuation_pow,
        Padic.valuation_mul (mul_ne_zero hx (mul_ne_zero hn hAu)) (mul_ne_zero hn hBu),
        Padic.valuation_mul hx (mul_ne_zero hn hAu),
        Padic.valuation_mul hn hAu,Padic.valuation_mul hn hBu,
        actual_val_zero_of_unit _ hA,actual_val_zero_of_unit _ hB,hv,hmid] at hVal
      omega
    have hzS : IsSquare (PadicInt.toZMod U) := by
      change IsSquare z
      rcases hz with h | h
      · rw [h]
        exact ⟨1,(one_mul (1:ZMod p)).symm⟩
      · have hsq := hsplit
        rw [map_neg,map_ofNat] at hsq
        rwa [h]
    obtain ⟨r,hr,he⟩ := (unit_square_iff_residue hp2 U hUI).mpr hzS
    exact Or.inr ⟨r,hr,hxU.trans (congrArg (fun z => n*z) he)⟩
  · left
    obtain ⟨u,hu,he⟩ := one_add_square_of_positive hp2 (-(x/n)) (by
      rw [actual_valuation_neg,actual_valuation_div _ _ hx hn,hv]
      omega)
    obtain ⟨v,hv0,hf⟩ := one_add_square_of_positive hp2 (x/(3*n)) (by
      rw [actual_valuation_div _ _ hx h3n,h3nV]
      omega)
    refine square_of_factors x y (d*n*u*v) hx
      (mul_ne_zero (mul_ne_zero (mul_ne_zero hd hn) hu) hv0) ?_
    calc
      y^2 = x*(x-n)*(x+3*n) := hY
      _ = x*((-n)*(1+ -(x/n)))*((3*n)*(1+x/(3*n))) := by
        field_simp [hn,h3n,h3] <;> ring
      _ = x*(d*n*u*v)^2 := by rw [he,hf]; linear_combination x*n^2*u^2*v^2*hD

/-- Applies the exact same split condition as the green forward table. -/
theorem selected_split_ramified_affine_labels (hp : 5≤p) (hp2 : p≠2)
    (n x y : ℚ_[p]) (hn : n≠0) (hv : n.valuation=1) (hx : x≠0)
    (hsplit : p%3=1) (hY : y^2=x*(x-n)*(x+3*n)) :
    (∃ u : ℚ_[p], u≠0 ∧ x=u^2) ∨ (∃ u : ℚ_[p], u≠0 ∧ x=n*u^2) :=
  split_ramified_affine_labels hp hp2 n x y hn hv hx ((residue_negThree_square_iff hp).mpr hsplit) hY

end CTRamifiedSplitSourceClasses318

#print axioms CTRamifiedSplitSourceClasses318.selected_split_ramified_affine_labels
