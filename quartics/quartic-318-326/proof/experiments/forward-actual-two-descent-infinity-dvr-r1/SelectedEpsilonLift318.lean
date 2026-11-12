module
public import ActualFourTorsion318
public import BranchHalving
public section
noncomputable section
namespace SelectedEpsilonLift318
open Polynomial GoodReductionResidue318 SelectedReductionOrder318
set_option maxHeartbeats 1000000
variable (p : ℕ) [Fact p.Prime]

/-- The extra finite-field root data in the original Gaussian ray argument
produce a genuine Qp square root of1+rho, for either actual embedding. -/
theorem epsilon_square (rho : ℚ_[p]) (hr : rho^2=2) (hp : p≠2)
    (z t : ZMod p) (hz : z^8= -1) (ht : t^4=2) :
    ∃ a : ℚ_[p], a^2=1+rho := by
  let r : ℤ_[p] := ⟨rho,ActualSplitOrbitEntry318.root_integral p rho hr⟩
  have hrbar := residueRoot_square p rho hr
  obtain ⟨b,hb⟩ := BranchHalving.epsilon_square_from_roots
    (residueRoot p rho hr) z t hrbar hz ht (two_residue_ne p hp)
  have heps : (1:ZMod p)+residueRoot p rho hr≠0 := by
    intro he
    have hh : residueRoot p rho hr= -1 := by linear_combination he
    rw [hh] at hrbar
    have h10 : (1:ZMod p)=0 := by linear_combination -hrbar
    exact one_ne_zero h10
  have hb0 : b≠0 := by
    intro he
    rw [he,zero_pow (by decide : (2:ℕ)≠0)] at hb
    exact heps hb.symm
  let a : ℤ_[p] := (b.val:ℤ_[p])
  have ha : PadicInt.toZMod a=b := by simp only [a,map_natCast,ZMod.natCast_zmod_val]
  let F : Polynomial ℤ_[p] := X^2-C (1+r)
  have hF : PadicInt.toZMod (F.aeval a)=0 := by
    simpa [F,ha,r,residueRoot] using sub_eq_zero.mpr hb
  have hd : PadicInt.toZMod (F.derivative.aeval a)≠0 := by
    simpa [F,ha] using mul_ne_zero (two_residue_ne p hp) hb0
  obtain ⟨c,hc,_⟩ := hensel_same_residue p F a hF hd
  have hc' : c^2=1+r := sub_eq_zero.mp (by simpa [F] using hc)
  refine ⟨(c:ℚ_[p]),?_⟩
  exact_mod_cast hc'

end SelectedEpsilonLift318
