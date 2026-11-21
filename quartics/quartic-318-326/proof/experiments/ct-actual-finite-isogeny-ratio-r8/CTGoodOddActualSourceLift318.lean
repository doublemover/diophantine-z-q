module
public import CTGoodOddReverseResidueLabel318
public import OriginalCasselsOddUnitCharacter318
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
public section

noncomputable section

namespace CTGoodOddActualSourceLift318

open CTGoodOddReverseResidueLabel318
open OriginalCasselsOddUnitSquare318 ActualTwoDescentHenselSquare318
open OriginalCasselsOddUnitCharacter318

variable {p : ℕ} [Fact p.Prime]

private theorem finite_small_ne (c : ℕ) (hc : 0<c) (h : c<p) :
    (c:ZMod p)≠0 := fun e => (not_le_of_gt h)
      (Nat.le_of_dvd hc ((ZMod.natCast_eq_zero_iff c p).mp e))

private theorem actual_source_lift (hp2 : p≠2) (N : ℤ_[p])
    (X Y : ZMod p) (hX : X≠0)
    (he : Y^2=X*(X-PadicInt.toZMod N)*(X+3*PadicInt.toZMod N)) :
    ∃ x y : ℤ_[p], PadicInt.toZMod x=X ∧ y^2=x*(x-N)*(x+3*N) := by
  by_cases hY : Y=0
  · have hzero : X*(X-PadicInt.toZMod N)*(X+3*PadicInt.toZMod N)=0 := by
      simpa only [hY,zero_pow (by decide : (2:ℕ)≠0)] using he.symm
    rcases mul_eq_zero.mp hzero with hleft | hright
    · have h := sub_eq_zero.mp ((mul_eq_zero.mp hleft).resolve_left hX)
      exact ⟨N,0,h.symm,by simp⟩
    · have h : X= -3*PadicInt.toZMod N := by
        rw [neg_mul]
        exact eq_neg_of_add_eq_zero_left hright
      refine ⟨-3*N,0,?_,?_⟩
      · rw [map_mul,map_neg,map_ofNat,h]
      · have hF : (-3:ℤ_[p])*N+3*N=0 := by rw [neg_mul,neg_add_cancel]
        rw [hF,mul_zero,zero_pow (by decide : (2:ℕ)≠0)]
  · let x : ℤ_[p] := X.val
    let z : ℤ_[p] := Y.val
    let A := x*(x-N)*(x+3*N)
    have hx : PadicInt.toZMod x=X := by simp only [x,map_natCast,ZMod.natCast_zmod_val]
    have hz : PadicInt.toZMod z=Y := by simp only [z,map_natCast,ZMod.natCast_zmod_val]
    have hnz : ‖z‖=1 := by
      rw [PadicInt.norm_def]
      exact PadicInt.isUnit_iff.mp ((residue_nonzero_iff_unit z).mp (fun h => hY (hz.symm.trans h)))
    have hn2 : ‖(2:ℤ_[p])‖=1 :=
      PadicInt.norm_natCast_eq_one_iff.mpr
        ((Nat.coprime_primes Fact.out (by decide : Nat.Prime 2)).mpr hp2)
    have ha : ‖z^2-A‖<1 := by
      apply (residue_zero_iff_norm _).mp
      simp only [A,map_sub,map_add,map_pow,map_mul,map_ofNat,hz,hx,he,sub_self]
    obtain ⟨y,hy⟩ := actual_hensel_square A z (by
      simpa only [norm_mul,hn2,hnz,one_mul,one_pow] using ha)
    exact ⟨x,y,hx,hy⟩

/-- The literal original source, not its forward quotient, has an actual
non-square unit abscissa at every odd good prime p≥5. This uses only the
reverse x-fibres, no dual elliptic addition or local invariant theorem. -/
theorem exists_good_source_nonsquare_unit (hp : 5≤p) (N : ℤ_[p]) (hN : IsUnit N) :
    ∃ x y : ℤ_[p], IsUnit x ∧ ¬IsSquare (PadicInt.toZMod x) ∧
      y^2=x*(x-N)*(x+3*N) := by
  have hp2 : p≠2 := by omega
  let n := PadicInt.toZMod N
  have hn : n≠0 := (hN.map PadicInt.toZMod).ne_zero
  have h2 : (2:ZMod p)≠0 := finite_small_ne 2 (by decide) (by omega)
  have h3 : (3:ZMod p)≠0 := finite_small_ne 3 (by decide) (by omega)
  have hF : ringChar (ZMod p)≠2 := by rw [ZMod.ringChar_zmod_n]; omega
  have hWitness : ∃ X Y : ZMod p, X≠0 ∧ ¬IsSquare X ∧
      Y^2=X*(X-n)*(X+3*n) := by
    by_cases hD : IsSquare (-3:ZMod p)
    · exact finite_original_nonsquare_abscissa n hn h2 h3 hF hD
    · by_cases hNS : IsSquare n
      · have hχ_n := (quadraticChar_one_iff_isSquare hn).mpr hNS
        have hχ_neg3 := quadraticChar_neg_one_iff_not_isSquare.mpr hD
        have hχ : quadraticChar (ZMod p) (-3*n)= -1 := by rw [map_mul,hχ_neg3,hχ_n,mul_one]
        refine ⟨-3*n,0,mul_ne_zero (neg_ne_zero.mpr h3) hn,
          quadraticChar_neg_one_iff_not_isSquare.mp hχ,?_⟩
        rw [show -3*n+3*n=0 by rw [neg_mul,neg_add_cancel],mul_zero,
          zero_pow (by decide : (2:ℕ)≠0)]
      · exact ⟨n,0,hn,hNS,by simp⟩
  obtain ⟨X,Y,hX,hNS,hE⟩ := hWitness
  obtain ⟨x,y,hx,he⟩ := actual_source_lift hp2 N X Y hX hE
  refine ⟨x,y,(residue_nonzero_iff_unit x).mp (fun h => hX (hx.symm.trans h)),?_,he⟩
  rwa [hx]

end CTGoodOddActualSourceLift318

#print axioms CTGoodOddActualSourceLift318.exists_good_source_nonsquare_unit
