module
public import OriginalCasselsRamifiedResidue318
public import OriginalCasselsGoodNonsquareLabel318
public section

noncomputable section

namespace OriginalCasselsGoodLift318

open OriginalCasselsOddUnitSquare318 OriginalCasselsRamifiedResidue318
open OriginalCasselsGoodNonsquareLabel318 ActualTwoDescentHenselSquare318

variable {p : ℕ} [Fact p.Prime]

private theorem finite_nat_nonzero (p : ℕ) [Fact p.Prime] (b : ℕ)
    (hb : 0<b) (hbp : b<p) : (b:ZMod p)≠0 := by
  intro h
  exact (not_le_of_gt hbp) (Nat.le_of_dvd hb ((ZMod.natCast_eq_zero_iff b p).mp h))

/-- Exact point lift at a nonzero finite abscissa. For nonzero Y, lift
the square ordinate at fixed X. For Y=0, lift the normalized quadratic
root (derivative nonzero for p≥5) and keep Y=0 literally. -/
theorem actual_target_lift (hp : 5≤p) (N : ℤ_[p]) (hN : IsUnit N)
    (X Y : ZMod p) (hX : X≠0)
    (he : Y^2=X*(X^2-4*(PadicInt.toZMod N)*X+16*(PadicInt.toZMod N)^2)) :
    ∃ x y : ℤ_[p], PadicInt.toZMod x=X ∧ y^2=x*(x^2-4*N*x+16*N^2) := by
  have hp2 : p≠2 := by omega
  by_cases hY : Y=0
  · have hg : X^2-4*(PadicInt.toZMod N)*X+16*(PadicInt.toZMod N)^2=0 := by
      have hh : X*(X^2-4*(PadicInt.toZMod N)*X+16*(PadicInt.toZMod N)^2)=0 :=
        by simpa only [hY,zero_pow (by decide : (2:ℕ)≠0)] using he.symm
      exact (mul_eq_zero.mp hh).resolve_left hX
    let v := (4:ZMod p)*PadicInt.toZMod N
    have hv : v≠0 := mul_ne_zero (finite_nat_nonzero p 4 (by decide) (by omega)) (hN.map PadicInt.toZMod).ne_zero
    have hV : X^2-v*X+v^2=0 := by
      change X^2-(4:ZMod p)*PadicInt.toZMod N*X+(4*PadicInt.toZMod N)^2=0
      linear_combination hg
    let r := X/v
    have hr : r^2-r+1=0 := by
      dsimp [r]
      field_simp [hv]
      <;> linear_combination hV
    obtain ⟨W,_,hWr,hW⟩ := lift_ramified_root hp r hr
    let x := (4:ℤ_[p])*N*W
    refine ⟨x,0,?_,?_⟩
    · simp only [x,map_mul,map_ofNat,hWr]
      change v*(X/v)=X
      field_simp [hv] <;> ring
    · have hg' : x^2-4*N*x+16*N^2=0 := by
        calc
          _ = ((4:ℤ_[p])*N)^2*(W^2-W+1) := by dsimp [x]; ring
          _ = _ := by rw [hW,mul_zero]
      rw [hg',mul_zero,zero_pow (by decide : (2:ℕ)≠0)]
  · let x : ℤ_[p] := X.val
    let z : ℤ_[p] := Y.val
    let A := x*(x^2-4*N*x+16*N^2)
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

/-- Under the actual good coefficient condition, preserve the original
nonzero nonsquare residue in the actual Qp curve witness. -/
theorem exists_lifted_nonsquare_abscissa (hp : 5≤p) (N : ℤ_[p]) (hN : IsUnit N) :
    ∃ x y : ℤ_[p], IsUnit x ∧ ¬IsSquare (PadicInt.toZMod x) ∧
      y^2=x*(x^2-4*N*x+16*N^2) := by
  have h2 : (2:ZMod p)≠0 := finite_nat_nonzero p 2 (by decide) (by omega)
  have h3 : (3:ZMod p)≠0 := finite_nat_nonzero p 3 (by decide) (by omega)
  have hchar : ringChar (ZMod p)≠2 := by rw [ZMod.ringChar_zmod_n]; omega
  obtain ⟨X,Y,hX,hNS,he⟩ := exists_nonsquare_label (PadicInt.toZMod N)
    (hN.map PadicInt.toZMod).ne_zero h2 h3 hchar
  obtain ⟨x,y,hx,hexy⟩ := actual_target_lift hp N hN X Y hX he
  refine ⟨x,y,(residue_nonzero_iff_unit x).mp (fun h => hX (hx.symm.trans h)),?_,hexy⟩
  rwa [hx]

end OriginalCasselsGoodLift318

#print axioms OriginalCasselsGoodLift318.exists_lifted_nonsquare_abscissa
