module
public import GammaHQuotient318
public import Mathlib.Algebra.Group.Action.Hom
public section
noncomputable section
open Function Filter Topology TopologicalSpace UpperHalfPlane
open DerivativeCocycle318 PeterssonQuotient318 GammaHGroup318 GammaHDiamond318
open scoped MatrixGroups
namespace GammaHAction318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
abbrev Fine (N:ℕ) := Base (GammaOneFiber318.image N)

/-- Normality is proved using the actual diamond kernel, before transporting
any period on the existing fine-level quotient. -/
theorem conjugate_gamma1 (N:ℕ) (H:Subgroup (ZMod N)ˣ) (g:gammaH N H)
    (k:SL(2,ℤ)) (hk:k∈CongruenceSubgroup.Gamma1 N) :
    g.val*k*g.val⁻¹∈CongruenceSubgroup.Gamma1 N := by
  let kH:gammaH N H:=⟨k,gamma1_le_gammaH N H hk⟩
  have hd : diamond N H kH=1 := (diamond_kernel_iff N H kH).mpr hk
  exact (diamond_kernel_iff N H (g*kH*g⁻¹)).mp (by simp [map_mul,map_inv,hd])

/-- Actual integral-matrix action on the already constructed Gamma1 quotient. -/
@[expose] def matrixAct (N:ℕ) (H:Subgroup (ZMod N)ˣ) (g:gammaH N H) : Fine N→Fine N :=
  Quotient.lift (fun tau=>GammaOneAtlas318.quotientMap N (g.val•tau)) (by
    intro a b hab
    obtain ⟨k,hk⟩:=MulAction.orbitRel_apply.mp hab
    obtain ⟨gamma,hgamma⟩:=k.property
    have hg : gamma.val•b=a := by
      change (k.val:G)•b=a at hk
      rw [←hgamma] at hk
      exact hk
    apply Quotient.sound
    apply MulAction.orbitRel_apply.mpr
    let m:CongruenceSubgroup.Gamma1 N:=⟨g.val*gamma.val*g.val⁻¹,
      conjugate_gamma1 N H g gamma.val gamma.property⟩
    refine ⟨⟨GammaOneFiber318.positiveMatrix N m,⟨m,rfl⟩⟩,?_⟩
    change (g.val*gamma.val*g.val⁻¹)•(g.val•b)=g.val•a
    simp only [mul_smul,inv_smul_smul,hg])

@[expose,instance_reducible] def matrixAction (N:ℕ) (H:Subgroup (ZMod N)ˣ) :
    MulAction (gammaH N H) (Fine N) where
  smul:=matrixAct N H
  one_smul q:=by
    induction q using Quotient.inductionOn with
    | h tau => change GammaOneAtlas318.quotientMap N ((1:SL(2,ℤ))•tau)=_;rw [one_smul];rfl
  mul_smul g h q:=by
    induction q using Quotient.inductionOn with
    | h tau => change GammaOneAtlas318.quotientMap N ((g.val*h.val)•tau)=_;rw [mul_smul];rfl

theorem matrixAct_projection (N:ℕ) (H:Subgroup (ZMod N)ˣ) (g:gammaH N H) (tau:UpperHalfPlane) :
    matrixAct N H g (GammaOneAtlas318.quotientMap N tau)=
      GammaOneAtlas318.quotientMap N (g.val•tau) := rfl

theorem matrixAct_continuous (N:ℕ) (H:Subgroup (ZMod N)ˣ) (g:gammaH N H) :
    Continuous (matrixAct N H g) := by
  have hg:Continuous (fun tau:UpperHalfPlane=>g.val•tau) :=
    (continuous_const_smul (g.val:GL (Fin 2) ℝ)).congr
      (fun tau=>(ModularGroup.sl_moeb g.val tau).symm)
  exact continuous_quot_lift _ (continuous_quot_mk.comp hg)

/-- Matrices in the proved diamond kernel act trivially, on the actual quotient. -/
theorem kernel_act (N:ℕ) (H:Subgroup (ZMod N)ˣ) (g:gammaH N H)
    (hg:diamond N H g=1) (q:Fine N) : matrixAct N H g q=q := by
  induction q using Quotient.inductionOn with
  | h tau =>
    have hm:g.val∈CongruenceSubgroup.Gamma1 N := (diamond_kernel_iff N H g).mp hg
    apply Quotient.sound
    apply MulAction.orbitRel_apply.mpr
    exact ⟨⟨GammaOneFiber318.positiveMatrix N ⟨g.val,hm⟩,⟨⟨g.val,hm⟩,rfl⟩⟩,rfl⟩

theorem matrixAct_eq_of_diamond_eq (N:ℕ) (H:Subgroup (ZMod N)ˣ) (g h:gammaH N H)
    (hgh:diamond N H g=diamond N H h) (q:Fine N) : matrixAct N H g q=matrixAct N H h q := by
  letI:=matrixAction N H
  have hk:diamond N H (h⁻¹*g)=1 := by simp [map_mul,map_inv,hgh]
  have he:=congrArg (fun z:Fine N=>h•z) (kernel_act N H (h⁻¹*g) hk q)
  change h•((h⁻¹*g)•q)=h•q at he
  change g•q=h•q
  simpa only [←mul_smul,mul_inv_cancel_left] using he

@[expose] def lift (N:ℕ) [NeZero N] (H:Subgroup (ZMod N)ˣ) (u:H) : gammaH N H :=
  (diamond_surjective N H u).choose

theorem lift_spec (N:ℕ) [NeZero N] (H:Subgroup (ZMod N)ˣ) (u:H) : diamond N H (lift N H u)=u :=
  (diamond_surjective N H u).choose_spec

/-- Actual finite diamond action, obtained from the proved surjective integral
congruence map. Independence of the chosen lift is proved above. -/
@[expose,instance_reducible] def diamondAction (N:ℕ) [NeZero N] (H:Subgroup (ZMod N)ˣ) :
    MulAction H (Fine N) := by
  letI:=matrixAction N H
  letI:SMul H (Fine N):=⟨fun u=>matrixAct N H (lift N H u)⟩
  apply (diamond_surjective N H).mulActionLeft (diamond N H)
  intro g q
  exact matrixAct_eq_of_diamond_eq N H _ g (lift_spec N H (diamond N H g)) q

theorem diamond_projection (N:ℕ) [NeZero N] (H:Subgroup (ZMod N)ˣ) (g:gammaH N H)
    (tau:UpperHalfPlane) :
    letI:=diamondAction N H
    diamond N H g • GammaOneAtlas318.quotientMap N tau=
      GammaOneAtlas318.quotientMap N (g.val•tau) := by
  letI:=diamondAction N H
  change matrixAct N H (lift N H (diamond N H g)) _=_
  rw [matrixAct_eq_of_diamond_eq N H _ g (lift_spec N H (diamond N H g))]
  rfl

theorem diamond_continuous (N:ℕ) [NeZero N] (H:Subgroup (ZMod N)ˣ) :
    letI:=diamondAction N H
    ContinuousConstSMul H (Fine N) := by
  letI:=diamondAction N H
  exact ⟨fun u=>matrixAct_continuous N H (lift N H u)⟩

end GammaHAction318
