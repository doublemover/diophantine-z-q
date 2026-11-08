module
public import GammaHFilledAction318
public import GammaHDiamondQuotient318
public import AllCuspConnected318
public section
noncomputable section
open Function Filter Topology TopologicalSpace
open GammaHGroup318 GammaHDiamond318 GammaHAction318 GammaHCuspEnds318 GammaHFilledAction318
open FiniteCuspEnds318 AllCuspOverlap318 AllCuspFilling318 AllCuspInfinity318
namespace GammaHCompactAction318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

@[expose,instance_reducible] def filledMatrixAction (N:ℕ) (hN:5≤N) (H:Subgroup (ZMod N)ˣ) :
    MulAction (gammaH N H) (Filled N hN) where
  smul:=filledAct N hN H
  one_smul z:=by
    change filledAct N hN H 1 z=z
    rcases original_or_cusp N hN z with ⟨b,rfl⟩|⟨c,rfl⟩
    · rw [filledAct_original]
      letI:=matrixAction N H
      change original N hN ((1:gammaH N H)•b)=original N hN b
      rw [one_smul]
    · rw [filledAct_cusp]
      letI:=endMatrixAction N H
      change cusp N hN ((1:gammaH N H)•c)=cusp N hN c
      rw [one_smul]
  mul_smul g h z:=by
    change filledAct N hN H (g*h) z=filledAct N hN H g (filledAct N hN H h z)
    rcases original_or_cusp N hN z with ⟨b,rfl⟩|⟨c,rfl⟩
    · rw [filledAct_original,filledAct_original,filledAct_original]
      letI:=matrixAction N H
      change original N hN ((g*h)•b)=original N hN (g•h•b)
      rw [mul_smul]
    · rw [filledAct_cusp,filledAct_cusp,filledAct_cusp]
      letI:=endMatrixAction N H
      change cusp N hN ((g*h)•c)=cusp N hN (g•h•c)
      rw [mul_smul]

theorem filledAct_eq_of_diamond_eq (N:ℕ) (hN:5≤N) (H:Subgroup (ZMod N)ˣ)
    (g h:gammaH N H) (he:diamond N H g=diamond N H h) (z:Filled N hN) :
    filledAct N hN H g z=filledAct N hN H h z := by
  rcases original_or_cusp N hN z with ⟨b,rfl⟩|⟨c,rfl⟩
  · rw [filledAct_original,filledAct_original,matrixAct_eq_of_diamond_eq N H g h he]
  · rw [filledAct_cusp,filledAct_cusp,matrixEnd_eq_of_diamond_eq N H g h he]

/-- The actual finite diamond action now extends across every actual cusp,
with no supplied compact action or continuity assumption. -/
@[expose,instance_reducible] def filledDiamondAction (N:ℕ) (hN:5≤N) [NeZero N]
    (H:Subgroup (ZMod N)ˣ) : MulAction H (Filled N hN) := by
  letI:=filledMatrixAction N hN H
  letI:SMul H (Filled N hN):=⟨fun u=>filledAct N hN H (lift N H u)⟩
  apply (diamond_surjective N H).mulActionLeft (diamond N H)
  intro g z
  exact filledAct_eq_of_diamond_eq N hN H _ g (lift_spec N H (diamond N H g)) z

theorem diamond_original (N:ℕ) (hN:5≤N) [NeZero N] (H:Subgroup (ZMod N)ˣ)
    (u:H) (b:Fine N) :
    letI:=diamondAction N H
    letI:=filledDiamondAction N hN H
    u•original N hN b=original N hN (u•b) :=
  filledAct_original N hN H (lift N H u) b

theorem diamond_cusp (N:ℕ) (hN:5≤N) [NeZero N] (H:Subgroup (ZMod N)ˣ)
    (u:H) (c:End N) :
    letI:=endDiamondAction N H
    letI:=filledDiamondAction N hN H
    u•cusp N hN c=cusp N hN (u•c) :=
  filledAct_cusp N hN H (lift N H u) c

theorem diamond_jInfinity (N:ℕ) (hN:5≤N) [NeZero N] (H:Subgroup (ZMod N)ˣ)
    (u:H) (z:Filled N hN) :
    letI:=filledDiamondAction N hN H
    jInfinity N hN (u•z)=jInfinity N hN z :=
  filledAct_jInfinity N hN H (lift N H u) z

theorem diamond_continuous (N:ℕ) (hN:5≤N) [NeZero N] (H:Subgroup (ZMod N)ˣ) :
    letI:=filledDiamondAction N hN H
    ContinuousConstSMul H (Filled N hN) := by
  letI:=filledDiamondAction N hN H
  exact ⟨fun u=>filledAct_continuous N hN H (lift N H u)⟩

end GammaHCompactAction318
