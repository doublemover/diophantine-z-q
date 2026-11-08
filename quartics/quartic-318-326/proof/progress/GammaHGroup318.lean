module
public import MarkedDiamond318
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.GroupTheory.QuotientGroup.Basic
public section
noncomputable section
open scoped MatrixGroups
open CongruenceSubgroup
namespace GammaHGroup318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

/-- The actual lower-right residue is a unit because its source is a group. -/
@[expose] def diagonal (N:ℕ) : Gamma0 N →* (ZMod N)ˣ :=
  (Gamma0Map N).toHomUnits

theorem diagonal_val (N:ℕ) (g:Gamma0 N) : (diagonal N g:ZMod N)=(g.val 1 1:ZMod N) := rfl

/-- The actual congruence subgroup Gamma_H, using the conventional lower-right
entry in H and the literal Gamma0 inclusion into SL(2,Z). -/
@[expose] def gammaH (N:ℕ) (H:Subgroup (ZMod N)ˣ) : Subgroup SL(2,ℤ) :=
  (H.comap (diagonal N)).map (Gamma0 N).subtype

theorem mem_iff (N:ℕ) (H:Subgroup (ZMod N)ˣ) (g:SL(2,ℤ)) :
    g∈gammaH N H ↔ (g 1 0:ZMod N)=0 ∧ ∃u:H,(g 1 1:ZMod N)=u.val := by
  constructor
  · rintro ⟨g0,hg0,rfl⟩
    exact ⟨Gamma0_mem.mp g0.property,⟨⟨diagonal N g0,hg0⟩,rfl⟩⟩
  · rintro ⟨hc,u,hu⟩
    let g0:Gamma0 N:=⟨g,Gamma0_mem.mpr hc⟩
    have he:diagonal N g0=u.val:=Units.ext hu
    exact ⟨g0,by change diagonal N g0∈H;rw [he];exact u.property,rfl⟩

theorem mem_iff_markedOrbit (N:ℕ) (H:Subgroup (ZMod N)ˣ) (g:SL(2,ℤ)) :
    g∈gammaH N H ↔ MarkedDiamond318.PreservesOrbit N H g :=
  (mem_iff N H g).trans (MarkedDiamond318.preservesOrbit_iff_lowerRight N H g).symm

theorem gammaH_le_gamma0 (N:ℕ) (H:Subgroup (ZMod N)ˣ) : gammaH N H≤Gamma0 N := by
  intro g hg
  exact Gamma0_mem.mpr ((mem_iff N H g).mp hg).1

theorem gamma1_le_gammaH (N:ℕ) (H:Subgroup (ZMod N)ˣ) : Gamma1 N≤gammaH N H := by
  intro g hg
  obtain ⟨_,hd,hc⟩:=(Gamma1_mem N g).mp hg
  exact (mem_iff N H g).mpr ⟨hc,⟨1,by simpa using hd⟩⟩

@[expose] def intoGamma0 (N:ℕ) (H:Subgroup (ZMod N)ˣ) : gammaH N H →* Gamma0 N :=
  Subgroup.inclusion (gammaH_le_gamma0 N H)

theorem diagonal_mem (N:ℕ) (H:Subgroup (ZMod N)ˣ) (g:gammaH N H) :
    diagonal N (intoGamma0 N H g)∈H := by
  obtain ⟨_,u,hu⟩ := (mem_iff N H g.val).mp g.property
  have he:diagonal N (intoGamma0 N H g)=u.val := Units.ext hu
  rw [he]
  exact u.property

/-- The actual diamond homomorphism on Gamma_H, not a selected residue label. -/
@[expose] def diamond (N:ℕ) (H:Subgroup (ZMod N)ˣ) : gammaH N H →* H :=
  ((diagonal N).comp (intoGamma0 N H)).codRestrict H (diagonal_mem N H)

theorem diamond_val (N:ℕ) (H:Subgroup (ZMod N)ˣ) (g:gammaH N H) :
    ((diamond N H g).val:ZMod N)=(g.val 1 1:ZMod N) := rfl

/-- The kernel of the actual diamond map is exactly the actual Gamma1 subgroup
inside Gamma_H, not an abstract subgroup of equal index. -/
theorem diamond_kernel_iff (N:ℕ) (H:Subgroup (ZMod N)ˣ) (g:gammaH N H) :
    diamond N H g=1 ↔ g.val∈Gamma1 N := by
  have hg0 := (intoGamma0 N H g).property
  constructor
  · intro h
    have hd:((g.val 1 1:ℤ):ZMod N)=1 := by
      have hh:=congrArg (fun u:H=>(u.val:ZMod N)) h
      exact hh
    have hmem : intoGamma0 N H g∈Gamma1' N := hd
    exact (Gamma1_mem N g.val).mpr ((Gamma1_to_Gamma0_mem (intoGamma0 N H g)).mp hmem)
  · intro h
    apply Subtype.ext
    apply Units.ext
    exact ((Gamma1_mem N g.val).mp h).2.1

end GammaHGroup318
