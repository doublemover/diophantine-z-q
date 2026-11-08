module
public import GammaHAction318
public section
noncomputable section
open Function Filter Topology TopologicalSpace UpperHalfPlane
open GammaHGroup318 GammaHDiamond318 GammaHAction318
open ModularTorusTransport318 ModularTorsionTransport318 EllipticTorsion318
open scoped MatrixGroups
namespace GammaHMarking318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

@[expose] def unitPoint (N:ℕ) [NeZero N] (tau:UpperHalfPlane) (u:(ZMod N)ˣ) :
    (ModularWeierstrass318.curve tau).toAffine.Point := torsionMap tau N (0,(u:ZMod N))

/-- The literal unit-labelled point is actual multiplication of the canonical
elliptic point, not just a renamed residue label. -/
theorem unitPoint_eq_nsmul (N:ℕ) [NeZero N] (tau:UpperHalfPlane) (u:(ZMod N)ˣ) :
    unitPoint N tau u=(u:ZMod N).val • MarkedPeriod318.standardPoint N tau := by
  change torsionMap tau N (0,(u:ZMod N))=(u:ZMod N).val • torsionMap tau N (0,1)
  rw [←map_nsmul]
  congr 1
  ext <;> simp [nsmul_eq_mul]

/-- The actual coordinate transport scales the marking by the inverse of the
conventional lower-right diamond unit. -/
theorem canonical_transport (N:ℕ) [NeZero N] (H:Subgroup (ZMod N)ˣ)
    (g:gammaH N H) (tau:UpperHalfPlane) :
    pointAddEquiv g.val tau (MarkedPeriod318.standardPoint N tau)=
      unitPoint N (g.val•tau) ((diamond N H g).val⁻¹) := by
  have hc : (g.val 1 0:ZMod N)=0 := ((mem_iff N H g.val).mp g.property).1
  have hd : (g.val 0 0:ZMod N)*(g.val 1 1:ZMod N)=1 := by
    have h:=congrArg (Int.castRingHom (ZMod N)) g.val.det_coe
    rw [Matrix.det_fin_two] at h
    simpa only [Int.coe_castRingHom,Int.cast_sub,Int.cast_mul,Int.cast_one,hc,mul_zero,sub_zero] using h
  have ha : (g.val 0 0:ZMod N)=((diamond N H g).val⁻¹: (ZMod N)ˣ) := by
    have he:=congrArg (fun z:ZMod N=>z*((↑((diamond N H g).val⁻¹)):ZMod N)) hd
    rw [←diamond_val N H g] at he
    simpa only [mul_assoc,Units.mul_inv,mul_one,one_mul] using he
  change pointAddEquiv g.val tau (torsionMap tau N (0,1))=torsionMap (g.val•tau) N (0,_)
  rw [torsion_transport]
  congr 1
  simp [residueMap,hc,ha]

/-- Central minus one is already trivial on the actual analytic fine quotient.
The finite diamond action must not be mistaken for a free marking action. -/
theorem minus_one_action (N:ℕ) [NeZero N] (H:Subgroup (ZMod N)ˣ)
    (hminus:(-1:(ZMod N)ˣ)∈H) (q:Fine N) :
    letI:=diamondAction N H
    (⟨-1,hminus⟩:H)•q=q := by
  letI:=diamondAction N H
  have hm : (-1:SL(2,ℤ))∈gammaH N H := by
    apply (mem_iff N H _).mpr
    constructor
    · simp [Matrix.SpecialLinearGroup.coe_neg]
    · refine ⟨⟨-1,hminus⟩,?_⟩
      simp [Matrix.SpecialLinearGroup.coe_neg]
  let g:gammaH N H:=⟨-1,hm⟩
  have hd : diamond N H g=⟨-1,hminus⟩ := by
    apply Subtype.ext
    apply Units.ext
    change (((-1:SL(2,ℤ)) 1 1:ℤ):ZMod N)=↑(-1:(ZMod N)ˣ)
    simp [Matrix.SpecialLinearGroup.coe_neg]
  induction q using Quotient.inductionOn with
  | h tau =>
    rw [←hd]
    change diamond N H g • GammaOneAtlas318.quotientMap N tau=GammaOneAtlas318.quotientMap N tau
    rw [diamond_projection]
    change GammaOneAtlas318.quotientMap N ((-1:SL(2,ℤ))•tau)=_
    rw [ModularGroup.SL_neg_smul,one_smul]

end GammaHMarking318
