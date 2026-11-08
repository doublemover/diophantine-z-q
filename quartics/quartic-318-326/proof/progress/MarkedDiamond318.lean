module
public import MarkedPeriod318
public section
noncomputable section
open scoped MatrixGroups
open ModularWeierstrass318 ModularTorusTransport318 ModularTorsionTransport318 EllipticTorsion318
namespace MarkedDiamond318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

/-- A matrix preserves the H-orbit of the canonical primitive residue label.
This is the point-level convention, with a, equivalently d inverse, in H. -/
def PreservesOrbit (N:ℕ) (H:Subgroup (ZMod N)ˣ) (g:SL(2,ℤ)) : Prop :=
  ∃u:H, residueMap g N (MarkedPeriod318.standardLabel N)=(0,(u.val:ZMod N))

theorem preservesOrbit_iff (N:ℕ) (H:Subgroup (ZMod N)ˣ) (g:SL(2,ℤ)) :
    PreservesOrbit N H g ↔ (g 1 0:ZMod N)=0 ∧ ∃u:H,(g 0 0:ZMod N)=u.val := by
  constructor
  · rintro ⟨u,hu⟩
    have hc:=congrArg Prod.fst hu
    have ha:=congrArg Prod.snd hu
    simp only [residueMap,MarkedPeriod318.standardLabel,AddMonoidHom.coe_mk,ZeroHom.coe_mk,
      mul_zero,mul_one,zero_sub,sub_zero] at hc ha
    exact ⟨neg_eq_zero.mp hc,⟨u,ha⟩⟩
  · rintro ⟨hc,u,hu⟩
    exact ⟨u,by simp [residueMap,MarkedPeriod318.standardLabel,hc,hu]⟩

/-- The lower-right-entry convention uses the inverse of the same diamond
unit. Since H is a subgroup, this is exactly the same congruence condition. -/
theorem preservesOrbit_iff_lowerRight (N:ℕ) (H:Subgroup (ZMod N)ˣ) (g:SL(2,ℤ)) :
    PreservesOrbit N H g ↔ (g 1 0:ZMod N)=0 ∧ ∃u:H,(g 1 1:ZMod N)=u.val := by
  have hd : (g 0 0:ZMod N)*(g 1 1:ZMod N)-(g 0 1:ZMod N)*(g 1 0:ZMod N)=1 := by
    have h:=congrArg (Int.castRingHom (ZMod N)) g.det_coe
    rw [Matrix.det_fin_two] at h
    simpa only [Int.coe_castRingHom,Int.cast_sub,Int.cast_mul,Int.cast_one] using h
  rw [preservesOrbit_iff]
  constructor
  · rintro ⟨hc,u,hu⟩
    refine ⟨hc,⟨u⁻¹,?_⟩⟩
    have h : (u.val:ZMod N)*(g 1 1:ZMod N)=1 := by simpa [hu,hc] using hd
    have hi:=congrArg (fun z:ZMod N => (↑(u.val⁻¹):ZMod N)*z) h
    simpa only [←mul_assoc,Units.inv_mul,one_mul,mul_one,Subgroup.coe_inv] using hi
  · rintro ⟨hc,u,hu⟩
    refine ⟨hc,⟨u⁻¹,?_⟩⟩
    have h : (g 0 0:ZMod N)*(u.val:ZMod N)=1 := by simpa [hu,hc] using hd
    have hi:=congrArg (fun z:ZMod N => z*(↑(u.val⁻¹):ZMod N)) h
    simpa only [mul_assoc,Units.mul_inv,mul_one,one_mul,Subgroup.coe_inv] using hi

/-- The literal H-orbit congruence condition is equivalent to transport of the
actual complex elliptic marked point into that same H-orbit of torsion labels. -/
theorem point_orbit_iff (N:ℕ) [NeZero N] (H:Subgroup (ZMod N)ˣ)
    (g:SL(2,ℤ)) (tau:UpperHalfPlane) :
    (∃u:H, pointAddEquiv g tau (MarkedPeriod318.standardPoint N tau)=
      torsionMap (g•tau) N (0,(u.val:ZMod N))) ↔ PreservesOrbit N H g := by
  simp only [MarkedPeriod318.standardPoint,torsion_transport,
    (torsionMap_injective (g•tau) N).eq_iff,PreservesOrbit]

end MarkedDiamond318
