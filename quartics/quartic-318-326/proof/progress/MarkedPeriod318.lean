module
public import ModularTorsionTransport318
public import GammaOneAtlas318
public section
noncomputable section
open scoped MatrixGroups
open ModularWeierstrass318 ModularTorusTransport318 ModularTorsionTransport318
open EllipticTorsion318 GammaOneFiber318 GammaOneAtlas318
namespace MarkedPeriod318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

/-- The point-level convention is the actual period point 1/N, not tau/N. -/
@[expose] def standardLabel (N:ℕ) : ZMod N × ZMod N := (0,1)
@[expose] def standardPoint (N:ℕ) [NeZero N] (tau:UpperHalfPlane) :
    (curve tau).toAffine.Point := torsionMap tau N (standardLabel N)

/-- The canonical marking is literally represented by the complex period 1/N. -/
theorem standardPoint_formula (N:ℕ) [NeZero N] (tau:UpperHalfPlane) :
    standardPoint N tau=LatticeModelPoint318.point tau ((N:ℂ)⁻¹) := by
  simpa [standardPoint,standardLabel] using torsionMap_intCast tau N 0 1

theorem standardPoint_order (N:ℕ) [NeZero N] (tau:UpperHalfPlane) :
    addOrderOf (standardPoint N tau)=N := by
  rw [standardPoint,addOrderOf_injective (torsionMap tau N) (torsionMap_injective tau N)]
  simp [standardLabel,Prod.addOrderOf,ZMod.addOrderOf_one]

/-- The literal inverse-transpose residue transformation fixes 1/N exactly
for the actual Gamma1 congruence subgroup. -/
theorem label_stabilizer (N:ℕ) (g:SL(2,ℤ)) :
    residueMap g N (standardLabel N)=standardLabel N ↔ g∈CongruenceSubgroup.Gamma1 N := by
  have hd : (g 0 0:ZMod N)*(g 1 1:ZMod N)-(g 0 1:ZMod N)*(g 1 0:ZMod N)=1 := by
    have h := congrArg (Int.castRingHom (ZMod N)) g.det_coe
    rw [Matrix.det_fin_two] at h
    simpa only [Int.coe_castRingHom,Int.cast_sub,Int.cast_mul,Int.cast_one] using h
  constructor
  · intro h
    have hc := congrArg Prod.fst h
    have ha := congrArg Prod.snd h
    simp only [residueMap,standardLabel,AddMonoidHom.coe_mk,ZeroHom.coe_mk,
      mul_zero,mul_one,zero_sub,sub_zero] at hc ha
    have hc' : (g 1 0:ZMod N)=0 := neg_eq_zero.mp hc
    exact (CongruenceSubgroup.Gamma1_mem N g).mpr ⟨ha,by simpa [ha,hc'] using hd,hc'⟩
  · intro hg
    obtain ⟨ha,_,hc⟩ := (CongruenceSubgroup.Gamma1_mem N g).mp hg
    simp [residueMap,standardLabel,ha,hc]

/-- An actual model-coordinate transport preserves the canonical marked point
if and only if the transporting integral matrix lies in Gamma1. -/
theorem point_stabilizer (N:ℕ) [NeZero N] (g:SL(2,ℤ)) (tau:UpperHalfPlane) :
    pointAddEquiv g tau (standardPoint N tau)=standardPoint N (g•tau) ↔
      g∈CongruenceSubgroup.Gamma1 N := by
  change pointAddEquiv g tau (torsionMap tau N (standardLabel N))=
    torsionMap (g•tau) N (standardLabel N) ↔ _
  rw [torsion_transport]
  exact (torsionMap_injective (g•tau) N).eq_iff.trans (label_stabilizer N g)

/-- Equality in the genuine analytic quotient is exactly an integral modular
change of period preserving the actual canonical point of order N. This does
not assert classification of all algebraic elliptic-curve isomorphisms. -/
theorem quotient_eq_iff_marked_transport (N:ℕ) [NeZero N] (tau sigma:UpperHalfPlane) :
    quotientMap N sigma=quotientMap N tau ↔
      ∃g:SL(2,ℤ), g•tau=sigma ∧
        pointAddEquiv g tau (standardPoint N tau)=standardPoint N (g•tau) := by
  constructor
  · intro h
    obtain ⟨g,hg⟩ := MulAction.orbitRel_apply.mp (Quotient.exact h)
    obtain ⟨gamma,hgamma⟩ := g.property
    refine ⟨gamma.val,?_,(point_stabilizer N gamma.val tau).mpr gamma.property⟩
    change (g.val:DerivativeCocycle318.G)•tau=sigma at hg
    rw [←hgamma] at hg
    exact hg
  · rintro ⟨g,hg,hP⟩
    have hmem := (point_stabilizer N g tau).mp hP
    apply Quotient.sound
    apply MulAction.orbitRel_apply.mpr
    exact ⟨⟨positiveMatrix N ⟨g,hmem⟩,⟨⟨g,hmem⟩,rfl⟩⟩,hg⟩

end MarkedPeriod318
