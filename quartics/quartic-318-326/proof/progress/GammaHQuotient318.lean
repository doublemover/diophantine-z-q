module
public import GammaHDiamond318
public import QuotientJ318
public section
noncomputable section
open Function Filter Topology TopologicalSpace UpperHalfPlane
open DerivativeCocycle318 PeterssonQuotient318 GammaHGroup318
open scoped MatrixGroups
namespace GammaHQuotient318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

@[expose] def positiveMatrix (N:ℕ) (H:Subgroup (ZMod N)ˣ) : gammaH N H →* G :=
  (Matrix.SpecialLinearGroup.toGLPos.comp (Matrix.SpecialLinearGroup.map (algebraMap ℤ ℝ))).comp
    (gammaH N H).subtype
@[expose] def image (N:ℕ) (H:Subgroup (ZMod N)ˣ) : Subgroup G := (positiveMatrix N H).range

instance properlyDiscontinuous (N:ℕ) (H:Subgroup (ZMod N)ˣ) :
    ProperlyDiscontinuousSMul (image N H) UpperHalfPlane := by
  have hfull : ProperlyDiscontinuousSMul
      (Matrix.SpecialLinearGroup.mapGL (n:=Fin 2) (R:=ℤ) ℝ).range UpperHalfPlane := inferInstance
  rw [Subgroup.properlyDiscontinuousSMul_iff] at hfull ⊢
  intro K L hK hL
  have hf:=hfull hK hL
  have hpre:=hf.preimage (f:=fun g:G=>(g:GL (Fin 2) ℝ)) Subtype.val_injective.injOn
  apply hpre.subset
  rintro g ⟨hg,hint⟩
  refine ⟨?_,hint⟩
  obtain ⟨gamma,rfl⟩:=hg
  exact ⟨gamma.val,rfl⟩

/-- The actual topological Gamma_H orbit quotient, with its quotient topology. -/
abbrev Curve (N:ℕ) (H:Subgroup (ZMod N)ˣ) := Base (image N H)
@[expose] def projection (N:ℕ) (H:Subgroup (ZMod N)ˣ) : UpperHalfPlane→Curve N H :=
  Quotient.mk (MulAction.orbitRel (image N H) UpperHalfPlane)

theorem projection_openQuotient (N:ℕ) (H:Subgroup (ZMod N)ˣ) :
    IsOpenQuotientMap (projection N H) := MulAction.isOpenQuotientMap_quotientMk

theorem curve_topology (N:ℕ) (H:Subgroup (ZMod N)ˣ) :
    T2Space (Curve N H) ∧ SecondCountableTopology (Curve N H) ∧ ConnectedSpace (Curve N H) :=
  ⟨inferInstance,ContinuousConstSMul.secondCountableTopology,inferInstance⟩

theorem image_one_le (N:ℕ) (H:Subgroup (ZMod N)ˣ) :
    GammaOneFiber318.image N ≤ image N H := by
  rintro g ⟨gamma,rfl⟩
  exact ⟨⟨gamma.val,gamma1_le_gammaH N H gamma.property⟩,rfl⟩

/-- The genuine map which forgets the point marking down to its H-orbit. -/
@[expose] def forget (N:ℕ) (H:Subgroup (ZMod N)ˣ) : Base (GammaOneFiber318.image N)→Curve N H :=
  Quotient.lift (projection N H) (by
    intro a b hab
    obtain ⟨g,hg⟩:=MulAction.orbitRel_apply.mp hab
    apply Quotient.sound
    apply MulAction.orbitRel_apply.mpr
    exact ⟨⟨g.val,image_one_le N H g.property⟩,hg⟩)

theorem forget_projection (N:ℕ) (H:Subgroup (ZMod N)ˣ) (tau:UpperHalfPlane) :
    forget N H (GammaOneAtlas318.quotientMap N tau)=projection N H tau := rfl

theorem forget_continuous (N:ℕ) (H:Subgroup (ZMod N)ˣ) : Continuous (forget N H) :=
  continuous_quot_lift _ continuous_quot_mk

theorem forget_surjective (N:ℕ) (H:Subgroup (ZMod N)ˣ) : Surjective (forget N H) := by
  intro z
  obtain ⟨tau,rfl⟩:=(projection_openQuotient N H).surjective z
  exact ⟨GammaOneAtlas318.quotientMap N tau,rfl⟩

/-- Actual quotient equality, with actual elliptic-point orbit transport.
The possible central kernel is retained rather than counted twice. -/
theorem projection_eq_iff_markedOrbit (N:ℕ) [NeZero N] (H:Subgroup (ZMod N)ˣ)
    (tau sigma:UpperHalfPlane) :
    projection N H sigma=projection N H tau ↔ ∃g:SL(2,ℤ),g•tau=sigma ∧
      ∃u:H,ModularTorusTransport318.pointAddEquiv g tau (MarkedPeriod318.standardPoint N tau)=
        EllipticTorsion318.torsionMap (g•tau) N (0,(u.val:ZMod N)) := by
  constructor
  · intro h
    obtain ⟨g,hg⟩:=MulAction.orbitRel_apply.mp (Quotient.exact h)
    obtain ⟨gamma,hgamma⟩:=g.property
    refine ⟨gamma.val,?_,?_⟩
    · change (g.val:G)•tau=sigma at hg
      rw [←hgamma] at hg
      exact hg
    · exact (MarkedDiamond318.point_orbit_iff N H gamma.val tau).mpr
        ((mem_iff_markedOrbit N H gamma.val).mp gamma.property)
  · rintro ⟨g,hg,hP⟩
    have hmem: g∈gammaH N H := (mem_iff_markedOrbit N H g).mpr
      ((MarkedDiamond318.point_orbit_iff N H g tau).mp hP)
    apply Quotient.sound
    apply MulAction.orbitRel_apply.mpr
    exact ⟨⟨positiveMatrix N H ⟨g,hmem⟩,⟨⟨g,hmem⟩,rfl⟩⟩,hg⟩

/-- Genuine j descends to the actual Gamma_H quotient. -/
@[expose] def jMap (N:ℕ) (H:Subgroup (ZMod N)ˣ) : Curve N H→ℂ :=
  Quotient.lift ActualQJ318.jInvariant (by
    intro a b hab
    obtain ⟨g,hg⟩:=MulAction.orbitRel_apply.mp hab
    rw [←hg]
    apply ActualJInvariant318.modular_invariant
    obtain ⟨gamma,hgamma⟩:=g.property
    rw [←hgamma]
    exact ⟨gamma.val,rfl⟩)

theorem jMap_projection (N:ℕ) (H:Subgroup (ZMod N)ˣ) (tau:UpperHalfPlane) :
    jMap N H (projection N H tau)=ActualQJ318.jInvariant tau := rfl

theorem jMap_forget (N:ℕ) (H:Subgroup (ZMod N)ˣ) (z:Base (GammaOneFiber318.image N)) :
    jMap N H (forget N H z)=QuotientJ318.jMap N z := by
  induction z using Quotient.inductionOn with
  | h tau => rfl

theorem jMap_curve_j (N:ℕ) (H:Subgroup (ZMod N)ˣ) (tau:UpperHalfPlane) :
    jMap N H (projection N H tau)=(ModularWeierstrass318.curve tau).j :=
  (ModularWeierstrass318.curve_j tau).symm

theorem jMap_continuous (N:ℕ) (H:Subgroup (ZMod N)ˣ) : Continuous (jMap N H) :=
  continuous_quot_lift _ QuotientJ318.j_holomorphic.continuous

end GammaHQuotient318
