module
public import AdmissibleStabilizer318
public import ModularArithmeticCoordinates318
public import Mathlib.Topology.Covering.Quotient
public section
noncomputable section
open Filter Set Topology
namespace AdmissibleQuotientCover318
open OpenJComplexEvaluation318 ModularArithmeticCoordinates318
open ThreeArithmeticQuotient318 GammaOneFiber318
set_option maxHeartbeats 0

lemma admissible_smul (g : image 3) (tau : UpperHalfPlane) (ht : Admissible tau) :
    Admissible (g•tau) := by
  obtain ⟨gamma,hgamma⟩ := g.property
  have he : (g:DerivativeCocycle318.G)=positiveMatrix 3 gamma := hgamma.symm
  change Admissible ((g:DerivativeCocycle318.G)•tau)
  rw [he]
  exact ThreeArithmeticPoint318.admissible_transform gamma.val tau ht

instance locusAction : MulAction (image 3) Locus where
  smul g tau := ⟨g•tau.val,admissible_smul g tau.val tau.property⟩
  one_smul tau := Subtype.ext (one_smul _ _)
  mul_smul g h tau := Subtype.ext (mul_smul g h tau.val)

@[simp] lemma smul_val (g : image 3) (tau : Locus) :
    (g•tau).val=g•tau.val := rfl

instance continuousAction : ContinuousConstSMul (image 3) Locus where
  continuous_const_smul g := by
    apply continuous_induced_rng.mpr
    exact (continuous_const_smul (Γ:=image 3) (T:=UpperHalfPlane) g).comp continuous_subtype_val

lemma locus_open : IsOpen {tau : UpperHalfPlane | Admissible tau} := by
  apply isOpen_iff_mem_nhds.mpr
  intro tau ht
  have he := OpenJLocalComparison318.admissible_eventually tau ht
  have hc : ContinuousAt (fun z : UpperHalfPlane => (z:ℂ)) tau := by fun_prop
  simpa only [UpperHalfPlane.ofComplex_apply] using hc.eventually he

instance locusLocallyCompact : LocallyCompactSpace Locus := locus_open.locallyCompactSpace

instance properlyDiscontinuous : ProperlyDiscontinuousSMul (image 3) Locus where
  finite_disjoint_inter_image {K L} hK hL := by
    have hf := finite_disjoint_inter_image (Γ:=image 3) (T:=UpperHalfPlane)
      (hK.image continuous_subtype_val) (hL.image continuous_subtype_val)
    apply hf.subset
    intro g hg
    obtain ⟨z,⟨w,hw,hwz⟩,hz⟩ := hg
    refine ⟨z.val,⟨w.val,⟨w,hw,rfl⟩,?_⟩,⟨z,hz,rfl⟩⟩
    exact congrArg Subtype.val hwz

instance cancelAction : IsCancelSMul (image 3) Locus := by
  apply isCancelSMul_iff_eq_one_of_smul_eq.mpr
  intro g tau hfix
  apply Subtype.ext
  obtain ⟨gamma,hgamma⟩ := g.property
  have hf : gamma.val•tau.val=tau.val := by
    have hv := congrArg Subtype.val hfix
    change (g:DerivativeCocycle318.G)•tau.val=tau.val at hv
    rw [←hgamma] at hv
    exact hv
  have he := AdmissibleStabilizer318.gamma_one_fixed gamma.val gamma.property
    tau.val tau.property hf
  have hge : gamma=1 := Subtype.ext he
  rw [←hgamma,hge,map_one]

lemma projection_fibers (a b : Locus) :
    sourceProjection a=sourceProjection b ↔ a∈MulAction.orbit (image 3) b := by
  constructor
  · intro he
    have hq : GammaOneAtlas318.quotientMap 3 a.val=
        GammaOneAtlas318.quotientMap 3 b.val := congrArg Subtype.val he
    obtain ⟨g,hg⟩ := MulAction.orbitRel_apply.mp (Quotient.exact hq)
    exact MulAction.mem_orbit_iff.mpr ⟨g,Subtype.ext hg⟩
  · intro he
    obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp he
    apply Subtype.ext
    apply Quotient.sound
    exact MulAction.orbitRel_apply.mpr ⟨g,congrArg Subtype.val hg⟩

/-- The actual already defined projection to the open Gamma1(3) source is
an honest quotient covering map on the admissible locus. -/
theorem covering : IsQuotientCoveringMap sourceProjection (image 3) :=
  sourceProjection_isOpenQuotientMap.isQuotientMap
    .isQuotientCoveringMap_of_properlyDiscontinuousSMul projection_fibers

theorem localHomeomorph : IsLocalHomeomorph sourceProjection := covering.isLocalHomeomorph

end AdmissibleQuotientCover318
