module
public import PELOriginalInvolutionFiber318
public section
noncomputable section
namespace PELOriginalInvolutionLocalCover318
open PELUnlevelledComplexBase318 PELOriginalMaximalQuotient318
open PELOriginalCharacterQuotient318 PELOriginalCharacterTopology318
open PELOriginalInvolutionTower318 OpenQuotientSameFibers318
open PELOriginalBaseCompact318 Filter Topology
set_option maxHeartbeats 1600000

lemma toInvolution_continuous (i : Fin 4) : Continuous (toInvolution i) := continuous_quot_mk
lemma toInvolution_open (i : Fin 4) : IsOpenMap (toInvolution i) := isOpenMap_quotient_mk'_mul
lemma toInvolution_surjective (i : Fin 4) : Function.Surjective (toInvolution i) :=
  Quotient.mk_surjective
instance involutionCompact (i : Fin 4) : CompactSpace (InvolutionBase i) := by
  apply isCompact_univ_iff.mp
  rw [← Set.range_eq_univ.mpr (toInvolution_surjective i),← Set.image_univ]
  exact isCompact_univ.image (toInvolution_continuous i)
instance involutionT2 (i : Fin 4) : T2Space (InvolutionBase i) := inferInstance
lemma toCharacterBase_continuous (i : Fin 4) : Continuous (toCharacterBase i) :=
  (toCharacter_continuous i).quotient_lift _
lemma toCharacterBase_surjective (i : Fin 4) : Function.Surjective (toCharacterBase i) := by
  intro q
  obtain ⟨x,rfl⟩ := toCharacter_surjective i q
  exact ⟨toInvolution i x,rfl⟩
lemma toCharacterBase_proper (i : Fin 4) : IsProperMap (toCharacterBase i) := by
  apply isProperMap_iff_isClosedMap_and_compact_fibers.mpr
  refine ⟨toCharacterBase_continuous i,?_,?_⟩
  · intro S hS
    exact (hS.isCompact.image (toCharacterBase_continuous i)).isClosed
  · intro q
    exact (isClosed_singleton.preimage (toCharacterBase_continuous i)).isCompact

/-- Local original kernel orbits coincide with local involution orbits,
including centers ramified in X→X/⟨w_m⟩. The actual residual4-map has no
additional local identification or hidden branch point. -/
lemma same_local_fibers (i : Fin 4) (p : UnlevelledBase) :
    ∃ U : Set UnlevelledBase, IsOpen U ∧ p ∈ U ∧
      ∀ x ∈ U, ∀ y ∈ U,
        toInvolution i x = toInvolution i y ↔ toCharacter i x = toCharacter i y := by
  obtain ⟨V,hV,hstab⟩ :=
    ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self (character i).ker p
  refine ⟨interior V,isOpen_interior,mem_interior_iff_mem_nhds.mpr hV,?_⟩
  intro x hx y hy
  constructor
  · exact fun he => congrArg (toCharacterBase i) he
  · intro he
    obtain ⟨k,hk⟩ := (toCharacter_eq_iff i x y).mp he
    have hfix := hstab k ⟨x,⟨⟨y,interior_subset hy,hk⟩,interior_subset hx⟩⟩
    have hm := kernel_fixed_mem i k p hfix
    exact (toInvolution_eq_iff i x y).mpr ⟨⟨k.val,hm⟩,hk⟩

/-- An actual local homeomorphism for the SAME degree4 map, on its original
quotient topologies, at every point. Its full source formula is retained. -/
theorem local_cover (i : Fin 4) (p : InvolutionBase i) :
    ∃ e : OpenPartialHomeomorph (InvolutionBase i) (CharacterBase i),
      p ∈ e.source ∧ ∀ y ∈ e.source,e y = toCharacterBase i y := by
  obtain ⟨x,rfl⟩ := toInvolution_surjective i p
  obtain ⟨U,hU,hxU,hfib⟩ := same_local_fibers i x
  let q := imageMap (toInvolution i) U
  let f := imageMap (toCharacter i) U
  have hq : IsOpenQuotientMap q := imageMap_openQuotient _ U
    (toInvolution_continuous i).continuousOn
    ((toInvolution_open i).comp hU.isOpenMap_subtype_val)
  have hf : IsOpenQuotientMap f := imageMap_openQuotient _ U
    (toCharacter_continuous i).continuousOn
    ((toCharacter_open i).comp hU.isOpenMap_subtype_val)
  have hr : ∀ y z : U,q y = q z ↔ f y = f z := by
    intro y z
    constructor
    · intro he
      exact Subtype.ext ((hfib y y.property z z.property).mp (congrArg Subtype.val he))
    · intro he
      exact Subtype.ext ((hfib y y.property z z.property).mpr (congrArg Subtype.val he))
  let H := homeomorph q f hq.isQuotientMap hf.isQuotientMap hr
  have hQ := toInvolution_open i U hU
  have hF := toCharacter_open i U hU
  let hne : Nonempty (toInvolution i '' U) := ⟨⟨toInvolution i x,⟨x,hxU,rfl⟩⟩⟩
  let e := OpenImageHomeomorphChart318.extend _ _ hQ hF hne H
  have hes : e.source = toInvolution i '' U :=
    OpenImageHomeomorphChart318.extend_source _ _ hQ hF hne H
  refine ⟨e,?_,?_⟩
  · rw [hes]
    exact ⟨x,hxU,rfl⟩
  · intro y hy
    rw [hes] at hy
    obtain ⟨z,hz,rfl⟩ := hy
    have he := OpenImageHomeomorphChart318.extend_value _ _ hQ hF hne H
      (⟨toInvolution i z,⟨z,hz,rfl⟩⟩ : toInvolution i '' U)
    have hv := homeomorph_value q f hq.isQuotientMap hf.isQuotientMap hr (⟨z,hz⟩ : U)
    exact he.trans (congrArg Subtype.val hv)
end PELOriginalInvolutionLocalCover318
