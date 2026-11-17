module
public import PELOriginalInvolutionVisibleSquare318
public section
noncomputable section
namespace PELOriginalInvolutionUnramified318
open PELUnlevelledComplexBase318 PELOriginalMaximalQuotient318
open PELOriginalCharacterQuotient318 PELOriginalCharacterBranches318
open PELOriginalInvolutionTower318 PELOriginalInvolutionLocalCover318
open PELOriginalInvolutionMaximalFibers318 PELOriginalBranchLabels318
open OpenQuotientSameFibers318 Filter Topology
set_option maxHeartbeats 2400000

/-- Away from the four visible target values, EVERY full original
stabilizer already lies in the original omitted-label involution. -/
lemma full_fixed_mem (i : Fin 4) (p : UnlevelledBase)
    (hp : PELOriginalMaximalQuotient318.projection p∉CharacterBranchValues i)
    (g : Labels) (hg : g • p=p) : g∈involutionGroup i := by
  have hK : g∈(character i).ker := by
    by_cases h1 : g=1
    · rw [h1]; exact (character i).ker.one_mem
    · have hn : Multiplicative.toAdd g≠0 := by
        intro he; exact h1 (congrArg Multiplicative.ofAdd he)
      obtain ⟨j,hj⟩ := original_fixed_label _ p hn hg
      have he : g=Multiplicative.ofAdd (InertiaLabels318.fiveLabels j) :=
        congrArg Multiplicative.ofAdd hj
      have hf : p∈fixedLocus j := by rw [he] at hg; exact hg
      have hz : InertiaLabels318.fiveLabels j i=0 := by
        by_contra hv
        apply hp
        exact (PELOriginalDirectCharacterBranches318.branch_values_iff i _).mpr
          ⟨j,hv,(PELOriginalDirectBranchEnumeration318.original_fixed_locus_one_orbit j p).mp hf⟩
      change character i g=1
      rw [he]
      change Multiplicative.ofAdd (InertiaLabels318.fiveLabels j i)=1
      rw [hz]; rfl
  exact kernel_fixed_mem i ⟨g,hK⟩ p hg

/-- The whole16-word orbit relation and the original order-two relation
coincide locally away from the four visible values, including above the
omitted fifth branch value of the ORIGINAL curve. -/
lemma same_local_fibers (i : Fin 4) (p : UnlevelledBase)
    (hp : PELOriginalMaximalQuotient318.projection p∉CharacterBranchValues i) :
    ∃ U : Set UnlevelledBase, IsOpen U ∧ p∈U ∧
      ∀ x∈U,∀ y∈U,toInvolution i x=toInvolution i y ↔
        PELOriginalMaximalQuotient318.projection x=PELOriginalMaximalQuotient318.projection y := by
  obtain ⟨V,hV,hstab⟩ :=
    ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self Labels p
  refine ⟨interior V,isOpen_interior,mem_interior_iff_mem_nhds.mpr hV,?_⟩
  intro x hx y hy
  constructor
  · exact fun he => congrArg (toOriginalMaximal i) he
  · intro he
    obtain ⟨g,hg⟩ := (PELOriginalMaximalQuotient318.projection_eq_iff x y).mp he
    have hfix := hstab g ⟨x,⟨⟨y,interior_subset hy,hg⟩,interior_subset hx⟩⟩
    exact (toInvolution_eq_iff i x y).mpr ⟨⟨g,full_fixed_mem i p hp g hfix⟩,hg⟩

/-- A genuine original local homeomorphism at EVERY point outside the
sixteen-point visible source locus. No genus, RH, algebraization, or
elliptic interpretation is used. -/
theorem local_cover (i : Fin 4) (p : InvolutionBase i)
    (hp : toOriginalMaximal i p∉CharacterBranchValues i) :
    ∃ e : OpenPartialHomeomorph (InvolutionBase i) MaximalBase,
      p∈e.source ∧ ∀ y∈e.source,e y=toOriginalMaximal i y := by
  obtain ⟨x,rfl⟩ := toInvolution_surjective i p
  obtain ⟨U,hU,hxU,hfib⟩ := same_local_fibers i x hp
  let q := imageMap (toInvolution i) U
  let f := imageMap PELOriginalMaximalQuotient318.projection U
  have hq : IsOpenQuotientMap q := imageMap_openQuotient _ U
    (toInvolution_continuous i).continuousOn
    ((toInvolution_open i).comp hU.isOpenMap_subtype_val)
  have hf : IsOpenQuotientMap f := imageMap_openQuotient _ U
    PELOriginalMaximalQuotient318.projection_continuous.continuousOn
    (PELOriginalMaximalQuotient318.projection_open.comp hU.isOpenMap_subtype_val)
  have hr : ∀ y z : U,q y=q z ↔ f y=f z := by
    intro y z
    constructor
    · intro he
      exact Subtype.ext ((hfib y y.property z z.property).mp (congrArg Subtype.val he))
    · intro he
      exact Subtype.ext ((hfib y y.property z z.property).mpr (congrArg Subtype.val he))
  let H := homeomorph q f hq.isQuotientMap hf.isQuotientMap hr
  have hQ := toInvolution_open i U hU
  have hF := PELOriginalMaximalQuotient318.projection_open U hU
  let hne : Nonempty (toInvolution i '' U) := ⟨⟨toInvolution i x,⟨x,hxU,rfl⟩⟩⟩
  let e := OpenImageHomeomorphChart318.extend _ _ hQ hF hne H
  have hes : e.source=toInvolution i '' U :=
    OpenImageHomeomorphChart318.extend_source _ _ hQ hF hne H
  refine ⟨e,?_,?_⟩
  · rw [hes]; exact ⟨x,hxU,rfl⟩
  · intro y hy
    rw [hes] at hy
    obtain ⟨z,hz,rfl⟩ := hy
    have he := OpenImageHomeomorphChart318.extend_value _ _ hQ hF hne H
      (⟨toInvolution i z,⟨z,hz,rfl⟩⟩ : toInvolution i '' U)
    have hv := homeomorph_value q f hq.isQuotientMap hf.isQuotientMap hr (⟨z,hz⟩ : U)
    exact he.trans (congrArg Subtype.val hv)
end PELOriginalInvolutionUnramified318
