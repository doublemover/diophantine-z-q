module
public import SplitHolomorphicGraphCoordinates318
public section
noncomputable section
namespace SplitHolomorphicAmbientChart318
open SplitHolomorphicImage318 SplitHolomorphicGraphCoordinates318 Set Filter Topology
variable {E F:Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ E]
  [FiniteDimensional ℂ F]
variable (f:E→F) (x:E) (hf:ContDiffAt ℂ 1 f x)
  (hinj:Function.Injective (fderiv ℂ f x))
local notation "A" => fderiv ℂ f x
local notation "K" => Normal A
local notation "v" => vertical f x hf hinj

/-- A genuine open ambient chart, with the ORIGINAL ambient topology.
Both directions are explicit, and the normal coordinate is the actual
kernel of the derivative projection. -/
@[expose] def ambientChart (W:Set E) (hW:IsOpen W) (hv:ContinuousOn v W):
    OpenPartialHomeomorph F (E×K) where
  toFun y:=shear f x hf hinj (split A hinj y)
  invFun q:=(split A hinj).symm ((shear f x hf hinj).symm q)
  source:=projection A ⁻¹' W
  target:=Prod.fst ⁻¹' W
  map_source':=fun y hy=>hy
  map_target':=by
    intro q hq
    change projection A (A q.1+(q.2+v q.1).val)∈W
    rw [map_add,projection_left A hinj]
    have hk:projection A (q.2+v q.1).val=0:=(q.2+v q.1).property
    rwa [hk,add_zero]
  left_inv':=by intro y _;simp only [Equiv.symm_apply_apply,ContinuousLinearEquiv.symm_apply_apply]
  right_inv':=by intro q _;simp only [ContinuousLinearEquiv.apply_symm_apply,Equiv.apply_symm_apply]
  open_source:=hW.preimage (projection A).continuous
  open_target:=hW.preimage continuous_fst
  continuousOn_toFun:=by
    change ContinuousOn (fun y=>(projection A y,normalPart A hinj y-v (projection A y))) _
    exact (projection A).continuous.continuousOn.prodMk
      ((normalPart A hinj).toContinuousLinearMap.continuous.continuousOn.sub
        (hv.comp (projection A).continuous.continuousOn (fun _ h=>h)))
  continuousOn_invFun:=by
    change ContinuousOn (fun q:E×K=>A q.1+(q.2+v q.1).val) _
    exact (A.continuous.comp continuous_fst).continuousOn.add
      (continuous_subtype_val.continuousOn.comp
        (continuous_snd.continuousOn.add
          (hv.comp continuous_fst.continuousOn (fun _ h=>h))) (fun _ _=>mem_univ _))

lemma ambient_holomorphic (W:Set E) (hW:IsOpen W) (hv:DifferentiableOn ℂ v W):
    DifferentiableOn ℂ (ambientChart f x hf hinj W hW hv.continuousOn)
      (projection A ⁻¹' W):=by
  change DifferentiableOn ℂ (fun y=>(projection A y,normalPart A hinj y-v (projection A y))) _
  exact (projection A).differentiable.differentiableOn.prodMk
    ((normalPart A hinj).toContinuousLinearMap.differentiable.differentiableOn.sub
      (hv.comp (projection A).differentiable.differentiableOn (fun _ h=>h)))
lemma ambient_inverse_holomorphic (W:Set E) (hW:IsOpen W) (hv:DifferentiableOn ℂ v W):
    DifferentiableOn ℂ (ambientChart f x hf hinj W hW hv.continuousOn).symm
      (Prod.fst ⁻¹' W):=by
  change DifferentiableOn ℂ (fun q:E×K=>A q.1+(q.2+v q.1).val) _
  exact (A.differentiable.comp differentiable_fst).differentiableOn.add
    ((LinearMap.ker (projection A).toLinearMap).subtypeL.differentiable.differentiableOn.comp
      (differentiable_snd.differentiableOn.add
        (hv.comp differentiable_fst.differentiableOn (fun _ h=>h))) (fun _ _=>mem_univ _))

/-- The entire local image, not only its tangent space, is sent to the
zero normal section by the actual local ambient biholomorphism. -/
lemma flattened_image (W:Set E) (hW:IsOpen W) (hv:ContinuousOn v W)
    (ht:W⊆(chart f x hf hinj).target):
    ambientChart f x hf hinj W hW hv '' (graph f x hf hinj '' W)=
      {q:E×K|q.1∈W ∧ q.2=0}:=by
  ext q
  constructor
  · rintro ⟨y,⟨w,hw,rfl⟩,rfl⟩
    have he:=flatten_graph f x hf hinj w (ht hw)
    change (shear f x hf hinj (split A hinj (graph f x hf hinj w))).1∈W ∧
      (shear f x hf hinj (split A hinj (graph f x hf hinj w))).2=0
    rw [he]
    exact ⟨hw,rfl⟩
  · rintro ⟨hw,hzero⟩
    refine ⟨graph f x hf hinj q.1,⟨q.1,hw,rfl⟩,?_⟩
    change shear f x hf hinj (split A hinj (graph f x hf hinj q.1))=q
    rw [flatten_graph f x hf hinj q.1 (ht hw)]
    exact Prod.ext rfl hzero.symm

lemma vertical_holomorphicOn (W:Set E)
    (hg:DifferentiableOn ℂ (graph f x hf hinj) W):DifferentiableOn ℂ v W:=
  (normalPart A hinj).toContinuousLinearMap.differentiable.differentiableOn.comp hg
    (fun _ _=>mem_univ _)
end SplitHolomorphicAmbientChart318
