module
public import SplitHolomorphicImage318
public section
noncomputable section
namespace SplitHolomorphicGraphCoordinates318
open SplitHolomorphicImage318 Set
variable {E F:Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ E]
  [FiniteDimensional ℂ F]
variable (A:E→L[ℂ]F) (hA:Function.Injective A)
abbrev Normal:=LinearMap.ker (projection A).toLinearMap
@[expose] def normalPart:F→ₗ[ℂ]Normal A:=
  { toFun:=fun y=>⟨y-A (projection A y),by
      change projection A (y-A (projection A y))=0
      rw [map_sub,projection_left A hA]
      exact sub_self _⟩
    map_add':=by intro u v;apply Subtype.ext;simp only [map_add];abel
    map_smul':=by intro c v;apply Subtype.ext;simp only [map_smul,smul_sub] }
@[expose] def splitLinear:F≃ₗ[ℂ]E×Normal A:=
  { toFun:=fun y=>(projection A y,normalPart A hA y)
    invFun:=fun q=>A q.1+q.2.val
    left_inv:=by intro y;change A (projection A y)+(y-A (projection A y))=y;abel
    right_inv:=by
      rintro ⟨w,k⟩
      apply Prod.ext
      · change projection A (A w+k.val)=w
        rw [map_add,projection_left A hA]
        have hk:projection A k.val=0:=k.property
        rw [hk,add_zero]
      · apply Subtype.ext
        change A w+k.val-A (projection A (A w+k.val))=k.val
        rw [map_add,projection_left A hA]
        have hk:projection A k.val=0:=k.property
        rw [hk,add_zero]
        abel
    map_add':=by
      intro u v
      apply Prod.ext
      · exact map_add _ _ _
      · exact map_add _ _ _
    map_smul':=by
      intro c v
      apply Prod.ext
      · exact map_smul _ _ _
      · exact map_smul _ _ _ }
/-- A genuine linear ambient splitting; the target topology is unchanged. -/
@[expose] def split:F≃L[ℂ]E×Normal A:=(splitLinear A hA).toContinuousLinearEquiv
lemma split_fst (y:F):(split A hA y).1=projection A y:=rfl
lemma split_snd (y:F):(split A hA y).2=normalPart A hA y:=rfl
lemma split_symm (q:E×Normal A):(split A hA).symm q=A q.1+q.2.val:=rfl

variable (f:E→F) (x:E) (hf:ContDiffAt ℂ 1 f x)
  (hinj:Function.Injective (fderiv ℂ f x))
@[expose] def vertical:E→Normal (fderiv ℂ f x):=fun w=>
  normalPart (fderiv ℂ f x) hinj (graph f x hf hinj w)
lemma vertical_contDiff:ContDiffAt ℂ 1 (vertical f x hf hinj) (projected f x x):=
  (normalPart (fderiv ℂ f x) hinj).toContinuousLinearMap.contDiff.contDiffAt.comp _
    (graph_contDiff f x hf hinj)
lemma split_graph (w:E) (hw:w∈(chart f x hf hinj).target):
    split (fderiv ℂ f x) hinj (graph f x hf hinj w)=
      (w,vertical f x hf hinj w):=by
  apply Prod.ext
  · exact graph_projected f x hf hinj w hw
  · rfl

/-- Explicit ambient shear: in the genuine derivative splitting, the
local image graph is flattened to the zero normal coordinate. No chosen
source topology or mere set bijection is used to define the splitting. -/
@[expose] def shear:(E×Normal (fderiv ℂ f x))≃(E×Normal (fderiv ℂ f x)):=
  { toFun:=fun q=>(q.1,q.2-vertical f x hf hinj q.1)
    invFun:=fun q=>(q.1,q.2+vertical f x hf hinj q.1)
    left_inv:=by
      rintro ⟨w,k⟩
      apply Prod.ext
      · rfl
      · change k-vertical f x hf hinj w+vertical f x hf hinj w=k
        abel
    right_inv:=by
      rintro ⟨w,k⟩
      apply Prod.ext
      · rfl
      · change k+vertical f x hf hinj w-vertical f x hf hinj w=k
        abel }
lemma flatten_graph (w:E) (hw:w∈(chart f x hf hinj).target):
    shear f x hf hinj (split (fderiv ℂ f x) hinj (graph f x hf hinj w))=(w,0):=by
  rw [split_graph f x hf hinj w hw]
  change (w,vertical f x hf hinj w-vertical f x hf hinj w)=(w,0)
  rw [sub_self]
lemma shear_contDiff (k:Normal (fderiv ℂ f x)):
    ContDiffAt ℂ 1 (shear f x hf hinj) (projected f x x,k):=by
  exact contDiffAt_fst.prodMk (contDiffAt_snd.sub
    ((vertical_contDiff f x hf hinj).comp _ contDiffAt_fst))
lemma shear_inverse_contDiff (k:Normal (fderiv ℂ f x)):
    ContDiffAt ℂ 1 (shear f x hf hinj).symm (projected f x x,k):=by
  exact contDiffAt_fst.prodMk (contDiffAt_snd.add
    ((vertical_contDiff f x hf hinj).comp _ contDiffAt_fst))
end SplitHolomorphicGraphCoordinates318
