module
public import SimplyConnectedCoverSheets318
public section
noncomputable section
namespace CoverSheetOverlap318
open Set
open SimplyConnectedCoverSheets318
universe u v w w' w''
variable {E:Type u} {X:Type v} {A:Type w} {B:Type w'} {D:Type w''}
  [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace A]
  [TopologicalSpace B] [TopologicalSpace D]
  [SimplyConnectedSpace A] [LocallyPathConnectedSpace A]
  [SimplyConnectedSpace B] [LocallyPathConnectedSpace B]
  [SimplyConnectedSpace D] [LocallyPathConnectedSpace D]
  (p:E→X) (SA SB:Set X) (ca:IsCoveringMapOn p SA) (cb:IsCoveringMapOn p SB)
  (f:C(A,X)) (g:C(B,X)) (hf:∀a,f a∈SA) (hg:∀b,g b∈SB)
  (a₀:A) (b₀:B) (j:C(D,A)) (k:C(D,B)) (hbase:∀d,f (j d)=g (k d)) (d₀:D)

/-- Identify the COMPLETE fibers by their identical projection value at
one actual point of the common domain. No cardinality argument is used. -/
@[expose] def pointFiber : Fiber p f (j d₀)≃Fiber p g (k d₀) where
  toFun x:=⟨x.val,x.property.trans (hbase d₀)⟩
  invFun x:=⟨x.val,x.property.trans (hbase d₀).symm⟩
  left_inv x:=rfl
  right_inv x:=rfl

/-- A SINGLE matching of global sheet labels on a connected common
coordinate domain, fixed by equality at one point. -/
@[expose] def labels : Fiber p f a₀≃Fiber p g b₀:=
  (fiberEquiv p SA ca f hf a₀ (j d₀)).trans
    ((pointFiber p f g j k hbase d₀).trans (fiberEquiv p SB cb g hg b₀ (k d₀)).symm)

lemma labels_at (e:Fiber p f a₀) :
    sheet p SB cb g hg b₀ (labels p SA SB ca cb f g hf hg a₀ b₀ j k hbase d₀ e) (k d₀)=
      sheet p SA ca f hf a₀ e (j d₀) := by
  have h: fiberEquiv p SB cb g hg b₀ (k d₀)
      (labels p SA SB ca cb f g hf hg a₀ b₀ j k hbase d₀ e)=
      pointFiber p f g j k hbase d₀ (fiberEquiv p SA ca f hf a₀ (j d₀) e):=by
    simp only [labels,Equiv.trans_apply,Equiv.apply_symm_apply]
  exact congrArg Subtype.val h

/-- Equality at that one point propagates to EVERY point of the actual
common domain by uniqueness of covering lifts. The match is not allowed
to vary with the point. This is the transition constancy used at real cuts. -/
theorem match_everywhere (e:Fiber p f a₀) (d:D) :
    sheet p SB cb g hg b₀ (labels p SA SB ca cb f g hf hg a₀ b₀ j k hbase d₀ e) (k d)=
      sheet p SA ca f hf a₀ e (j d) := by
  let F:C(D,E):=(sheet p SA ca f hf a₀ e).comp j
  let G:C(D,E):=(sheet p SB cb g hg b₀
    (labels p SA SB ca cb f g hf hg a₀ b₀ j k hbase d₀ e)).comp k
  have hF:p ∘ F=f.comp j:=by
    funext t
    exact congrFun (sheet_lifts p SA ca f hf a₀ e) (j t)
  have hG:p ∘ G=f.comp j:=by
    funext t
    exact (congrFun (sheet_lifts p SB cb g hg b₀
      (labels p SA SB ca cb f g hf hg a₀ b₀ j k hbase d₀ e)) (k t)).trans (hbase t).symm
  have he:p (F d₀)=(f.comp j) d₀:=congrFun hF d₀
  have hu:=ca.existsUnique_continuousMap_lifts (f.comp j) he (fun t=>hf (j t))
  have hGF:G=F:=hu.unique
    ⟨labels_at p SA SB ca cb f g hf hg a₀ b₀ j k hbase d₀ e,hG⟩ ⟨rfl,hF⟩
  exact congrArg (fun H:C(D,E)=>H d) hGF
end CoverSheetOverlap318
