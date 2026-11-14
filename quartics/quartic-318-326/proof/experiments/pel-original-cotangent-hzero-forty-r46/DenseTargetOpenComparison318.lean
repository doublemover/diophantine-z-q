module
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Compactness.Compact
public section
noncomputable section
namespace DenseTargetOpenComparison318
open Set
variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]

/-- A genuine open map cannot identify two points if its fibers over a
dense target subset are singletons. The argument also controls boundary
fibers; no boundary injectivity is supplied. -/
theorem injective [T2Space M] (F : M → N) (hF : IsOpenMap F)
    (V : Set N) (hV : Dense V)
    (hfib : ∀ x y,F x=F y → F x∈V → x=y) : Function.Injective F := by
  intro x y hxy
  by_contra hne
  obtain ⟨A,B,hA,hB,hx,hy,hdis⟩ := t2_separation hne
  have hI : IsOpen (F '' A ∩ F '' B) := (hF A hA).inter (hF B hB)
  have hn : (F '' A ∩ F '' B).Nonempty :=
    ⟨F x,⟨⟨x,hx,rfl⟩,⟨y,hy,hxy.symm⟩⟩⟩
  obtain ⟨w,⟨hwA,hwB⟩,hwV⟩ := hV.inter_open_nonempty _ hI hn
  obtain ⟨a,ha,haw⟩ := hwA
  obtain ⟨b,hb,hbw⟩ := hwB
  have hab := hfib a b (haw.trans hbw.symm) (haw.symm ▸ hwV)
  exact Set.disjoint_left.mp hdis ha (hab.symm ▸ hb)

/-- A dense regular-target image already forces surjectivity for the
actual continuous compact-source map. -/
theorem surjective [CompactSpace M] [T2Space N] (F : M → N)
    (hF : Continuous F) (V : Set N) (hV : Dense V) (hcover : V⊆range F) :
    Function.Surjective F := by
  have hc : IsClosed (range F) := (isCompact_range hF).isClosed
  intro y
  exact (closure_minimal hcover hc) (hV y)

/-- The SAME compact-source map becomes a genuine homeomorphism once
openness and the dense regular fibers are proved. -/
@[expose] def homeomorph [CompactSpace M] [T2Space M] [T2Space N]
    (F : M → N) (hc : Continuous F) (ho : IsOpenMap F)
    (V : Set N) (hV : Dense V) (hcover : V⊆range F)
    (hfib : ∀ x y,F x=F y → F x∈V → x=y) : M ≃ₜ N :=
  (Equiv.ofBijective F ⟨injective F ho V hV hfib,surjective F hc V hV hcover⟩).
    toHomeomorphOfContinuousOpen hc ho

/-- Interior injectivity suffices for the dense fibers only when ALL
preimages of the regular target region are shown to lie in that interior. -/
theorem fibers_of_interior (F : M → N) (U : Set M) (V : Set N)
    (hinj : InjOn F U) (hpre : F ⁻¹' V⊆U) :
    ∀ x y,F x=F y → F x∈V → x=y := by
  intro x y hxy hx
  exact hinj (hpre hx) (hpre (hxy ▸ hx)) hxy
end DenseTargetOpenComparison318
