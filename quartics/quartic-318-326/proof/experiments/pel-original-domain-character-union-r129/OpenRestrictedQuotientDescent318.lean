module
public import Mathlib.Topology.Constructions
public section
noncomputable section
namespace OpenRestrictedQuotientDescent318
open Set Topology
variable {X Y Z:Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- A choice of a representative is used only after genuine surjectivity;
all values and continuity are independent of that choice by exact fibers. -/
@[expose] def representative (q:X→Y) (hq:Function.Surjective q) (y:Y) : X :=
  Classical.choose (hq y)

theorem representative_spec (q:X→Y) (hq:Function.Surjective q) (y:Y) :
    q (representative q hq y)=y := Classical.choose_spec (hq y)

@[expose] def descended (q:X→Y) (hq:Function.Surjective q) (g:X→Z) : Y→Z :=
  fun y=>g (representative q hq y)

theorem descended_agrees (q:X→Y) (hq:Function.Surjective q) (g:X→Z)
    (hg:∀x x',q x=q x'→g x=g x') (x:X) : descended q hq g (q x)=g x :=
  hg _ x (representative_spec q hq (q x))

theorem descended_continuous (q:X→Y) (hq:IsQuotientMap q) (g:X→Z)
    (hc:Continuous g) (hg:∀x x',q x=q x'→g x=g x') :
    Continuous (descended q hq.surjective g) := by
  apply hq.continuous_iff.mpr
  have he:descended q hq.surjective g ∘ q=g :=
    funext (descended_agrees q hq.surjective g hg)
  rw [he]
  exact hc

/-- Restricting the ACTUAL quotient to an open target complement retains
its quotient topology; no topology is transported from the desired map. -/
theorem restricted_quotient (q:X→Y) (hq:IsQuotientMap q)
    (V:Set Y) (hV:IsOpen V) : IsQuotientMap (V.restrictPreimage q) :=
  hq.restrictPreimage_isOpen hV
end OpenRestrictedQuotientDescent318
