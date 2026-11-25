module
public import OriginalR47ArithmeticFixedPoint318
public import OriginalR47RelativeNodeDatum318
public import OriginalR47LiteralDoubleOrigin318
public import OriginalR47PointedClosedNodalWindow318
public import OriginalR47CanonicalTraitClosedPoint318
public import Mathlib.AlgebraicGeometry.FunctionField
public section
noncomputable section

namespace OriginalR47ActualBadNodeAt318
open AlgebraicGeometry CategoryTheory Set
open OriginalSplitNodeCoordinates318
open OriginalR47TraitRoundKernel318
open OriginalR47InitialArithmeticAtlas318 (fixedPrime fixedPoint fixedPoint_trait fixedPoint_old)
open OriginalR47RelativeNodeDatum318
open OriginalR47RelativePointedWindow318
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type} [CommRing R] [IsDedekindDomain R]
local notation "S" => base (R:=R)
variable {X : Scheme} (s : X ⟶ S) (x : X)

/-- Actual stable double-node datum, over the canonical arithmetic
trait of the original x. This is the usual paired relative nodal
chart at a nonsmooth point; the two named axes vanish and the literal
thickness is positive. There is no closedness, support-size, component
generic assertion, or nonsmooth-census assertion in this structure. -/
structure DoubleNode where
  params : Parameters (Localization.AtPrime (fixedPrime s x))
  m : ℕ
  positive : m ≠ 0
  W : Window (toTrait (fixedPrime s x) s) (fixedPoint s x)
    (nodeBase params (params.q^m))
  xAxis_mem : xAxis (params.q^m) ∈ (W.g W.w).asIdeal
  yAxis_mem : yAxis (params.q^m) ∈ (W.g W.w).asIdeal

/-- Thickness one is terminal on this very window. At larger
thickness the strict actual Rees centre is I(q,m−2), derived from
the double-axis calculation, not obtained from an independent
centre list. -/
theorem terminal_or_active (N : DoubleNode s x) :
    TerminalAt (toTrait (fixedPrime s x) s) (fixedPoint s x) ∨
      ∃ d, Nonempty (ActiveAt (toTrait (fixedPrime s x) s) (fixedPoint s x) d) := by
  rcases N with ⟨P,m,hm,W,hx,hy⟩
  by_cases h : m = 1
  · subst m
    exact Or.inl (Or.inr ⟨P,P.q^1,W,Or.inl (pow_one _)⟩)
  · obtain ⟨d,hd⟩ : ∃ d : ℕ, m = d+2 := ⟨m-2,by omega⟩
    subst m
    refine Or.inr ⟨d,⟨⟨P,W,?_⟩⟩⟩
    exact OriginalR47LiteralDoubleOrigin318.thick_read P.q P.q_irred d (W.g W.w) hx hy

variable [LocallyOfFiniteType s]

/-- At a nongeneric arithmetic base point, every genuine original
relative double-node point is a closed point of the *old actual*
model. In particular a fibre component generic cannot be such a
point. The proof reads the genuine old point window and is independent
of the residue field of the chosen split-model coefficients. -/
theorem closed (N : DoubleNode s x) (hx : s x ≠ genericPoint S) :
    IsClosed ({x} : Set X) := by
  let p := fixedPrime s x
  let f := toTrait p s
  let v := fixedPoint s x
  have hp : p ≠ ⊥ := by
    intro hp
    apply hx
    rw [genericPoint_eq_bot_of_affine]
    exact PrimeSpectrum.ext hp
  letI : p.IsPrime := (s x).isPrime
  letI : p.IsMaximal := (s x).isPrime.isMaximal hp
  letI : LocallyOfFiniteType f := MorphismProperty.pullback_snd _ _
    (inferInstance : LocallyOfFiniteType s)
  let b := nodeBase N.params (N.params.q^N.m)
  let a := N.W.g N.W.w
  letI : a.asIdeal.IsMaximal := OriginalR47LiteralDoubleOrigin318.maximal
    N.params.q N.m N.params.q_irred N.positive a N.xAxis_mem N.yAxis_mem
  have hpoint : b a = IsLocalRing.closedPoint (Localization.AtPrime p) := by
    have he := congrArg (fun j : N.W.U ⟶ trait p => j N.W.w) N.W.over
    rw [Scheme.Hom.comp_apply,Scheme.Hom.comp_apply,N.W.point,fixedPoint_trait s x] at he
    exact he.symm
  have hc : IsClosed ({b a} : Set (trait p)) := by
    rw [hpoint]
    exact IsLocalRing.isClosed_singleton_closedPoint _
  have hcv : IsClosed ({v} : Set (restricted p s)) := by
    have H := OriginalR47PointedClosedNodalWindow318.transport
      N.W.g N.W.e f b N.W.over N.W.w a rfl hc
    exact N.W.point ▸ H
  have hc' := OriginalR47CanonicalTraitClosedPoint318.descend p s v (fixedPoint_trait s x) hcv
  change IsClosed ({forgetMap p s (fixedPoint s x)} : Set X) at hc'
  rwa [fixedPoint_old s x] at hc'

end OriginalR47ActualBadNodeAt318

#print axioms OriginalR47ActualBadNodeAt318.terminal_or_active
#print axioms OriginalR47ActualBadNodeAt318.closed
