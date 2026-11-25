module
public import OriginalR47ActualCentralFibre318
public import OriginalR47PointedReesAlignment318
public section
noncomputable section

namespace OriginalR47CentralSurvivorFibre318

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set
open OriginalSplitNodeCoordinates318
open OriginalAffineReesBlowup318
open OriginalThickCentralReesChart318 (O I)
open OriginalUpperR40SplitFieldFibre318 (toOld cf)
open OriginalR47PointedReesAlignment318 (Aligned extended asSpec)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The original atAxes name is retained as the literal predicate. -/
abbrev atAxes {L : Type} [CommRing L] (π : L) (n : ℕ)
    (z : PrimeSpectrum (Node (π^n))) : Prop :=
  OriginalR47ActualCentralFibre318.atAxes π n z

section General

variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
variable [IsDomain R] [UniqueFactorizationMonoid R]
variable (q : R) (hq : Irreducible q) (d : ℕ)
variable (m : Ideal A) [m.IsMaximal]
variable [Algebra A B] [Algebra (O q d) B]
variable {u₀ : PrimeSpectrum B} (F : Aligned q d m u₀)

/-- The selected point of the central chart over the true old residue
point. This formulation explicitly pins the two chart legs before
evaluating points of the actual pullback. -/
theorem aligned_unique (hd : d ≠ 0) :
    let g : blowup F.W.point.asIdeal ⟶ blowup (I q d) := F.toSplit
    let j : Spec (CommRingCat.of (Node (q^d))) ⟶ blowup (I q d) := cf q hq d
    let V : Scheme := pullback g j
    let ell : V ⟶ Spec (CommRingCat.of (Node (q^d))) := pullback.snd g j
    let rho : V ⟶ Spec (CommRingCat.of (Localization.Away F.W.g)) :=
      pullback.fst g j ≫ projection F.W.point.asIdeal
    ∃! a : V, rho a = F.W.point ∧ atAxes q d (ell a) := by
  dsimp only
  let g : blowup F.W.point.asIdeal ⟶ blowup (I q d) := F.toSplit
  let j : Spec (CommRingCat.of (Node (q^d))) ⟶ blowup (I q d) := cf q hq d
  let V : Scheme := pullback g j
  let ell : V ⟶ Spec (CommRingCat.of (Node (q^d))) := pullback.snd g j
  let rho : V ⟶ Spec (CommRingCat.of (Localization.Away F.W.g)) :=
    pullback.fst g j ≫ projection F.W.point.asIdeal
  let b := asSpec (extended (A:=O q d) F.W.g)
  change ∃! a : V, rho a = F.W.point ∧ atAxes q d (ell a)
  have H : IsPullback ell rho (j ≫ toOld q d) b :=
    ((IsPullback.of_hasPullback g j).paste_horiz F.splitSquare.flip).flip
  exact OriginalR47ActualCentralFibre318.in_cartesian_chart q hq d ell rho b H
    F.W.point F.splitRead hd

end General

section NamedThick

variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
variable [IsDomain R] [IsDiscreteValuationRing R]
variable (q : R) (hq : Irreducible q) (e : ℕ)
variable (p : Ideal A) [p.IsMaximal]
variable [Algebra A B] [Algebra (O q (e+2)) B]
variable {v₀ : PrimeSpectrum B} (G : Aligned q (e+2) p v₀)

/-- The unique central survivor of this same actual aligned old chart
has exact next ideal I(q,e). The old offset e+2 is in the actual chart
arrow itself, not recovered from the number of points in a fibre. -/
theorem aligned_exact_child :
    let g : blowup G.W.point.asIdeal ⟶ blowup (I q (e+2)) := G.toSplit
    let j : Spec (CommRingCat.of (Node (q^(e+2)))) ⟶ blowup (I q (e+2)) :=
      cf q hq (e+2)
    let V : Scheme := pullback g j
    let ell : V ⟶ Spec (CommRingCat.of (Node (q^(e+2)))) := pullback.snd g j
    let rho : V ⟶ Spec (CommRingCat.of (Localization.Away G.W.g)) :=
      pullback.fst g j ≫ projection G.W.point.asIdeal
    ∃! a : V, rho a = G.W.point ∧ (ell a).asIdeal = I q e := by
  dsimp only
  let g : blowup G.W.point.asIdeal ⟶ blowup (I q (e+2)) := G.toSplit
  let j : Spec (CommRingCat.of (Node (q^(e+2)))) ⟶ blowup (I q (e+2)) :=
    cf q hq (e+2)
  let V : Scheme := pullback g j
  let ell : V ⟶ Spec (CommRingCat.of (Node (q^(e+2)))) := pullback.snd g j
  let rho : V ⟶ Spec (CommRingCat.of (Localization.Away G.W.g)) :=
    pullback.fst g j ≫ projection G.W.point.asIdeal
  let b := asSpec (extended (A:=O q (e+2)) G.W.g)
  change ∃! a : V, rho a = G.W.point ∧ (ell a).asIdeal = I q e
  have H : IsPullback ell rho (j ≫ toOld q (e+2)) b :=
    ((IsPullback.of_hasPullback g j).paste_horiz G.splitSquare.flip).flip
  exact OriginalR47ActualCentralFibre318.exact_child q hq e ell rho b H G.W.point G.splitRead

end NamedThick

end OriginalR47CentralSurvivorFibre318

#print axioms OriginalR47CentralSurvivorFibre318.aligned_unique
#print axioms OriginalR47CentralSurvivorFibre318.aligned_exact_child
