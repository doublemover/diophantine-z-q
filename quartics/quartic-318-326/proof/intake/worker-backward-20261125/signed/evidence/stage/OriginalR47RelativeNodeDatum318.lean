module
public import OriginalR47RelativePointedWindow318
public import OriginalR47PointedNodeSiteDatum318
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.Etale.Basic
public section
noncomputable section

namespace OriginalR47RelativeNodeDatum318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open OriginalR47RelativePointedWindow318
open OriginalSplitNodeCoordinates318
open OriginalThickCentralReesChart318 (O I)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {T : Type} [CommRing T]
local notation "S" => Spec (CommRingCat.of T)

/-- One fixed coefficient change of the actual arithmetic trait.
It may be a localization of an étale residue extension, so ask
formal étaleness on the ring map, not finite type of this localization.
The q in the literal model is a unit times the original uniformizer. -/
structure Parameters (T : Type) [CommRing T] where
  D : Type
  [comm : CommRing D]
  [domain : IsDomain D]
  [dvr : IsDiscreteValuationRing D]
  φ : T →+* D
  formal : letI := φ.toAlgebra; Algebra.FormallyEtale T D
  π : T
  π_irred : Irreducible π
  q : D
  q_irred : Irreducible q
  u : Dˣ
  scale : q = φ π * (u:D)

attribute [instance] Parameters.comm Parameters.domain Parameters.dvr

abbrev nodeBase (P : Parameters T) (δ : P.D) :
    Spec (CommRingCat.of (Node δ)) ⟶ S :=
  Spec.algebraMap P.D (Node δ) ≫ Spec.map (CommRingCat.ofHom P.φ)

abbrev lineBase : Spec (CommRingCat.of (Polynomial T)) ⟶ S :=
  Spec.algebraMap T (Polynomial T)

variable {X Y : Scheme} {f : X ⟶ S} {x : X}

/-- The ordinary relative chart is either an actual line chart of the
old smooth locus, or an actual literal node chart with a unit axis, or
a true thickness-one chart. Only the last possibility can have both
axes nonunits. Keep the exact old base, not just the residue chart. -/
def TerminalAt (f : X ⟶ S) (x : X) : Prop :=
  Nonempty (Window f x (lineBase (T:=T))) ∨
    ∃ (P : Parameters T) (δ : P.D)
      (J : Window f x (nodeBase P δ)),
      δ = P.q ∨ xAxis δ ∉ (J.g J.w).asIdeal ∨ yAxis δ ∉ (J.g J.w).asIdeal

/-- The actual active chart has literal thickness d+2 at its specified
old closed point (not just an isomorphic completed equation). -/
structure ActiveAt (f : X ⟶ S) (x : X) (d : ℕ) where
  params : Parameters T
  W : Window f x (nodeBase params (params.q^(d+2)))
  atCentre : (W.g W.w).asIdeal = I params.q d

@[expose] def activeSite {d : ℕ} (P : ActiveAt f x d) : OriginalR47TrueNodeSite318.Site X x d where
  R := P.params.D
  q := P.params.q
  q_irred := P.params.q_irred
  U := P.W.U
  u := P.W.w
  into := P.W.e
  split := P.W.g
  flat := P.W.eFlat
  unram := P.W.eUnram
  finite := P.W.eFinite
  flatSplit := P.W.gFlat
  unramSplit := P.W.gUnram
  finiteSplit := P.W.gFinite
  read := P.W.point
  literal := P.atCentre

/-- Retain the genuine terminal witness under the indicated old open
immersion. Unit/nonunit status is on the same split target point. -/
theorem terminal_pull_open (P : TerminalAt f x) (k : Y ⟶ X) [IsOpenImmersion k]
    (y : Y) (hy : k y = x) : TerminalAt (k ≫ f) y := by
  rcases P with ⟨C⟩ | ⟨p,δ,C,h⟩
  · exact Or.inl ⟨(pull_open C k y hy).choose⟩
  · obtain ⟨J,H⟩ := pull_open C k y hy
    exact Or.inr ⟨p,δ,J,H.symm ▸ h⟩

theorem terminal_push_open {f' : Y ⟶ S} {y : Y} (P : TerminalAt f' y)
    (j : Y ⟶ X) [IsOpenImmersion j] (h : j ≫ f = f') :
    TerminalAt f (j y) := by
  rcases P with ⟨C⟩ | ⟨p,δ,C,H⟩
  · exact Or.inl ⟨push_open C j h⟩
  · exact Or.inr ⟨p,δ,push_open C j h,H⟩

@[expose] def active_push_iso {f' : Y ⟶ S} {y : Y} {d : ℕ}
    (P : ActiveAt f' y d) (j : Y ≅ X) (h : j.hom ≫ f = f') :
    ActiveAt f (j.hom y) d where
  params := P.params
  W := push_open P.W j.hom h
  atCentre := P.atCentre

end OriginalR47RelativeNodeDatum318

#print axioms OriginalR47RelativeNodeDatum318.activeSite
#print axioms OriginalR47RelativeNodeDatum318.terminal_pull_open
#print axioms OriginalR47RelativeNodeDatum318.active_push_iso
