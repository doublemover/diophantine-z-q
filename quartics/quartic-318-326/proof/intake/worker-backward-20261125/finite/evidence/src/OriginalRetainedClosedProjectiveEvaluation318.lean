module

public import OriginalRetainedProjectiveRatio318
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section
noncomputable section

namespace OriginalRetainedClosedProjectiveEvaluation318

open AlgebraicGeometry CategoryTheory MvPolynomial
open OriginalRetainedProjectiveAffinePiece318 OriginalRetainedProjectiveRatio318
open OriginalRetainedComplexZeroByPasting318
attribute [local instance] MvPolynomial.gradedAlgebra

variable {κ : Type} [Fintype κ] [DecidableEq κ]
variable {A Y E : Scheme} (a : A ⟶ Y) (P33 : E ⟶ Y) (σ : T ⟶ E)
local notation "F" => fiber a (σ ≫ P33)
local notation "X" => retainedCarrier a P33 σ
variable (ι₀ : X ⟶ Ambient κ)

/-- Freeze all three affine objects and the quotient arrow before
checking the projective or base composition of a chosen quotient chart. -/
abbrev quotientSpec (i : κ) (I : Ideal (Poly κ i)) :=
  Spec (CommRingCat.of (Poly κ i ⧸ I))

def quotientArrow (i : κ) (I : Ideal (Poly κ i)) :
    quotientSpec i I ⟶ Spec (CommRingCat.of (Poly κ i)) :=
  let φ : CommRingCat.of (Poly κ i) ⟶ CommRingCat.of (Poly κ i ⧸ I) :=
    CommRingCat.ofHom (Ideal.Quotient.mk I)
  Spec.map φ

def quotientAmbient (i : κ) (I : Ideal (Poly κ i)) :
    quotientSpec i I ⟶ Ambient κ :=
  quotientArrow i I ≫ affineArrow κ i

def quotientBase (i : κ) (I : Ideal (Poly κ i)) :
    quotientSpec i I ⟶ T :=
  let φ : CommRingCat.of ℂ ⟶ CommRingCat.of (Poly κ i ⧸ I) :=
    CommRingCat.ofHom ((Ideal.Quotient.mk I).comp (algebraMap ℂ (Poly κ i)))
  Spec.map φ

section UnexpandedPiece
variable {Z : Scheme} (β : Z ⟶ T) (j₀ : Z ⟶ Ambient κ)
variable (i : κ) (I : Ideal (Poly κ i)) (j : quotientSpec i I ⟶ Z)

/-- Elaborate composition outside the dependent record. The three
Scheme objects are explicit, keeping the original fibre opaque. -/
def ambientCondition : Prop :=
  @CategoryStruct.comp Scheme inferInstance (quotientSpec i I) Z (Ambient κ) j j₀ =
    quotientAmbient i I

def baseCondition : Prop :=
  @CategoryStruct.comp Scheme inferInstance (quotientSpec i I) Z T j β =
    quotientBase i I

def rangeCondition : Prop :=
  Set.range j = Set.range (pulledFirst κ j₀ i)

structure QuotientPiece where
  I : Ideal (Poly κ i)
  j : quotientSpec i I ⟶ Z
  openChart : IsOpenImmersion j
  ambientRead : ambientCondition j₀ i I j
  baseRead : baseCondition β i I j
  rangeRead : rangeCondition j₀ i I j

variable {β j₀ i}

theorem QuotientPiece.toAmbient (c : QuotientPiece β j₀ i) :
    c.j ≫ j₀ = quotientAmbient i c.I :=
  c.ambientRead

theorem QuotientPiece.toBase (c : QuotientPiece β j₀ i) :
    c.j ≫ β = quotientBase i c.I :=
  c.baseRead

theorem QuotientPiece.rangeChart (c : QuotientPiece β j₀ i) :
    Set.range c.j = Set.range (pulledFirst κ j₀ i) :=
  c.rangeRead

variable (β j₀ i)
def QuotientPiece.of_projective [IsClosedImmersion j₀]
    (h : j₀ ≫ projectiveBase κ=β) : QuotientPiece β j₀ i := by
  let ex := pulled_piece_quotient κ j₀ β h i
  let I₀ := Classical.choose ex
  let ex' := Classical.choose_spec ex
  let J : quotientSpec i I₀ ⟶ Z := Classical.choose ex'
  let H := Classical.choose_spec ex'
  refine ⟨I₀,J,H.1,?_,?_,H.2.2.2⟩
  · simpa only [ambientCondition, quotientAmbient, quotientArrow] using H.2.1
  · simpa only [baseCondition, quotientBase] using H.2.2.1
end UnexpandedPiece

/-- The one selected original complex surface and base, untouched by
the elaboration-oriented decomposition above. -/
abbrev Chart (i : κ) :=
  QuotientPiece (retainedBase a P33 σ) ι₀ i

def choose [IsClosedImmersion ι₀] (over : ι₀ ≫ projectiveBase κ=retainedBase a P33 σ) (i : κ) :
    Chart a P33 σ ι₀ i :=
  QuotientPiece.of_projective (retainedBase a P33 σ) ι₀ i over

variable {i : κ} (C : Chart a P33 σ ι₀ i) (v : κ → ℂ)
local notation "ae" => MvPolynomial.aeval (ratio v i)

abbrev KillsChart := C.I ≤ RingHom.ker ae.toRingHom

/-- It suffices to verify the original actual dehomogenized generators.
This does not assert that unrelated equations cut out the surface. -/
theorem kills_of_generators (r : Set (Poly κ i)) (h : Ideal.span r=C.I)
    (s : ∀ f ∈ r, ae f=0) : KillsChart a P33 σ ι₀ C v := by
  rw [KillsChart,← h,Ideal.span_le]
  intro f hf
  exact (RingHom.mem_ker (f := ae.toRingHom)).2 (s f hf)

def quotientRead (h : KillsChart a P33 σ ι₀ C v) : (Poly κ i ⧸ C.I) →ₐ[ℂ] ℂ :=
  Ideal.Quotient.liftₐ C.I ae (fun x hx => (RingHom.mem_ker (f := ae.toRingHom)).1 (h hx))

variable (h : KillsChart a P33 σ ι₀ C v)

theorem quotientRead_comp : (quotientRead a P33 σ ι₀ C v h).toRingHom.comp
    (Ideal.Quotient.mk C.I) = ae.toRingHom := by
  exact congrArg AlgHom.toRingHom (Ideal.Quotient.liftₐ_comp C.I ae
    (fun x hx => (RingHom.mem_ker (f := ae.toRingHom)).1 (h hx)))

/-- This is an actual point on the original closed group over the
same named complex embedding, with exact base arrow. -/
def actual (h : KillsChart a P33 σ ι₀ C v) : Over.mk (𝟙 T) ⟶ F :=
  Over.homMk (Spec.map (CommRingCat.ofHom (quotientRead a P33 σ ι₀ C v h).toRingHom) ≫ C.j) (by
    change (Spec.map (CommRingCat.ofHom (quotientRead a P33 σ ι₀ C v h).toRingHom) ≫ C.j) ≫
      retainedBase a P33 σ = 𝟙 T
    rw [Category.assoc,C.toBase,quotientBase,← Spec.map_comp,← CommRingCat.ofHom_comp,← RingHom.comp_assoc,
      quotientRead_comp]
    have eq : ae.toRingHom.comp (algebraMap ℂ (Poly κ i)) = RingHom.id ℂ :=
      RingHom.ext fun c => ae.commutes c
    rw [eq,CommRingCat.ofHom_id,Spec.map_id])

theorem actual_ambient :
    (actual a P33 σ ι₀ C v h).left ≫ ι₀ = actualPointFromVector v i := by
  change (Spec.map (CommRingCat.ofHom (quotientRead a P33 σ ι₀ C v h).toRingHom) ≫ C.j) ≫ ι₀ = _
  rw [Category.assoc,C.toAmbient,quotientAmbient,quotientArrow,← Category.assoc,← Spec.map_comp,← CommRingCat.ofHom_comp,
    quotientRead_comp,actualPointFromVector]

/-- If the same vector is read in two genuine quotient charts, the
whole points of the original closed surface agree before any
analytification, not just after applying coordinate functions. -/
theorem actual_overlap [IsClosedImmersion ι₀] {k : κ}
    (D : Chart a P33 σ ι₀ k) (hd : KillsChart a P33 σ ι₀ D v)
    (hi : v i≠0) (hk : v k≠0) :
    actual a P33 σ ι₀ C v h = actual a P33 σ ι₀ D v hd := by
  apply Over.OverMorphism.ext
  apply (cancel_mono ι₀).mp
  rw [actual_ambient,actual_ambient]
  exact actual_chart_ratio v i hi k hk

/-- Exact uniqueness immediately identifies an already retained
group point with a coordinate evaluation. No maps are deduced from
matching the unmarked scalar T or its differential. -/
theorem actual_is_old_point [IsClosedImmersion ι₀]
    (old : Over.mk (𝟙 T) ⟶ F) (pin : old.left ≫ ι₀=actualPointFromVector v i) :
    actual a P33 σ ι₀ C v h = old := by
  apply Over.OverMorphism.ext
  apply (cancel_mono ι₀).mp
  rw [actual_ambient,pin]

end OriginalRetainedClosedProjectiveEvaluation318
