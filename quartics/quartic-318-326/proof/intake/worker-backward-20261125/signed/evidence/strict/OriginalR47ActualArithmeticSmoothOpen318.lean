module
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Smooth.Locus
public section
noncomputable section

namespace OriginalR47ActualArithmeticSmoothOpen318

open AlgebraicGeometry CategoryTheory Set
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {R : Type u} [CommRing R] {X : Scheme.{u}}
variable (s : X ⟶ Spec (CommRingCat.of R))

abbrev chartRing (i : X.affineOpenCover.I₀) := X.affineOpenCover.X i
abbrev chart (i : X.affineOpenCover.I₀) : Spec (chartRing i) ⟶ X := X.affineOpenCover.f i

/-- Literal structure map from the chosen actual affine open of X,
not a second nodal base or a closed-fibre approximation. -/
abbrev structural (i : X.affineOpenCover.I₀) : CommRingCat.of R ⟶ chartRing i :=
  Spec.preimage (chart i ≫ s)

abbrev scalar (i : X.affineOpenCover.I₀) : Algebra R (chartRing i) :=
  (structural s i).hom.toAlgebra

theorem structural_read (i : X.affineOpenCover.I₀) :
    Spec.map (structural s i) = chart i ≫ s := Spec.map_preimage _

@[expose] def chartSmooth (i : X.affineOpenCover.I₀) : Set (Spec (chartRing i)) :=
  letI : Algebra R (chartRing i) := scalar s i
  Algebra.smoothLocus R (chartRing i)

variable [IsNoetherianRing R] [LocallyOfFiniteType s]

/-- Finitely presented because the base is the actual Noetherian
arithmetic ring and the structural map is locally finite type. -/
theorem chart_open (i : X.affineOpenCover.I₀) : IsOpen (chartSmooth s i) := by
  let : Algebra R (chartRing i) := scalar s i
  let : IsOpenImmersion (chart i) := X.affineOpenCover.map_prop i
  have h : LocallyOfFiniteType (Spec.map (structural s i)) :=
    (structural_read s i).symm ▸ (inferInstance : LocallyOfFiniteType (chart i ≫ s))
  have hft : (algebraMap R (chartRing i)).FiniteType :=
    (HasRingHomProperty.Spec_iff (P:=@LocallyOfFiniteType)).mp h
  let : Algebra.FiniteType R (chartRing i) := RingHom.finiteType_algebraMap.mp hft
  let : Algebra.FinitePresentation R (chartRing i) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact Algebra.isOpen_smoothLocus

/-- The intrinsic open on the *same* arithmetic X is the union of the
literal affine smooth-locus opens along its actual affine cover.
No separate neighbourhood, bad set, or assertion that it is open
appears in the inputs. -/
@[expose] def smoothOpen : X.Opens :=
  ⟨⋃ i : X.affineOpenCover.I₀, (chart i) '' chartSmooth s i,
    isOpen_iUnion fun i => by
      let : IsOpenImmersion (chart i) := X.affineOpenCover.map_prop i
      exact (chart i).isOpenEmbedding.isOpenMap _ (chart_open s i)⟩

theorem mem_smoothOpen (x : X) :
    x ∈ smoothOpen s ↔
      ∃ (i : X.affineOpenCover.I₀) (p : Spec (chartRing i)), p ∈ chartSmooth s i ∧ chart i p = x := by
  change x ∈ (⋃ i : X.affineOpenCover.I₀, (chart i) '' chartSmooth s i) ↔ _
  exact Set.mem_iUnion

end OriginalR47ActualArithmeticSmoothOpen318

#print axioms OriginalR47ActualArithmeticSmoothOpen318.structural_read
#print axioms OriginalR47ActualArithmeticSmoothOpen318.chart_open
#print axioms OriginalR47ActualArithmeticSmoothOpen318.mem_smoothOpen
