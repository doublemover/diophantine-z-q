module

public import SelectedSameAActualOpenChartSplit318
public import SelectedSameAActualAffineFibre318
public import SelectedActualAdditiveStalkLocalExact318
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import all SelectedSameAActualFibreSheafArrows318
import all SelectedSameADualNumberFlatCoefficient318
import all SelectedSameAAffineStructureScalar318

/-!
# Short exactness of the original actual closed-fibre differential row

Input one genuine smooth family over dual numbers and its actual fibre
square. The algebras, the relevant pointwise cover, and both affine arrows
are constructed from the actual scheme data; no exact sequence is supplied.
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace SelectedSameAGlobalActualClosedFibreRow318

universe u
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open SelectedSameAActualFibreSheafArrows318
open SelectedSameAAffineStructureScalar318

variable {k : Type u} [CommRing k]
variable {X A : Scheme.{u}} (σ : X ⟶ spec (D k)) (ρ : A ⟶ X) (a : A ⟶ spec k)

/-- The original structure projection is a genuine closed immersion;
its closedness transfers to the actual fibre square. -/
theorem actual_fibre_closed (H : IsPullback ρ a σ (sMap (pr k))) : IsClosedImmersion ρ := by
  have hp : Function.Surjective (pr k) := by
    intro b
    exact ⟨TrivSqZeroExt.inl b, TrivSqZeroExt.fst_inl k b⟩
  have hc : IsClosedImmersion (sMap (pr k)) :=
    IsClosedImmersion.spec_of_surjective _ hp
  exact MorphismProperty.of_isPullback H.flip hc

/-- Compute the splitting on the actual inverse image of an arbitrary affine
open of the same deformation. All algebras are read off from the given maps. -/
theorem split_on_actual_affine [Smooth σ] [IsClosedImmersion ρ]
    (H : IsPullback ρ a σ (sMap (pr k))) {U : X.Opens} (hU : IsAffineOpen U) :
    Nonempty (((moduleComplex σ ρ a H.w).map
      (Scheme.Modules.restrictFunctor (hU.preimage ρ).fromSpec)).Splitting) := by
  let V := ρ ⁻¹ᵁ U
  let hV : IsAffineOpen V := hU.preimage ρ
  let C := Γ(X, U)
  let B := Γ(A, V)
  letI : Algebra (D k) C := (scalar σ U).toAlgebra
  letI : Algebra k C := (scalar (xOverK σ) U).toAlgebra
  letI : Algebra k B := (scalar a V).toAlgebra
  letI : Algebra C B := (ρ.app U).hom.toAlgebra
  let j := hU.fromSpec
  let l := hV.fromSpec
  have hz : j ≫ σ = sMap (algebraMap (D k) C) :=
    SelectedSameAActualAffineFibre318.affine_structure_from_scalar σ hU
  have hu : j ≫ xOverK σ = sMap (algebraMap k C) :=
    SelectedSameAActualAffineFibre318.affine_structure_from_scalar (xOverK σ) hU
  have hv : l ≫ a = sMap (algebraMap k B) :=
    SelectedSameAActualAffineFibre318.affine_structure_from_scalar a hV
  have hsq : l ≫ ρ = sMap (algebraMap C B) ≫ j := by
    symm
    change Spec.map (ρ.app U) ≫ hU.fromSpec = hV.fromSpec ≫ ρ
    rw [Scheme.Hom.app_eq_appLE]
    exact IsAffineOpen.SpecMap_appLE_fromSpec ρ hU hV le_rfl
  have hr : CommRingCat.ofHom (algebraMap k C) ≫ CommRingCat.ofHom (algebraMap C B) =
      CommRingCat.ofHom (algebraMap k B) := by
    apply Spec.map_injective
    rw [Spec.map_comp]
    change sMap (algebraMap C B) ≫ sMap (algebraMap k C) = sMap (algebraMap k B)
    rw [← hu, ← Category.assoc, ← hsq, Category.assoc, fibre_over_k σ ρ a H.w, hv]
  have hrt (b : k) : algebraMap C B (algebraMap k C b) = algebraMap k B b :=
    congrArg (fun q => q b) hr
  letI : IsScalarTower k C B := IsScalarTower.of_algebraMap_eq (fun b => (hrt b).symm)
  let ρr : C →ₐ[k] B :=
    { __ := algebraMap C B
      commutes' := hrt }
  letI : Module.Flat (D k) C :=
    RingHom.flat_algebraMap_iff.mp (scalar_flat σ hU)
  letI : Smooth a := MorphismProperty.of_isPullback H (inferInstance : Smooth σ)
  have hSmooth : Smooth (sMap (algebraMap k B)) := hv ▸ (inferInstance : Smooth (l ≫ a))
  have hRing : (algebraMap k B).Smooth :=
    (HasRingHomProperty.Spec_iff (P := @Smooth)).mp hSmooth
  letI : Algebra.Smooth k B := RingHom.smooth_algebraMap.mp hRing
  obtain ⟨hsurj, hker⟩ := SelectedSameAActualAffineFibre318.actual_chart_reduction σ ρ a H hU
  have hred : algebraMap C B = (ρ.app U).hom := rfl
  have hε : SelectedSameADualNumberFlatCoefficient318.epsilonIn k C =
      scalar σ U (SelectedSameADualNumberFibreKernel318.ε k) := by
    unfold SelectedSameADualNumberFlatCoefficient318.epsilonIn
      SelectedSameADualNumberFlatCoefficient318.epsilon
    rfl
  have hk : RingHom.ker (algebraMap C B) = Ideal.span
      ({SelectedSameADualNumberFlatCoefficient318.epsilonIn k C} : Set C) := by
    rw [hred, hε]
    exact hker
  have hs : Function.Surjective (algebraMap C B) := by
    rw [hred]
    exact hsurj
  exact SelectedSameAActualOpenChartSplit318.actual_open_chart_split σ ρ a H.w j l hz hsq hu hv
    ρr rfl hk hs

variable [HasSheafify (_root_.Opens.grothendieckTopology (A : TopCat.{u})) AddCommGrpCat.{u}]

/-- Genuine additive short exactness from the actual smooth deformation and
the given pullback, with no assumed cover, affine sections, or splitting. -/
theorem actual_additive_short_exact [Smooth σ] (H : IsPullback ρ a σ (sMap (pr k))) :
    (additiveComplex σ ρ a H.w).ShortExact := by
  letI : IsClosedImmersion ρ := actual_fibre_closed σ ρ a H
  let I := {U : X.Opens // IsAffineOpen U}
  let W (i : I) := spec Γ(A, ρ ⁻¹ᵁ i.1)
  let j (i : I) : W i ⟶ A := (i.2.preimage ρ).fromSpec
  letI : ∀ i : I, IsOpenImmersion (j i) := fun i => inferInstanceAs
    (IsOpenImmersion (i.2.preimage ρ).fromSpec)
  have hCover (x : A) : ∃ (i : I) (y : W i), j i y = x := by
    obtain ⟨_, ⟨U, hU, rfl⟩, hx, _⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (ρ x)) isOpen_univ
    let i : I := ⟨U, hU⟩
    have hx' : x ∈ ρ ⁻¹ᵁ U := hx
    refine ⟨i, ?_⟩
    change x ∈ Set.range (hU.preimage ρ).fromSpec
    rwa [IsAffineOpen.range_fromSpec]
  exact SelectedActualAdditiveStalkLocalExact318.short_exact_of_open_splitting
    (moduleComplex σ ρ a H.w) W j hCover (fun i => split_on_actual_affine σ ρ a H i.2)

end SelectedSameAGlobalActualClosedFibreRow318
