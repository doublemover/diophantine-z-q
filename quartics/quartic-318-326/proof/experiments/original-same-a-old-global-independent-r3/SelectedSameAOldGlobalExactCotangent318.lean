module

public import SelectedSameAOldFibreRingSquare318
public import SelectedSameAOldChartArrows318
public import SelectedSameAOldMarkedCompositeZero318
public import SelectedActualAdditiveStalkLocalExact318

/-!
# Additive short exactness of the old family's original cotangent row

Actual smoothness and the one literal old Cartesian fibre are the inputs.
No directional row, tangent map, or same-row comparison is needed.
-/

public section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace SelectedSameAOldGlobalExactCotangent318

universe u
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open SelectedSameAOldMarkedCompositeZero318
open SelectedSameAOldFibreRingSquare318
open SelectedSameAOldChartArrows318
open SelectedSameAAffineStructureScalar318
open SelectedActualAdditiveStalkLocalExact318

variable {k T : Type u} [Field k] [CommRing T] [Algebra k T]
variable {A P : Scheme.{u}}
variable (p : P ⟶ Spec (CommRingCat.of T)) (i : A ⟶ P)
variable (a : A ⟶ Spec (CommRingCat.of k)) (x : T →ₐ[k] k)
variable (J : IsPullback i a p (Spec.map (CommRingCat.ofHom x.toRingHom)))

@[expose] def totalOverK : P ⟶ Spec (CommRingCat.of k) := p ≫ Spec.algebraMap k T

include J in
theorem original_closed : IsClosedImmersion i := by
  have hx : Function.Surjective x.toRingHom := fun c => ⟨algebraMap k T c, x.commutes c⟩
  have hc : IsClosedImmersion (Spec.map (CommRingCat.ofHom x.toRingHom)) := IsClosedImmersion.spec_of_surjective _ hx
  exact MorphismProperty.of_isPullback J.flip hc

include J in
/-- Actual smooth chart and genuine affine fibre supply the split
old row on that chart, without assuming any of its actual rings. -/
theorem original_split_on_affine [Smooth p] [IsClosedImmersion i]
    {U : P.Opens} (hU : IsAffineOpen U) :
    Nonempty (((oldDirect p i a x J.w).map
      (Scheme.Modules.restrictFunctor (hU.preimage i).fromSpec)).Splitting) := by
  let V := i ⁻¹ᵁ U
  let hV : IsAffineOpen V := hU.preimage i
  let C := Γ(P, U)
  let B := Γ(A, V)
  letI : Algebra T C := (scalar p U).toAlgebra
  letI : Algebra T k := x.toRingHom.toAlgebra
  letI : Algebra C B := (i.app U).hom.toAlgebra
  letI : Algebra k B := (scalar a V).toAlgebra
  letI : Algebra k C := ((algebraMap T C).comp (algebraMap k T)).toAlgebra
  letI : Algebra T B := ((algebraMap C B).comp (algebraMap T C)).toAlgebra
  letI : IsScalarTower k T C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsScalarTower T C B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have jp := SelectedSameAOldFibreRingSquare318.actual_old_affine_ring_pushout p i a
    x.toRingHom J hU
  have he (t : T) : algebraMap T B t = algebraMap k B (algebraMap T k t) :=
    congrArg (fun f => f t) jp.w.symm
  letI : IsScalarTower T k B := IsScalarTower.of_algebraMap_eq he
  letI : IsScalarTower k C B := IsScalarTower.of_algebraMap_eq fun c => by
    change algebraMap k B c = algebraMap T B (algebraMap k T c)
    rw [he]
    congr 1
    exact (x.commutes c).symm
  letI : Algebra.IsPushout T k C B := CommRingCat.isPushout_iff_isPushout.mp jp
  letI : Algebra.Smooth T C :=
    RingHom.smooth_algebraMap.mp (SelectedSameAOldFibreRingSquare318.actual_smooth_scalar p hU)
  let j := hU.fromSpec
  let l := hV.fromSpec
  have hpj : j ≫ p = Spec.algebraMap T C :=
    affine_structure_from_scalar p hU
  have hqj : j ≫ totalOverK p = Spec.algebraMap k C := by
    unfold totalOverK
    rw [← Category.assoc, hpj, ← Spec.map_comp] <;> rfl
  have hal : l ≫ a = Spec.algebraMap k B :=
    affine_structure_from_scalar a hV
  have hsq : l ≫ i = Spec.algebraMap C B ≫ j := by
    symm
    change Spec.map (i.app U) ≫ hU.fromSpec = hV.fromSpec ≫ i
    rw [Scheme.Hom.app_eq_appLE]
    exact IsAffineOpen.SpecMap_appLE_fromSpec i hU hV le_rfl
  let hiK : i ≫ totalOverK p = a := old_marked_over_field p i a x J.w
  let c := SelectedSameAOldCotangentFibreSplit318.oldFibreRow k T C B
  let R := (oldDirect p i a x J.w).map (Scheme.Modules.restrictFunctor l)
  let til := tilde.functor (CommRingCat.of B)
  letI : til.Additive := by
    constructor
    intro M N f g
    exact AlgebraicGeometry.tilde.map_add f g
  letI : til.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive til
  have hl := old_left_normalized p (totalOverK p) i j l rfl hqj hpj hsq
  have hg := old_right_normalized (totalOverK p) a i j l hiK hqj hal hsq
  have e : R ≅ c.map til := ShortComplex.isoMk (oldSource p i j l hpj hsq)
      (oldMiddle (totalOverK p) i j l hqj hsq) (oldTarget a l hal) hl.symm hg.symm
  obtain ⟨sp⟩ := SelectedSameAOldCotangentFibreSplit318.oldFibreRow_split k T C B
  exact ⟨(sp.map til).ofIso e.symm⟩

variable [hSite : HasSheafify
  (_root_.Opens.grothendieckTopology (A : TopCat.{u})) AddCommGrpCat.{u}]

include J hSite in
/-- The native hOld input for the exact direct original row. The actual old
family supplies each affine splitting; the genuine additive sheaf row is
short exact by the checked open-cover criterion. -/
theorem original_additive_short_exact [Smooth p] :
    ((oldDirect p i a x J.w).map (actualAdditive A)).ShortExact := by
  letI : IsClosedImmersion i := original_closed p i a x J
  let I := {U : P.Opens // IsAffineOpen U}
  let W (j : I) := Spec Γ(A, i ⁻¹ᵁ j.1)
  let j (c : I) : W c ⟶ A := (c.2.preimage i).fromSpec
  letI : ∀ c : I, IsOpenImmersion (j c) := fun c =>
    inferInstanceAs (IsOpenImmersion (c.2.preimage i).fromSpec)
  have cover (v : A) : ∃ (c : I) (y : W c), j c y = v := by
    obtain ⟨_, ⟨U, hU, rfl⟩, hv, _⟩ := P.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (i v)) isOpen_univ
    let c : I := ⟨U, hU⟩
    have hV : v ∈ i ⁻¹ᵁ U := hv
    refine ⟨c, ?_⟩
    change v ∈ Set.range (hU.preimage i).fromSpec
    rwa [IsAffineOpen.range_fromSpec]
  exact SelectedActualAdditiveStalkLocalExact318.short_exact_of_open_splitting
    (oldDirect p i a x J.w) W j cover
    (fun c => original_split_on_affine p i a x J c.2)

end SelectedSameAOldGlobalExactCotangent318
