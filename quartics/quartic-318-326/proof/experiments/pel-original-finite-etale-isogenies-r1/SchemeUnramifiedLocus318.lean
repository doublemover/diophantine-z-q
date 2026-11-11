module
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.RingTheory.Unramified.Locus
public section
noncomputable section
namespace SchemeUnramifiedLocus318
open AlgebraicGeometry CategoryTheory TopologicalSpace RingHom
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
lemma formallyUnramified_stalkMap_iff {f : X ⟶ Y} {x : X} (U : Y.Opens)
      (hU : IsAffineOpen U) (V : X.Opens) (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U)
      (hx : x ∈ V) :
    letI := (f.appLE U V hVU).hom.toAlgebra
    (f.stalkMap x).hom.FormallyUnramified ↔
      hV.primeIdealOf ⟨x, hx⟩ ∈ Algebra.unramifiedLocus Γ(Y, U) Γ(X, V) := by
  let := (f.appLE U V hVU).hom.toAlgebra
  let p := (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal
  let q := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  have : q.LiesOver p :=
    ⟨congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hx).1).symm⟩
  let := Localization.AtPrime.algebraOfLiesOver p q
  trans Algebra.FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime q)
  · rw [← formallyUnramified_algebraMap]
    exact RingHom.FormallyUnramified.respectsIso.arrow_mk_iso_iff
      (IsAffineOpen.arrowStalkMapIso f U hU V hV hVU hx)
  · exact by
      constructor
      · intro H
        letI := H
        letI : Algebra.FormallyUnramified Γ(Y, U) (Localization.AtPrime p) :=
          Algebra.FormallyUnramified.of_isLocalization p.primeCompl
        exact Algebra.FormallyUnramified.comp Γ(Y, U) (Localization.AtPrime p) _
      · intro H
        letI := H
        exact Algebra.FormallyUnramified.of_restrictScalars Γ(Y, U)
          (Localization.AtPrime p) (Localization.AtPrime q)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma exists_unramified_of_formallyUnramified_stalk
    (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (x : X) (H : (f.stalkMap x).hom.FormallyUnramified) :
    ∃ (U : Y.Opens) (_ : IsAffineOpen U) (V : X.Opens) (_ : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U),
      x ∈ V ∧ (f.appLE U V hVU).hom.FormallyUnramified := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.2.preimage f.continuous)
  have := f.finitePresentation_appLE hU hV hVU
  algebraize [(f.appLE U V hVU).hom]
  have : Algebra.IsUnramifiedAt _ _ := (formallyUnramified_stalkMap_iff U hU V hV hVU hxV).mp H
  obtain ⟨r, hrx, hr⟩ := Algebra.exists_formallyUnramified_of_isUnramifiedAt (R := Γ(Y, U))
    (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  refine ⟨_, hU, _, hV.basicOpen r, (X.basicOpen_le r).trans hVU, ?_, ?_⟩
  · rwa [← PrimeSpectrum.mem_basicOpen, IsAffineOpen.primeIdealOf,
      ← hV.fromSpec_preimage_basicOpen, Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply,
      IsAffineOpen.isoSpec_hom, IsAffineOpen.toSpecΓ_fromSpec] at hrx
  · have := hV.isLocalization_basicOpen r
    rw [← RingHom.formallyUnramified_algebraMap] at hr
    convert
      RingHom.FormallyUnramified.propertyIsLocal.respectsIso.1 _
        (IsLocalization.algEquiv (.powers r) _ Γ(X, X.basicOpen r)).toRingEquiv hr
    ext
    dsimp
    simp only [IsScalarTower.algebraMap_apply Γ(Y, U) Γ(X, V) (Localization _),
      IsLocalization.map_eq]
    simp only [algebraMap_toAlgebra, RingHomCompTriple.comp_apply, ← ConcreteCategory.comp_apply,
      Scheme.Hom.appLE_map]

lemma isOpen_locus [LocallyOfFinitePresentation f] :
    IsOpen { x | (f.stalkMap x).hom.FormallyUnramified } := by
  refine isOpen_iff_forall_mem_open.mpr fun x hx ↦ ?_
  obtain ⟨U, hU, V, hV, hVU, hxV, H⟩ := exists_unramified_of_formallyUnramified_stalk f x hx
  algebraize [(f.appLE U V hVU).hom]
  exact ⟨V, fun y hy ↦ (formallyUnramified_stalkMap_iff U hU V hV hVU hy).mpr
    (inferInstanceAs (Algebra.IsUnramifiedAt _ _)), V.2, hxV⟩

/-- The genuine open set of points formally unramified over a base, as a `Scheme.Opens`. -/
def locus (f : X ⟶ Y) [LocallyOfFinitePresentation f] : X.Opens :=
  ⟨{ x | (f.stalkMap x).hom.FormallyUnramified }, isOpen_locus f⟩

lemma mem_locus {f : X ⟶ Y} [LocallyOfFinitePresentation f] {x : X} :
    x ∈ locus f ↔ (f.stalkMap x).hom.FormallyUnramified := .rfl

lemma locus_eq_top (f : X ⟶ Y) [LocallyOfFinitePresentation f] [FormallyUnramified f] :
    locus f = ⊤ := by
  rw [← top_le_iff]
  rintro x -
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.2.preimage f.continuous)
  have := f.formallyUnramified_appLE hU hV hVU
  algebraize [(f.appLE U V hVU).hom]
  rw [mem_locus, formallyUnramified_stalkMap_iff U hU V hV hVU hxV]
  exact inferInstanceAs (Algebra.IsUnramifiedAt _ _)

set_option backward.isDefEq.respectTransparency.types false in
lemma locus_eq_top_iff {f : X ⟶ Y} [LocallyOfFinitePresentation f] :
    locus f = ⊤ ↔ FormallyUnramified f := by
  refine ⟨fun H ↦ ?_, fun _ ↦ locus_eq_top f⟩
  refine IsZariskiLocalAtSource.iff_exists_resLE.mpr fun x ↦ ?_
  obtain ⟨U, hU, V, hV, hVU, hxV, H⟩ :=
    exists_unramified_of_formallyUnramified_stalk f _ (H.ge (Set.mem_univ x))
  refine ⟨U, V, hxV, hVU, ?_⟩
  have : IsAffine _ := hU
  have : IsAffine _ := hV
  rw [HasRingHomProperty.iff_of_isAffine (P := @FormallyUnramified)]
  exact (RingHom.FormallyUnramified.propertyIsLocal.respectsIso.arrow_mk_iso_iff
    (arrowResLEAppIso f U V hVU)).mpr H

lemma preimage_locus_eq {U : Scheme.{u}}
    (f : U ⟶ X) (g : X ⟶ Y) [IsOpenImmersion f] [LocallyOfFinitePresentation g] :
    f ⁻¹ᵁ locus g = locus (f ≫ g) := by
  ext x
  refine (RingHom.FormallyUnramified.respectsIso.cancel_right_isIso _ (f.stalkMap x)).symm.trans ?_
  rw [← CommRingCat.hom_comp, ← stalkMap_comp]
  rfl

end SchemeUnramifiedLocus318
