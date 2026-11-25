module
public import OriginalR47RetainedAffineSpread318
public import OriginalR47RetainedTraitLift318
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Properties
public section
noncomputable section

namespace OriginalR47RetainedPrincipalCover318

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set
open OriginalR47TraitRoundKernel318 (base trait brace)
open OriginalR47RetainedTraitLift318 (eta etaAt etaAt_read)
open OriginalR47RetainedAffineSpread318 (toLocal)
open scoped nonZeroDivisors
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {R : Type u} [CommRing R] [IsDomain R]
local notation "B" => base (R:=R)
local notation "K" => FractionRing R
local notation "G" => Spec (CommRingCat.of K)

abbrev opening (d : R) : Spec (CommRingCat.of (Localization.Away d)) ⟶ B :=
  Spec.algebraMap R (Localization.Away d)

@[expose] def fracAway (d : R) (hd : d ≠ 0) : Localization.Away d →ₐ[R] K :=
  IsLocalization.liftAlgHom (M := Submonoid.powers d) (f := Algebra.ofId R K) fun t =>
    IsLocalization.map_units K
      (⟨(t : R), powers_le_nonZeroDivisors_of_noZeroDivisors hd t.property⟩ : R⁰)

abbrev overGeneric (d : R) (hd : d ≠ 0) : G ⟶ Spec (CommRingCat.of (Localization.Away d)) :=
  Spec.map (CommRingCat.ofHom (fracAway d hd).toRingHom)

theorem opening_generic (d : R) (hd : d ≠ 0) :
    overGeneric d hd ≫ opening d = eta (R:=R) := by
  change Spec.map (CommRingCat.ofHom (fracAway d hd).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away d))) =
    Spec.map (CommRingCat.ofHom (algebraMap R K))
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact (fracAway d hd).commutes x

/-- The generic point of each true old trait restricts to exactly the
same generic arrow of the principal open. This tests the whole map
of localization rings over R, not merely the image point. -/
theorem local_generic (p : Ideal R) [p.IsPrime] (d : R) (hd : d ∉ p) :
    etaAt p ≫ toLocal p d hd = overGeneric d (fun h => hd (h.symm ▸ p.zero_mem)) := by
  let hd₀ : d ≠ 0 := fun h => hd (h.symm ▸ p.zero_mem)
  let c := OriginalR47RetainedDenominatorSpread318.canonical p d hd
  change Spec.map (CommRingCat.ofHom (algebraMap (Localization.AtPrime p) K)) ≫
    Spec.map (CommRingCat.ofHom c.toRingHom) = Spec.map (CommRingCat.ofHom (fracAway d hd₀).toRingHom)
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply IsLocalization.ringHom_ext (Submonoid.powers d)
  apply RingHom.ext
  intro r
  change algebraMap (Localization.AtPrime p) K (c (algebraMap R (Localization.Away d) r)) =
    fracAway d hd₀ (algebraMap R (Localization.Away d) r)
  rw [c.commutes,(fracAway d hd₀).commutes]
  exact (IsScalarTower.algebraMap_apply R (Localization.AtPrime p) K r).symm

/-- The whole original fraction-field arrow has its single value
at the genuine generic base point. -/
theorem eta_point (x : G) : eta (R:=R) x = genericPoint B := by
  have hx : x = (⊥ : PrimeSpectrum K) := Subsingleton.elim _ _
  rw [hx,genericPoint_eq_bot_of_affine]
  apply PrimeSpectrum.ext
  change (⊥ : Ideal K).comap (algebraMap R K) = ⊥
  ext a
  change (algebraMap R K a ∈ (⊥ : Ideal K)) ↔ a ∈ (⊥ : Ideal R)
  simp only [Ideal.mem_bot]
  constructor
  · intro he
    exact (IsFractionRing.injective R K) (he.trans (map_zero (algebraMap R K)).symm)
  · intro he
    exact he.symm ▸ map_zero (algebraMap R K)

/-- The actual original fraction-field arrow is dominant on the original
arithmetic base. Its image contains the genuine generic prime. -/
theorem eta_dominates : IsDominant (eta (R:=R)) := by
  refine ⟨(show Dense ({genericPoint B} : Set B) from
    (dense_iff_closure_eq.mpr (genericPoint_closure B))).mono ?_⟩
  intro x hx
  obtain rfl := Set.mem_singleton_iff.mp hx
  exact ⟨(⊥ : PrimeSpectrum K),eta_point _⟩

variable {Y : Scheme.{u}} [Y.IsSeparated]

/-- Actual global section from its true local lifts and a single common
whole generic map. Use a principal cover of the original arithmetic
base, its actual pairwise scheme pullbacks, and equality over the given
separated resolved scheme. No rational-map quotient is used. -/
theorem glue (t : Y ⟶ B) [LocallyOfFiniteType t] (Pη : G ⟶ Y)
    (loc : ∀ x : PrimeSpectrum R, ∃ φ : trait x.asIdeal ⟶ Y,
      φ ≫ t = brace x.asIdeal ∧ etaAt x.asIdeal ≫ φ = Pη) :
    ∃! Q : B ⟶ Y, eta (R:=R) ≫ Q = Pη := by
  classical
  choose φ hφ hφη using loc
  have hSP (x : PrimeSpectrum R) :=
    OriginalR47RetainedAffineSpread318.at_local t x.asIdeal (φ x) (hφ x)
  choose d hd F hF using hSP
  have hd₀ (x : PrimeSpectrum R) : d x ≠ 0 := fun h => hd x (h.symm ▸ x.asIdeal.zero_mem)
  have htop : Ideal.span (Set.range d) = ⊤ := by
    by_contra hn
    obtain ⟨m,hm,H⟩ := Ideal.exists_le_maximal _ hn
    let x : PrimeSpectrum R := ⟨m,hm.isPrime⟩
    exact hd x (H (Ideal.subset_span ⟨x,rfl⟩))
  let C : Scheme.OpenCover B :=
    (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of R)
      (ι := PrimeSpectrum R) d htop).openCover
  let g (i : C.I₀) : G ⟶ C.X i := overGeneric (d i) (hd₀ i)
  have hg (i : C.I₀) : g i ≫ C.f i = eta (R:=R) := opening_generic (d i) (hd₀ i)
  have hFg (i : C.I₀) : g i ≫ F i = Pη := by
    change overGeneric (d i) (hd₀ i) ≫ F i = Pη
    rw [← local_generic i.asIdeal (d i) (hd i), Category.assoc, hF i, hφη i]
  let : IsDominant (eta (R:=R)) := eta_dominates
  have hpair (i j : C.I₀) :
      pullback.fst (C.f i) (C.f j) ≫ F i = pullback.snd _ _ ≫ F j := by
    let V := pullback (C.f i) (C.f j)
    let l : G ⟶ V := pullback.lift (g i) (g j) ((hg i).trans (hg j).symm)
    let j₁ : V ⟶ C.X i := pullback.fst (C.f i) (C.f j)
    let j₂ : V ⟶ C.X j := pullback.snd (C.f i) (C.f j)
    have hl₁ : l ≫ j₁ = g i := pullback.lift_fst _ _ _
    have hl₂ : l ≫ j₂ = g j := pullback.lift_snd _ _ _
    let : IsOpenImmersion j₁ := MorphismProperty.pullback_fst _ _ (C.map_prop j)
    let : IsOpenImmersion (C.f i) := C.map_prop i
    let : IsReduced V := isReduced_of_isOpenImmersion (j₁ ≫ C.f i)
    have hh : l ≫ (j₁ ≫ C.f i) = eta (R:=R) := by rw [← Category.assoc, hl₁, hg i]
    let : IsDominant (l ≫ (j₁ ≫ C.f i)) := hh.symm ▸ (inferInstance : IsDominant (eta (R:=R)))
    let : IsDominant l := IsDominant.of_comp_of_isOpenImmersion l (j₁ ≫ C.f i)
    apply AlgebraicGeometry.ext_of_isDominant l
    change l ≫ (j₁ ≫ F i) = l ≫ (j₂ ≫ F j)
    rw [← Category.assoc, hl₁, hFg i, ← Category.assoc, hl₂, hFg j]
  let Q := C.glueMorphisms F hpair
  have hQ : eta (R:=R) ≫ Q = Pη := by
    let i : C.I₀ := (⊥ : PrimeSpectrum R)
    rw [← hg i, Category.assoc, C.ι_glueMorphisms F hpair i, hFg i]
  exact ⟨Q,hQ,fun Q' hQ' => AlgebraicGeometry.ext_of_isDominant (eta (R:=R)) (hQ'.trans hQ.symm)⟩

end OriginalR47RetainedPrincipalCover318

#print axioms OriginalR47RetainedPrincipalCover318.opening_generic
#print axioms OriginalR47RetainedPrincipalCover318.local_generic
#print axioms OriginalR47RetainedPrincipalCover318.eta_point
#print axioms OriginalR47RetainedPrincipalCover318.eta_dominates
#print axioms OriginalR47RetainedPrincipalCover318.glue
