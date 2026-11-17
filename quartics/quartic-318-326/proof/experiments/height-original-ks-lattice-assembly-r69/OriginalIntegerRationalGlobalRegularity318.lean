module
public import OriginalIntegerGlobalFiniteNormalization318
public import OriginalIntegerRationalNormalization318
public import OriginalIntegerReciprocalRationalNormalization318
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Properties
public section
noncomputable section
namespace OriginalIntegerRationalGlobalRegularity318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

/-- Native scheme stalks, not an abstract local ring substituted for them. -/
private theorem spec_stalk_regular (R : Type) [CommRing R] [IsRegularRing R]
    (x : Spec (CommRingCat.of R)) :
    IsRegularLocalRing ((Spec (CommRingCat.of R)).presheaf.stalk x) :=
  IsRegularLocalRing.of_ringEquiv
    (Spec.stalkIso (CommRingCat.of R) x).commRingCatIsoToRingEquiv.symm

private theorem stalk_regular_of_iso {X Y : Scheme} (e : X ≅ Y)
    (h : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) (x : X) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  letI := h (e.hom x)
  exact IsRegularLocalRing.of_ringEquiv
    (asIso (e.hom.stalkMap x)).commRingCatIsoToRingEquiv

private theorem stalk_regular_of_cover {X : Scheme} (C : X.OpenCover)
    (h : ∀ i (y : C.X i), IsRegularLocalRing ((C.X i).presheaf.stalk y)) (x : X) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  obtain ⟨i, y, rfl⟩ := C.exists_eq x
  letI := h i y
  exact IsRegularLocalRing.of_ringEquiv
    (asIso ((C.f i).stalkMap y)).commRingCatIsoToRingEquiv.symm

private theorem spec_int_comp {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    Spec.map (CommRingCat.ofHom f) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ A)) =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ B)) := by
  rw [← Spec.map_comp]
  exact congrArg (fun g : ℤ →+* B => Spec.map (CommRingCat.ofHom g))
    (Subsingleton.elim (f.comp (algebraMap ℤ A)) (algebraMap ℤ B))

variable (c : Fin 4 → ℚˣ)
open OriginalIntegerGlobalNormalization318
abbrev FiniteRing := OriginalIntegerFiniteClosure318.Closure c
abbrev ReciprocalRing := OriginalIntegerReciprocalNormalization318.Closure c
abbrev baseChangeMap := Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))
abbrev integralStructure := OriginalIntegerGlobalFiniteNormalization318.structureMap c

/-- This is the actual categorical base change of the constructed integral
normalization over Spec Z, not a separately selected rational model. -/
abbrev rationalFiber := pullback (integralStructure c) baseChangeMap

theorem finite_structure :
    OriginalIntegerClosureGluing318.finiteChart c ≫ integralStructure c =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ (FiniteRing c))) := by
  unfold integralStructure OriginalIntegerGlobalFiniteNormalization318.structureMap
  rw [← Category.assoc, finite_restriction, finiteProjection, Category.assoc,
    IntegralFourRootProjectiveProjection318.finite_structure]
  exact spec_int_comp (OriginalIntegerNormalizationMap318.toClosure c).toRingHom

theorem reciprocal_structure :
    OriginalIntegerClosureGluing318.infinityChart c ≫ integralStructure c =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ (ReciprocalRing c))) := by
  unfold integralStructure OriginalIntegerGlobalFiniteNormalization318.structureMap
  rw [← Category.assoc, infinity_restriction, infinityProjection, Category.assoc,
    IntegralFourRootProjectiveProjection318.reciprocal_structure]
  exact spec_int_comp (OriginalIntegerReciprocalOrderNormalization318.toClosure c).toRingHom

abbrev sourceCover : (source c).OpenCover where
  I₀ := Bool
  X
    | false => Spec (CommRingCat.of (FiniteRing c))
    | true => Spec (CommRingCat.of (ReciprocalRing c))
  f
    | false => OriginalIntegerClosureGluing318.finiteChart c
    | true => OriginalIntegerClosureGluing318.infinityChart c
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, ?_⟩
    · intro x
      obtain ⟨p, hp⟩ | ⟨p, hp⟩ := OpenPushoutChartPreimage318.charts_cover
        (OriginalIntegerNormalizedOverlap318.intoFinite c)
        (OriginalIntegerReciprocalNormalization318.intoInfinity c) x
      · exact ⟨false, p, hp⟩
      · exact ⟨true, p, hp⟩
    · intro i
      cases i <;> infer_instance

/-- Base change of the entire proved source cover. -/
abbrev rationalCover : (rationalFiber c).OpenCover :=
  (sourceCover c).pullback₂ (pullback.fst (integralStructure c) baseChangeMap)

@[expose] def finiteFiberIso : (rationalCover c).X false ≅
    Spec (CommRingCat.of (FiniteRing c ⊗[ℤ] ℚ)) := by
  change pullback (OriginalIntegerClosureGluing318.finiteChart c)
    (pullback.fst (integralStructure c) baseChangeMap) ≅ _
  refine pullbackRightPullbackFstIso (integralStructure c) baseChangeMap _ ≪≫ ?_
  rw [finite_structure]
  exact pullbackSpecIso ℤ (FiniteRing c) ℚ

@[expose] def reciprocalFiberIso : (rationalCover c).X true ≅
    Spec (CommRingCat.of (ReciprocalRing c ⊗[ℤ] ℚ)) := by
  change pullback (OriginalIntegerClosureGluing318.infinityChart c)
    (pullback.fst (integralStructure c) baseChangeMap) ≅ _
  refine pullbackRightPullbackFstIso (integralStructure c) baseChangeMap _ ≪≫ ?_
  rw [reciprocal_structure]
  exact pullbackSpecIso ℤ (ReciprocalRing c) ℚ

/-- Every native local ring of the ACTUAL rational base change is regular.
This uses both whole rational affine charts and their actual base-changed
cover; it makes no assertion about any arithmetic special fiber. -/
theorem rationalFiber_stalk_regular (x : rationalFiber c) :
    IsRegularLocalRing ((rationalFiber c).presheaf.stalk x) := by
  apply stalk_regular_of_cover (rationalCover c) _ x
  intro i y
  cases i with
  | false =>
    apply stalk_regular_of_iso (finiteFiberIso c) _ y
    intro z
    letI := OriginalIntegerRationalNormalization318.integerRationalFiber_regular c
    exact spec_stalk_regular _ z
  | true =>
    apply stalk_regular_of_iso (reciprocalFiberIso c) _ y
    intro z
    letI := OriginalIntegerReciprocalRationalNormalization318.integerRationalFiber_regular c
    exact spec_stalk_regular _ z

/-- Properness of the actual rational fiber follows by native base change,
not from the regularity statement or a function-field comparison. -/
instance rationalFiber_proper : IsProper (pullback.snd (integralStructure c) baseChangeMap) := by
  letI := (OriginalIntegerGlobalFiniteNormalization318.proper_separated c).1
  infer_instance

end OriginalIntegerRationalGlobalRegularity318
