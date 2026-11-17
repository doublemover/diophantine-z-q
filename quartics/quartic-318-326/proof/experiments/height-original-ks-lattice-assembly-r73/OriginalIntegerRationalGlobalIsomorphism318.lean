module
public import OriginalIntegerRationalGlobalComparison318
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public section
noncomputable section
namespace OriginalIntegerRationalGlobalIsomorphism318
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
open OriginalIntegerRationalGlobalRegularity318
open OriginalIntegerRationalTwoCover318
open OriginalIntegerRationalIntersectionProjections318
open OriginalIntegerRationalOverlapSquares318
variable (c : Fin 4 → ℚˣ)
local instance sourceField : Field (L c) :=
  (KummerTensorField318.source_raw_field c).toField

private theorem dominant_of_injective {R F : Type} [CommRing R] [CommRing F]
    (h : R →+* F) (hh : Function.Injective h) :
    IsDominant (Spec.map (CommRingCat.ofHom h)) := by
  constructor
  change DenseRange (PrimeSpectrum.comap h)
  apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical h).mpr
  rw [(RingHom.injective_iff_ker_eq_bot).mp hh]
  exact bot_le

local instance rationalSeparated : (rationalFiber c).IsSeparated := by
  letI := rationalFiber_proper c
  refine ⟨?_⟩
  have hs : IsSeparated (pullback.snd (integralStructure c) baseChangeMap ≫
      terminal.from (Spec (CommRingCat.of ℚ))) := inferInstance
  simpa only [terminal.comp_from] using hs

@[expose] def inverseLocal (i : Bool) : (originalCover c).X i ⟶ rationalFiber c := by
  cases i with
  | false => exact (finiteIso c).inv ≫ (rationalCover c).f false
  | true => exact (infinityIso c).inv ≫ (rationalCover c).f true

/-- Exact inverse-chart equality on the literal overlap, obtained from the
full SOURCE intersection, not from any claimed target preimage property. -/
theorem inverse_literal_overlap :
    Spec.map (CommRingCat.ofHom (fromFinite c)) ≫ inverseLocal c false =
    Spec.map (CommRingCat.ofHom (fromInfinity c)) ≫ inverseLocal c true := by
  apply (cancel_epi (OriginalIntegerRationalIntersectionProjections318.iso c).hom).mp
  change _ ≫ (_ ≫ ((finiteIso c).inv ≫ _)) =
    _ ≫ (_ ≫ ((infinityIso c).inv ≫ _))
  rw [← Category.assoc, finite_projection, Category.assoc,
    Iso.hom_inv_id_assoc, ← Category.assoc, infinity_projection,
    Category.assoc, Iso.hom_inv_id_assoc]
  exact pullback.condition

private theorem field_finite_square :
    Spec.map (CommRingCat.ofHom (overlapEmbedding c)) ≫
      Spec.map (CommRingCat.ofHom (fromFinite c)) =
    Spec.map (CommRingCat.ofHom (finiteEmbedding c)) := by
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((overlapEmbedding c).comp (fromFinite c))) = _
  rw [finite_square]

private theorem field_infinity_square :
    Spec.map (CommRingCat.ofHom (overlapEmbedding c)) ≫
      Spec.map (CommRingCat.ofHom (fromInfinity c)) =
    Spec.map (CommRingCat.ofHom (infinityEmbedding c)) := by
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((overlapEmbedding c).comp (fromInfinity c))) = _
  rw [infinity_square]

private theorem inverse_field_square :
    Spec.map (CommRingCat.ofHom (finiteEmbedding c)) ≫ inverseLocal c false =
    Spec.map (CommRingCat.ofHom (infinityEmbedding c)) ≫ inverseLocal c true := by
  rw [← field_finite_square, Category.assoc, inverse_literal_overlap,
    ← Category.assoc, field_infinity_square]

abbrev originalIntersection :=
  pullback ((originalCover c).f false) ((originalCover c).f true)

/-- The actual common original-field point lifted to the FULL original
chart intersection. -/
@[expose] def intersectionPoint : Spec (CommRingCat.of (L c)) ⟶ originalIntersection c :=
  pullback.lift (Spec.map (CommRingCat.ofHom (finiteEmbedding c)))
    (Spec.map (CommRingCat.ofHom (infinityEmbedding c)))
    ((OriginalIntegerRationalGenericPoint318.finite_tensor_point c).trans
      (OriginalIntegerRationalGenericPoint318.reciprocal_tensor_point c).symm)

private theorem intersectionPoint_dominant : IsDominant (intersectionPoint c) := by
  letI : IsDominant (Spec.map (CommRingCat.ofHom (finiteEmbedding c))) :=
    dominant_of_injective (finiteEmbedding c) (finiteEmbedding_injective c)
  letI : IsDominant (intersectionPoint c ≫
      pullback.fst ((originalCover c).f false) ((originalCover c).f true)) := by
    simpa only [intersectionPoint, pullback.lift_fst] using
      (inferInstance : IsDominant (Spec.map (CommRingCat.ofHom (finiteEmbedding c))))
  exact IsDominant.of_comp_of_isOpenImmersion (intersectionPoint c)
    (pullback.fst ((originalCover c).f false) ((originalCover c).f true))

private theorem originalIntersection_reduced : IsReduced (originalIntersection c) := by
  letI : _root_.IsReduced (Finite c ⊗[ℤ] ℚ) :=
    isReduced_of_injective (finiteEmbedding c) (finiteEmbedding_injective c)
  exact isReduced_of_isOpenImmersion
    (pullback.fst ((originalCover c).f false) ((originalCover c).f true))

/-- Equality of inverse charts on the FULL TARGET intersection follows
from its actual dominant field point, reducedness and separatedness of the
actual rational fiber. No equality of target preimages is assumed. -/
theorem inverse_cross :
    pullback.fst ((originalCover c).f false) ((originalCover c).f true) ≫ inverseLocal c false =
    pullback.snd ((originalCover c).f false) ((originalCover c).f true) ≫ inverseLocal c true := by
  letI := intersectionPoint_dominant c
  letI := originalIntersection_reduced c
  apply ext_of_isDominant (intersectionPoint c)
  simpa only [intersectionPoint, ← Category.assoc,
    pullback.lift_fst, pullback.lift_snd] using inverse_field_square c

theorem inverse_compatibility (i j : Bool) :
    pullback.fst ((originalCover c).f i) ((originalCover c).f j) ≫ inverseLocal c i =
    pullback.snd ((originalCover c).f i) ((originalCover c).f j) ≫ inverseLocal c j := by
  cases i <;> cases j
  · exact congrArg (fun f => f ≫ inverseLocal c false)
      ((cancel_mono ((originalCover c).f false)).mp pullback.condition)
  · exact inverse_cross c
  · apply (cancel_epi (pullbackSymmetry ((originalCover c).f false)
      ((originalCover c).f true)).hom).mp
    simpa only [← Category.assoc, pullbackSymmetry_hom_comp_fst,
      pullbackSymmetry_hom_comp_snd] using (inverse_cross c).symm
  · exact congrArg (fun f => f ≫ inverseLocal c true)
      ((cancel_mono ((originalCover c).f true)).mp pullback.condition)

@[expose] def inverse : Original c ⟶ rationalFiber c :=
  (originalCover c).glueMorphisms (inverseLocal c) (inverse_compatibility c)

@[reassoc] theorem inverse_restriction (i : Bool) :
    (originalCover c).f i ≫ inverse c = inverseLocal c i :=
  (originalCover c).ι_glueMorphisms _ _ i

/-- The actual global rational base change is isomorphic to the original
model. Both inverse identities are checked on whole proved covers; no
arithmetic special-fiber regularity is asserted. -/
@[expose] def iso : rationalFiber c ≅ Original c where
  hom := OriginalIntegerRationalGlobalComparison318.comparison c
  inv := inverse c
  hom_inv_id := by
    apply (rationalCover c).hom_ext
    intro i
    rw [← Category.assoc, OriginalIntegerRationalGlobalComparison318.restriction]
    cases i <;>
      simp only [OriginalIntegerRationalGlobalComparison318.localMap,
        Category.assoc, inverse_restriction, inverseLocal,
        Iso.hom_inv_id_assoc, Category.comp_id]
  inv_hom_id := by
    apply (originalCover c).hom_ext
    intro i
    rw [← Category.assoc, inverse_restriction]
    cases i <;>
      simp only [inverseLocal, Category.assoc,
        OriginalIntegerRationalGlobalComparison318.restriction,
        OriginalIntegerRationalGlobalComparison318.localMap,
        Iso.inv_hom_id_assoc, Category.comp_id]

end OriginalIntegerRationalGlobalIsomorphism318
