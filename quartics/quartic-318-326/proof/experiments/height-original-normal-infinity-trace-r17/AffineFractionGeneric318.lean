module
public import AffineFunctionFieldMap318
public section
noncomputable section
namespace AffineFractionGeneric318
open AlgebraicGeometry CategoryTheory
universe u
variable (R K : Type u) [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

@[expose] def map : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R K))

instance dominant : IsDominant (map R K) := by
  constructor
  change DenseRange (PrimeSpectrum.comap (algebraMap R K))
  apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
  rw [(RingHom.injective_iff_ker_eq_bot (algebraMap R K)).mp (IsFractionRing.injective R K)]
  exact bot_le

local instance spec_dominant : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
  dominant R K

local instance : Algebra R (Spec (CommRingCat.of R)).functionField :=
  AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (CommRingCat.of R)
local instance : IsFractionRing R (Spec (CommRingCat.of R)).functionField :=
  AlgebraicGeometry.functionField_isFractionRing_of_affine (CommRingCat.of R)
local instance : Algebra K (Spec (CommRingCat.of K)).functionField :=
  AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (CommRingCat.of K)
local instance : IsFractionRing K (Spec (CommRingCat.of K)).functionField :=
  AlgebraicGeometry.functionField_isFractionRing_of_affine (CommRingCat.of K)

/-- The literal generic-stalk map of the original fraction-field inclusion
is bijective. Surjectivity is proved using actual fractions twice, retaining
both original affine coefficient embeddings. -/
theorem generic_isIso : IsIso (DominantFunctionField318.map (map R K)) := by
  let q := DominantFunctionField318.map (map R K)
  have hcoeff (r : R) :
      q (algebraMap R (Spec (CommRingCat.of R)).functionField r) =
        algebraMap K (Spec (CommRingCat.of K)).functionField (algebraMap R K r) :=
    AffineFunctionFieldMap318.on_coefficient (algebraMap R K) r
  dsimp only [q] at hcoeff
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  refine ⟨q.hom.injective, ?_⟩
  intro z
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective K z
  obtain ⟨an, ad, _, ha⟩ := IsFractionRing.div_surjective R a
  obtain ⟨bn, bd, _, hb⟩ := IsFractionRing.div_surjective R b
  let r := algebraMap R (Spec (CommRingCat.of R)).functionField
  refine ⟨(r an / r ad) / (r bn / r bd), ?_⟩
  calc
    _ = algebraMap K (Spec (CommRingCat.of K)).functionField
        ((algebraMap R K an / algebraMap R K ad) /
          (algebraMap R K bn / algebraMap R K bd)) := by
      simp only [map_div₀, r, hcoeff]
    _ = _ := by rw [ha, hb, map_div₀]
end AffineFractionGeneric318
