module
public import FlatJChart318
public section
noncomputable section
namespace ArithmeticJModel318
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ) (B:Type) [CommRing B] [IsDomain B]
  [Algebra (OpenJModel318.Base N) B] [Module.Finite (OpenJModel318.Base N) B]
  [Algebra.Etale (OpenJModel318.Base N) B]

@[expose] def structureMap :
    (OpenJProjectiveMap318.coverMap N B).normalization ⟶ Spec (CommRingCat.of ℤ) :=
  (OpenJProjectiveMap318.coverMap N B).fromNormalization≫ProjectiveJLine318.structureMap ℤ

/-- The actual source meets the generic characteristic-zero fiber. -/
theorem model_dominant (hN:N≠0) : IsDominant (structureMap N B) := by
  letI:=FlatJChart318.cover_charZero N B hN
  have hd:IsDominant (Spec.map (CommRingCat.ofHom (algebraMap ℤ B))) := by
    constructor
    change DenseRange (PrimeSpectrum.comap (algebraMap ℤ B))
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
    rw [(RingHom.injective_iff_ker_eq_bot (algebraMap ℤ B)).mp (FaithfulSMul.algebraMap_injective ℤ B)]
    exact bot_le
  have he:(OpenJProjectiveMap318.coverMap N B).toNormalization≫structureMap N B=
      Spec.map (CommRingCat.ofHom (algebraMap ℤ B)):=
    ProperOpenJNormalization318.normalization_over_Z N B
  letI:IsDominant ((OpenJProjectiveMap318.coverMap N B).toNormalization≫structureMap N B):=by
    rw [he];exact hd
  exact IsDominant.of_comp (f:=(OpenJProjectiveMap318.coverMap N B).toNormalization) (structureMap N B)

/-- Properness makes that actual dense image all of Spec Z. -/
theorem model_surjective (hN:N≠0) : Surjective (structureMap N B) := by
  letI:IsProper (structureMap N B):=(ProperOpenJNormalization318.proper_integral_extension N B hN).2.2
  letI:=model_dominant N B hN
  infer_instance

/-- A genuine proper, flat and surjective model over Z. All three are derived
for the same constructed scheme and the same structure morphism. -/
theorem proper_flat_surjective (hN:N≠0) :
    IsProper (structureMap N B) ∧ Flat (structureMap N B) ∧ Surjective (structureMap N B) :=
  ⟨(ProperOpenJNormalization318.proper_integral_extension N B hN).2.2,
    FlatJChart318.model_flat N B hN,model_surjective N B hN⟩

theorem finite_presentation (hN:N≠0) : LocallyOfFinitePresentation (structureMap N B) := by
  letI:IsProper (structureMap N B):=(proper_flat_surjective N B hN).1
  infer_instance

end ArithmeticJModel318
