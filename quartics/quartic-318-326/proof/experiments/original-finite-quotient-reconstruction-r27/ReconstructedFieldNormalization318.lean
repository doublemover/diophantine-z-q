module
public import ContactFieldNormalization318
public import OriginalTangentFieldReconstruction318
public section
noncomputable section
namespace ReconstructedFieldNormalization318
open Polynomial AlgebraicGeometry CategoryTheory
variable (L : Type) [Field L] [Algebra (RatFunc ℚ) L]

/-- The actual generic morphism to the ORIGINAL projective t-line. -/
@[expose] def base : Spec (CommRingCat.of L) ⟶ ProjectiveJLine318.scheme ℚ :=
  Spec.map (CommRingCat.ofHom
    ((algebraMap (RatFunc ℚ) L).comp (algebraMap ℚ[X] (RatFunc ℚ)))) ≫
      JLineAtlas318.chart ℚ 1

instance base_quasiCompact : QuasiCompact (base L) := by
  exact ⟨fun _ _ _ => (Set.toFinite _).isCompact⟩
instance base_quasiSeparated : QuasiSeparated (base L) := by
  unfold base
  infer_instance

variable (c : Fin 4 → ℚˣ)
local instance actualField : Field (ContactFieldNormalization318.Field c) :=
  (KummerTensorField318.source_raw_field c).toField
variable (e : ContactFieldNormalization318.Field c ≃ₐ[RatFunc ℚ] L)

/-- Contravariance fixes the direction: the given old-field-to-L map induces
Spec L to the original field spectrum. -/
@[expose] def specIso : Spec (CommRingCat.of L) ≅
    Spec (CommRingCat.of (ContactFieldNormalization318.Field c)) :=
  Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op

@[reassoc] theorem base_square : (specIso L c e).hom ≫ ContactFieldNormalization318.genericBase c =
    base L := by
  change Spec.map (CommRingCat.ofHom e.toRingHom) ≫ ContactFieldNormalization318.genericBase c = _
  rw [ContactFieldNormalization318.genericBase_polynomial, ← Category.assoc, ← Spec.map_comp]
  unfold base
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact e.commutes (algebraMap ℚ[X] (RatFunc ℚ) a)

/-- Actual globally glued relative normalization of the supplied original
field, identified with the existing Contact model by the SAME field map. -/
@[expose] def iso : (base L).normalization ≅ ContactProjectiveModel318.model c :=
  NormalizationSourceIso318.iso (base L) (ContactFieldNormalization318.genericBase c)
    (specIso L c e) (base_square L c e) ≪≫ ContactFieldNormalization318.iso c

@[reassoc] theorem iso_source : (base L).toNormalization ≫ (iso L c e).hom =
    (specIso L c e).hom ≫ ContactFieldNormalization318.genericSource c := by
  simp only [iso, Iso.trans_hom, NormalizationSourceIso318.iso_source_assoc,
    ContactFieldNormalization318.iso_source]

@[reassoc] theorem iso_base : (iso L c e).hom ≫ ContactProjectiveModel318.modelMap c =
    (base L).fromNormalization := by
  simp only [iso, Iso.trans_hom, Category.assoc, ContactFieldNormalization318.iso_base,
    NormalizationSourceIso318.iso_base]

variable [FiniteDimensional (RatFunc ℚ) L] [IsGalois (RatFunc ℚ) L]
/-- This is a constructed normalization scheme, not yet an identification
with an independently constructed PEL curve. The old field map is retained
in the exact generic-source square. -/
theorem exists_normalization_iso
    (labels : (L ≃ₐ[RatFunc ℚ] L) ≃* FourBinaryCharacters318.Group)
    (models : ∀ (q : ℚ[X]) (hq : Prime q),
      OriginalTangentFieldReconstruction318.LocalModel labels q hq) :
    ∃ c : Fin 4 → ℚˣ,
      ∃ e : ContactFieldNormalization318.Field c ≃ₐ[RatFunc ℚ] L,
        ∃ E : (base L).normalization ≅ ContactProjectiveModel318.model c,
          (base L).toNormalization ≫ E.hom =
            (specIso L c e).hom ≫ ContactFieldNormalization318.genericSource c ∧
          ∀ (σ : L ≃ₐ[RatFunc ℚ] L) z, σ (e z) = e
            (FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c)
              (FourBinaryCharacters318.signPattern (labels σ)) z) := by
  obtain ⟨c, e, he⟩ := OriginalTangentFieldReconstruction318.reconstruct labels models
  exact ⟨c, e, iso L c e, iso_source L c e, he⟩
end ReconstructedFieldNormalization318
