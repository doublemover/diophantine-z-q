module
public import ReconstructedFieldNormalization318
public section
noncomputable section
namespace OriginalCandidateCurveIso318
open Polynomial AlgebraicGeometry CategoryTheory
variable {L : Type} [Field L] [Algebra (RatFunc ℚ) L]
  {Y : Scheme} [IsIntegral Y]
  (g : Spec (CommRingCat.of L) ⟶ Y) (p : Y ⟶ ProjectiveJLine318.scheme ℚ)
  [IsDominant g] [IsIntegralHom p] [IsIso (DominantFunctionField318.map g)]
  (hbase : g ≫ p = ReconstructedFieldNormalization318.base L)
  {ι : Type*} (V : ι → Y.affineOpens) (hcover : ⨆ i, (V i).1 = ⊤)
  (hnormal : ∀ i, IsIntegrallyClosed Γ(Y, (V i).1))

lemma composite_quasiCompact : QuasiCompact (g ≫ p) := by
  rw [hbase]
  infer_instance
lemma composite_quasiSeparated : QuasiSeparated (g ≫ p) := by
  rw [hbase]
  infer_instance

variable (c : Fin 4 → ℚˣ)
local instance actualField : Field (ContactFieldNormalization318.Field c) :=
  (KummerTensorField318.source_raw_field c).toField
variable (e : ContactFieldNormalization318.Field c ≃ₐ[RatFunc ℚ] L)

/-- Comparison with an ORIGINAL supplied curve, not merely with a replacement
normalization. The curve must have its real integral map, normal affine cover
and birational generic embedding of the SAME L over the SAME projective t-line. -/
@[expose] def iso : Y ≅ ContactProjectiveModel318.model c := by
  letI := composite_quasiCompact g p hbase
  letI := composite_quasiSeparated g p hbase
  exact (NormalizationBirationalComparison318.iso g p V hcover hnormal).symm ≪≫
    NormalizationSourceIso318.iso (g ≫ p) (ContactFieldNormalization318.genericBase c)
      (ReconstructedFieldNormalization318.specIso L c e)
      ((ReconstructedFieldNormalization318.base_square L c e).trans hbase.symm) ≪≫
        ContactFieldNormalization318.iso c

/-- The actual generic restriction is precisely the originally reconstructed
field map, with its correct contravariant direction. -/
@[reassoc] theorem iso_source : g ≫ (iso g p hbase V hcover hnormal c e).hom =
    (ReconstructedFieldNormalization318.specIso L c e).hom ≫
      ContactFieldNormalization318.genericSource c := by
  letI := composite_quasiCompact g p hbase
  letI := composite_quasiSeparated g p hbase
  have hg : g ≫ (NormalizationBirationalComparison318.iso g p V hcover hnormal).inv =
      (g ≫ p).toNormalization := by
    have he := congrArg (fun k => k ≫
      (NormalizationBirationalComparison318.iso g p V hcover hnormal).inv)
      (NormalizationBirationalComparison318.iso_source g p V hcover hnormal)
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using he.symm
  simp only [iso, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, hg, NormalizationSourceIso318.iso_source_assoc,
    ContactFieldNormalization318.iso_source]

@[reassoc] theorem iso_base : (iso g p hbase V hcover hnormal c e).hom ≫
    ContactProjectiveModel318.modelMap c = p := by
  letI := composite_quasiCompact g p hbase
  letI := composite_quasiSeparated g p hbase
  have hp : (NormalizationBirationalComparison318.iso g p V hcover hnormal).inv ≫
      (g ≫ p).fromNormalization = p := by
    have he := congrArg (fun k =>
      (NormalizationBirationalComparison318.iso g p V hcover hnormal).inv ≫ k)
      (NormalizationBirationalComparison318.iso_base g p V hcover hnormal)
    simpa only [←Category.assoc, Iso.inv_hom_id, Category.id_comp] using he.symm
  simp only [iso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    ContactFieldNormalization318.iso_base, NormalizationSourceIso318.iso_base]
  exact hp

variable [FiniteDimensional (RatFunc ℚ) L] [IsGalois (RatFunc ℚ) L]
include hbase hcover hnormal in
/-- The curve isomorphism is constructed, not supplied. Genuine PEL geometry
must still construct Y,p,g, its normal cover, and the local inertia models. -/
theorem exists_original_curve_iso
    (labels : (L ≃ₐ[RatFunc ℚ] L) ≃* FourBinaryCharacters318.Group)
    (models : ∀ (q : ℚ[X]) (hq : Prime q),
      OriginalTangentFieldReconstruction318.LocalModel labels q hq) :
    ∃ c : Fin 4 → ℚˣ,
      ∃ e : ContactFieldNormalization318.Field c ≃ₐ[RatFunc ℚ] L,
        ∃ E : Y ≅ ContactProjectiveModel318.model c,
          E.hom ≫ ContactProjectiveModel318.modelMap c = p ∧
          g ≫ E.hom = (ReconstructedFieldNormalization318.specIso L c e).hom ≫
            ContactFieldNormalization318.genericSource c ∧
          ∀ (σ : L ≃ₐ[RatFunc ℚ] L) z, σ (e z) = e
            (FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c)
              (FourBinaryCharacters318.signPattern (labels σ)) z) := by
  obtain ⟨c, e, he⟩ := OriginalTangentFieldReconstruction318.reconstruct labels models
  exact ⟨c, e, iso g p hbase V hcover hnormal c e,
    iso_base g p hbase V hcover hnormal c e, iso_source g p hbase V hcover hnormal c e, he⟩
end OriginalCandidateCurveIso318
