module
public import OriginalAllPrimeDualSectionComparison318
public import NormalizedWholeBicanonicalSheaf318
public section
noncomputable section
namespace OriginalWholeDualityModel318
open AlgebraicGeometry CategoryTheory NumberField
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318
set_option maxHeartbeats 1800000
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t)) (D : Data c t w)
local notation "V" => OriginalPointFinitePlaceRoots318.V c t w
local notation "a" => IntegralSourceBranches318.contacts V

/-- Actual global rank-one model module, with produced finite-dual local
identifications and the proved whole-overlap differential transition. -/
@[expose] def canonicalCandidate : D.model.Modules :=
  NormalizedWholeDualitySheaf318.line V D.coefficients a
@[expose] def bicanonicalCandidate : D.model.Modules :=
  NormalizedWholeBicanonicalSheaf318.line V D.coefficients a

theorem canonical_locallyFree : (canonicalCandidate c t w D).IsLocallyFree :=
  NormalizedWholeDualitySheaf318.locallyFree V D.coefficients a
theorem bicanonical_locallyFree : (bicanonicalCandidate c t w D).IsLocallyFree :=
  NormalizedWholeBicanonicalSheaf318.locallyFree V D.coefficients a

@[expose] def section0 : Γ(bicanonicalCandidate c t w D,⊤) :=
  NormalizedWholeBicanonicalSheaf318.section0 V D.coefficients a
@[expose] def section1 : Γ(bicanonicalCandidate c t w D,⊤) :=
  NormalizedWholeBicanonicalSheaf318.section1 V D.coefficients a

/-- The SAME previously constructed proper model and its original
valuative section now carry actual global module sheaves and actual
global sections. No regularity, normalization, dualizing-sheaf identity,
intrinsic tensor-square identity or KS/Hodge statement is inferred. -/
theorem exists_model : ∃ (D : Data c t w) (g : Spec (CommRingCat.of V) ⟶ D.model),
    g ≫ D.structureMap=𝟙 _ ∧
    Spec.map (CommRingCat.ofHom (algebraMap V (K c t))) ≫ g=D.genericPoint ∧
    IsProper D.structureMap ∧ IsSeparated D.structureMap ∧
    (canonicalCandidate c t w D).IsLocallyFree ∧
    (bicanonicalCandidate c t w D).IsLocallyFree := by
  obtain ⟨D,g,hbase,hgeneric⟩ := OriginalAllPlaceNormalizedData318.exists_center c t w
  exact ⟨D,g,hbase,hgeneric,D.proper_separated.1,D.proper_separated.2,
    canonical_locallyFree c t w D,bicanonical_locallyFree c t w D⟩

/-- The local integral tensors underlying these specified global
coefficients have genuine balanced differential images equal to the
original branch q0 and q1, at every place and in either coordinate mode. -/
theorem original_section_images {m : OriginalAllPrimeZoomInput318.Mode}
    (I : OriginalAllPrimeZoomInput318.Input c t w D m) :
    (OriginalAllPrimeDualSectionComparison318.modelRealization c t w D I
      (OriginalAllPrimeDualSectionComparison318.modelSection0 c t w D (m:=m))=
      OriginalAllPrimeIntegralBicanonical318.genericSection0 c t w D I) ∧
    (OriginalAllPrimeDualSectionComparison318.modelRealization c t w D I
      (OriginalAllPrimeDualSectionComparison318.modelSection1 c t w D (m:=m))=
      OriginalAllPrimeIntegralBicanonical318.genericSection1 c t w D I) :=
  ⟨OriginalAllPrimeDualSectionComparison318.section0_image c t w D I,
    OriginalAllPrimeDualSectionComparison318.section1_image c t w D I⟩
end OriginalWholeDualityModel318
