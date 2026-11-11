module
public import FourRootActualBranchKaehler318
public import FourRootInfinityAffineComparison318
public import Mathlib.RingTheory.Localization.Basic
public section
noncomputable section
namespace FourRootActualInfinityKaehler318
open FourRootReciprocalBranchData318
open FourRootActualBranchKaehler318
variable (b:Fin 4→ℂ) (hb:Function.Injective b)
abbrev I:=FourRootInfinityCoordinateRing318.Ring b
@[expose] def denominator:I b:=
  (FourRootInfinityAffineComparison318.equivalence b hb).symm
    (FourRootActualFiniteBranchChart318.denominator (branches b) 0)
abbrev SourceRing:=Localization.Away (denominator b hb)
lemma powers_map:
    (Submonoid.powers (denominator b hb)).map
      (FourRootInfinityAffineComparison318.equivalence b hb).toMonoidHom=
        Submonoid.powers (FourRootActualFiniteBranchChart318.denominator (branches b) 0):=by
  rw [Submonoid.map_powers,denominator,AlgEquiv.apply_symm_apply]
/-- The entire infinity principal neighborhood is identified with the
actual branch-zero localization over reciprocal parameter v=u². -/
@[expose] def localizationEquiv:SourceRing b hb≃ₐ[ℂ]
    FourRootActualBranchKaehler318.SourceRing (branches b) 0:=
  IsLocalization.algEquivOfAlgEquiv (SourceRing b hb)
    (FourRootActualBranchKaehler318.SourceRing (branches b) 0)
    (FourRootInfinityAffineComparison318.equivalence b hb) (powers_map b hb)
lemma on_source(x:I b):localizationEquiv b hb (algebraMap (I b) (SourceRing b hb) x)=
    algebraMap (FourRootActualFractionField318.A (branches b))
      (FourRootActualBranchKaehler318.SourceRing (branches b) 0)
      (FourRootInfinityAffineComparison318.equivalence b hb x):=
  IsLocalization.algEquivOfAlgEquiv_eq (powers_map b hb) x
@[expose] def coordinate:SourceRing b hb:=
  algebraMap (I b) (SourceRing b hb) (FourRootInfinityCoordinateRing318.coordinate b none)
lemma coordinate_image:localizationEquiv b hb (coordinate b hb)=
    sourceCoordinate (branches b) 0:=by
  rw [coordinate,on_source,source_coordinate_original]
  rfl
@[expose] def frame:KaehlerDifferential ℂ (SourceRing b hb)≃ₗ[SourceRing b hb]SourceRing b hb:=
  EtaleDifferentialFrame318.ofAlgEquiv (localizationEquiv b hb).symm
    (sourceFrame (branches b) 0)
lemma coordinate_normalized:frame b hb (KaehlerDifferential.D ℂ _ (coordinate b hb))=1:=by
  have h:coordinate b hb=(localizationEquiv b hb).symm (sourceCoordinate (branches b) 0):=
    (localizationEquiv b hb).injective (by rw [coordinate_image,AlgEquiv.apply_symm_apply])
  rw [h,frame,ActualEtaleFrameNormalization318.ofAlgEquiv_D_image,source_normalized,map_one]
/-- Literal reciprocal projective parameter, not u treated as the base. -/
@[expose] def reciprocalParameter:SourceRing b hb:=
  algebraMap (I b) (SourceRing b hb) (FourRootInfinityCoordinateRing318.coordinate b none^2)
lemma exact_square:reciprocalParameter b hb=coordinate b hb^2:=map_pow _ _ _
theorem reciprocal_differential:
    KaehlerDifferential.D ℂ (SourceRing b hb) (reciprocalParameter b hb)=
      (2*coordinate b hb) • KaehlerDifferential.D ℂ _ (coordinate b hb):=by
  simpa only [map_one,mul_one,map_zero,sub_zero,one_mul] using
    SquareCoordinateDifferential318.D_of_square (reciprocalParameter b hb) (coordinate b hb)
      (0:ℂ) (1:ℂ) (by simpa only [map_zero,sub_zero,map_one,one_mul] using exact_square b hb)
theorem reciprocal_coefficient:
    frame b hb (KaehlerDifferential.D ℂ _ (reciprocalParameter b hb))=2*coordinate b hb:=by
  rw [reciprocal_differential,map_smul,coordinate_normalized,smul_eq_mul,mul_one]
end FourRootActualInfinityKaehler318
