module
public import ContactFiniteCoefficientIdentity318
public import ContactOverlapAlgebraMaps318
public section
noncomputable section
namespace ContactFiniteOverlapDifferential318
open Polynomial ContactOverlapAlgebraMaps318
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ)
abbrev O := ContactKummerOrder318.OpenOrder c

@[expose] def P : O c := SourceOpenFractionField318.orderToOpen c (SourceOpenFractionField318.d c)
@[expose] def z (i : Fin 4) : O c := branchMap c i (ContactFrameNormalization318.sourceCoordinate c i)
@[expose] def factor (i : Fin 4) : O c := 2*algebraMap ℚ (O c) (↑(c i)⁻¹:ℚ)*z c i

lemma P_image (i : Fin 4) :
    branchMap c i (ContactFiniteCoefficientIdentity318.branchP c i)=P c :=
  BranchOverlapLocalization318.toOpen_on_source c i _

theorem P_unit : IsUnit (P c) := by
  letI : Algebra (ContactKummerOrder318.SourceOrder c) (O c) :=
    (SourceOpenFractionField318.orderToOpen c).toAlgebra
  letI := SourceOpenFractionField318.open_isLocalization c
  exact IsLocalization.Away.algebraMap_isUnit (S:=O c) (SourceOpenFractionField318.d c)

/-- The finite bicanonical coefficient identity now holds in the same
entire actual unbranched overlap for every branch. -/
theorem coefficient_cleared (i : Fin 4) :
    P c * branchMap c i (ContactBicanonicalCoefficients318.branchQ0 c i)=(factor c i)^2 := by
  have h := congrArg (branchMap c i) (ContactFiniteCoefficientIdentity318.finite_cleared c i)
  simpa only [map_mul,map_pow,map_ofNat,AlgHom.commutes,P_image,factor,z] using h

/-- Universal differential identity after the actual Q-algebra restriction,
not an equality inferred merely from matching generic points. -/
theorem differential_relation (i : Fin 4) :
    KaehlerDifferential.D ℚ (O c) (SourceInfinityOverlap318.t c)=
      factor c i • KaehlerDifferential.D ℚ (O c) (z c i) := by
  have h := congrArg (AlgHomDifferential318.map (branchMap c i))
    (ContactBranchDifferential318.D_branchT c i)
  simpa only [AlgHomDifferential318.map_D,AlgHomDifferential318.map_smul,
    branchMap_coordinate,map_mul,map_ofNat,AlgHom.commutes,factor,z] using h
end ContactFiniteOverlapDifferential318
