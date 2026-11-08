module
public import ContactFiniteOverlapDifferential318
public import InfinityDenominatorOverlap318
public import ReciprocalBicanonicalIdentity318
public import ReciprocalCoordinateDifferential318
public section
noncomputable section
namespace ContactInfinityOverlapDifferential318
open Polynomial ContactOverlapAlgebraMaps318 ContactBicanonicalCoefficients318
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ)
abbrev O := ContactKummerOrder318.OpenOrder c
@[expose] def C0 : O c := algebraMap ℚ (O c) (∏j:Fin 3,(c j.succ:ℚ))
@[expose] def c0 : O c := algebraMap ℚ (O c) (c 0:ℚ)
@[expose] def k0 : O c := algebraMap ℚ (O c) (↑(c 0)⁻¹:ℚ)
@[expose] def inverseDenominator : O c := infinityMap c (infinityDenominatorInverse c)
@[expose] def inverseU : O c := ↑((SourceInfinityOverlap318.u_unit c).unit⁻¹)
@[expose] def factor : O c := -(2*inverseU c*SourceInfinityOverlap318.t c)

lemma c0_k0 : c0 c*k0 c=1 := by
  change algebraMap ℚ (O c) (c 0:ℚ)*algebraMap ℚ (O c) (↑(c 0)⁻¹:ℚ)=1
  rw [←map_mul,Units.mul_inv,map_one]

lemma u_inverseU : SourceInfinityOverlap318.u c*inverseU c=1 := by
  exact (congrArg (fun v : O c => v*inverseU c)
    (SourceInfinityOverlap318.u_unit c).unit_spec).symm.trans (Units.mul_inv _)

lemma denominator_inverse : InfinityDenominatorOverlap318.denominator c*inverseDenominator c=1 := by
  have hi : algebraMap ℚ[X] (Infinity c) (InfinityOpenChart318.denominator c) *
      algebraMap (InfinityOpenChart318.OpenBase c) (Infinity c)
        (IsLocalization.Away.invSelf (InfinityOpenChart318.denominator c))=1 := by
    rw [IsScalarTower.algebraMap_apply ℚ[X] (InfinityOpenChart318.OpenBase c) (Infinity c),
      ←map_mul,IsLocalization.Away.mul_invSelf,map_one]
  change infinityMap c _ * infinityMap c _ = 1
  rw [←map_mul]
  exact (congrArg (infinityMap c) hi).trans (map_one (infinityMap c))

lemma q0_image : infinityMap c (infinityQ0 c)=
    4*C0 c*(k0 c)^5*(SourceInfinityOverlap318.u c)^2*inverseDenominator c := by
  simp only [infinityQ0,map_mul,map_pow,AlgHom.commutes,infinityMap_coordinate,
    infinityScale,fourUnit,infinityTwist,Units.val_mul,Units.val_pow_eq_pow_val,Units.coe_prod,Units.val_mk0,
    map_mul,map_pow,map_ofNat,C0,k0,inverseDenominator]

lemma q1_image : infinityMap c (infinityQ1 c)=4*C0 c*(k0 c)^4*inverseDenominator c := by
  simp only [infinityQ1,map_mul,AlgHom.commutes,infinityScale,fourUnit,infinityTwist,
    Units.val_mul,Units.val_pow_eq_pow_val,Units.coe_prod,Units.val_mk0,map_mul,map_pow,map_ofNat,C0,k0,inverseDenominator]

/-- The actual infinity coefficient satisfies the same cleared derivative
square on the entire common ring, using the specified reciprocal convention. -/
theorem coefficient_cleared :
    ContactFiniteOverlapDifferential318.P c * infinityMap c (infinityQ0 c)=(factor c)^2 := by
  have h1 := ReciprocalBicanonicalIdentity318.cleared (c0 c) (k0 c) (C0 c)
    (SourceInfinityOverlap318.u c) (ContactFiniteOverlapDifferential318.P c)
    (InfinityDenominatorOverlap318.denominator c) (inverseDenominator c)
    (c0_k0 c) (denominator_inverse c) (InfinityDenominatorOverlap318.denominator_identity c)
  have h2 := ReciprocalBicanonicalIdentity318.factor_cleared
    (SourceInfinityOverlap318.u c) (inverseU c) (SourceInfinityOverlap318.t c) (c0 c)
    (u_inverseU c) (SourceInfinityOverlap318.coordinate_relation c)
  rw [q0_image]
  exact ((SourceInfinityOverlap318.u_unit c).pow 6).mul_left_cancel (h1.trans h2.symm)

theorem differential_relation :
    KaehlerDifferential.D ℚ (O c) (SourceInfinityOverlap318.t c)=
      factor c • KaehlerDifferential.D ℚ (O c) (SourceInfinityOverlap318.u c) :=
  ReciprocalCoordinateDifferential318.D_of_inverse _ _ _ (c 0:ℚ)
    (u_inverseU c) (SourceInfinityOverlap318.coordinate_relation c)

theorem q1_relation :
    SourceInfinityOverlap318.t c*infinityMap c (infinityQ0 c)=infinityMap c (infinityQ1 c) := by
  rw [q0_image,q1_image]
  exact ReciprocalBicanonicalIdentity318.q1_relation _ _ _ _ _ _
    (c0_k0 c) (SourceInfinityOverlap318.coordinate_relation c)
end ContactInfinityOverlapDifferential318
