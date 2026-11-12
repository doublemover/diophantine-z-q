module
public import RationalContactPoint318
public import ContactIntrinsicFrames318
public section
noncomputable section
namespace ContactBranchPoint318
open AlgebraicGeometry CategoryTheory ContactKummerOrder318 Polynomial
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
variable (c : Fin 4 → ℚˣ) (t : ℚ)
    (hn : ∀ i, RationalContactPoint318.parameters c t i ≠ 0)

local instance pointBase : Algebra R (RationalContactPoint318.PointField c t) :=
  ((algebraMap ℚ (RationalContactPoint318.PointField c t)).comp (Polynomial.aeval t).toRingHom).toAlgebra
local instance pointSMul : SMul R (RationalContactPoint318.PointField c t) := (pointBase c t).toSMul
local instance pointModule : Module R (RationalContactPoint318.PointField c t) := Algebra.toModule

include hn in
/-- The literal three-other-root denominator is nonzero at the original
source-order point. No new field or substitute tuple is chosen. -/
theorem denominator_ne (i : Fin 4) :
    RationalContactPoint318.sourcePoint c t (SourceDenominatorCover318.denominator c i) ≠ 0 := by
  change RationalContactPoint318.sourcePoint c t
    (algebraMap R (SourceOrder c) (SourceDenominatorCover318.twisted c i)) ≠ 0
  rw [(RationalContactPoint318.sourcePoint c t).commutes]
  change algebraMap ℚ (RationalContactPoint318.PointField c t)
    (Polynomial.aeval t (SourceDenominatorCover318.twisted c i)) ≠ 0
  have hprod : Polynomial.aeval t (SourceDenominatorCover318.twisted c i) ≠ 0 := by
    simpa only [SourceDenominatorCover318.twisted, map_prod,
      RationalContactPoint318.parameters] using
      (Finset.prod_ne_zero_iff.mpr (fun j _ => hn (FourRootPivot318.indices i j.succ)))
  simpa only [map_zero] using
    (algebraMap ℚ (RationalContactPoint318.PointField c t)).injective.ne hprod

/-- The original point factors through every actual finite branch chart
when all four specialized coefficients are nonzero. -/
@[expose] def branchPoint (i : Fin 4) :
    ContactIntrinsicFrames318.BranchRing c i →+* RationalContactPoint318.PointField c t :=
  IsLocalization.Away.lift (SourceDenominatorCover318.denominator c i)
    (isUnit_iff_ne_zero.mpr (denominator_ne c t hn i))

theorem branchPoint_algebraMap (i : Fin 4) (a : SourceOrder c) :
    branchPoint c t hn i (algebraMap (SourceOrder c) (ContactIntrinsicFrames318.BranchRing c i) a) =
      RationalContactPoint318.sourcePoint c t a :=
  IsLocalization.Away.lift_eq _ _ _

theorem branchPoint_polynomial (i : Fin 4) (f : ℚ[X]) :
    branchPoint c t hn i
      (algebraMap (SourceOrder c) (ContactIntrinsicFrames318.BranchRing c i)
        (algebraMap ℚ[X] (SourceOrder c) f)) =
      algebraMap ℚ (RationalContactPoint318.PointField c t) (Polynomial.aeval t f) := by
  rw [branchPoint_algebraMap]
  exact (RationalContactPoint318.sourcePoint c t).commutes f

@[expose] def branchMap (i : Fin 4) :
    Spec (CommRingCat.of (RationalContactPoint318.PointField c t)) ⟶
      Spec (CommRingCat.of (ContactIntrinsicFrames318.BranchRing c i)) :=
  Spec.map (CommRingCat.ofHom (branchPoint c t hn i))

/-- Equality as morphisms into the original complete source, including
its actual branch embedding rather than only equality of coordinates. -/
theorem branchMap_original (i : Fin 4) :
    branchMap c t hn i ≫ ContactIntrinsicFrames318.branchEmbedding c i =
      RationalContactPoint318.point c t := by
  unfold branchMap ContactIntrinsicFrames318.branchEmbedding RationalContactPoint318.point
  rw [← Category.assoc, ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact branchPoint_algebraMap c t hn i a

end ContactBranchPoint318
