module
public import ProjectiveLineOOne318
public import PullbackLineFrames318
public import ContactBicanonicalProjectiveMap318
public section
noncomputable section
namespace ContactProjectiveLinePullback318
open AlgebraicGeometry CategoryTheory Polynomial
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ)

/-- The actual inverse-image O-module of the separately constructed target O(1). -/
@[expose] def line : (ContactGlobalSmooth318.Model c).Modules :=
  (Scheme.Modules.pullback (ContactBicanonicalProjectiveMap318.projectiveMap c)).obj
    ProjectiveLineOOne318.line

@[expose] def branchFrame (i : Fin 4) :
    (line c).restrict (ContactIntrinsicFrames318.branchEmbedding c i) ≅
      SheafOfModules.unit (Spec (CommRingCat.of (ContactIntrinsicFrames318.BranchRing c i))).ringCatSheaf :=
  PullbackLineFrames318.frame (ContactBicanonicalProjectiveMap318.projectiveMap c)
    (JLineAtlas318.chart ℚ 1) (ContactIntrinsicFrames318.branchEmbedding c i)
    (Spec.map (CommRingCat.ofHom (Polynomial.aeval (ContactBicanonicalRatios318.branchRatio c i)).toRingHom))
    (by rw [ContactBicanonicalProjectiveMap318.projectiveMap_eq]
        exact ContactBicanonicalProjectiveMap318.branch_comparison c i)
    ProjectiveLineOOne318.line ProjectiveLineOOne318.finiteFrame

@[expose] def infinityFrame :
    (line c).restrict (InfinityGlobalScheme318.chartEmbedding c) ≅
      SheafOfModules.unit (ReciprocalInfinityNormalization318.neighborhood c).ringCatSheaf :=
  PullbackLineFrames318.frame (ContactBicanonicalProjectiveMap318.projectiveMap c)
    (JLineAtlas318.chart ℚ 0) (InfinityGlobalScheme318.chartEmbedding c)
    (Spec.map (CommRingCat.ofHom (Polynomial.aeval (ContactBicanonicalRatios318.infinityRatio c)).toRingHom))
    (by rw [ContactBicanonicalProjectiveMap318.projectiveMap_eq]
        exact ContactBicanonicalProjectiveMap318.infinity_comparison c)
    ProjectiveLineOOne318.line ProjectiveLineOOne318.infinityFrame
end ContactProjectiveLinePullback318
