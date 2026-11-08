module
public import ContactDerivativeFrameComparison318
public section
noncomputable section
namespace ContactBicanonicalSectionNormalization318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ)

@[expose] def coefficient0 : (i : Option (Fin 4)) → Γ(ContactIntrinsicFrames318.chart c i,⊤)
  | some i => (Scheme.ΓSpecIso (CommRingCat.of (ContactIntrinsicFrames318.BranchRing c i))).inv
      (ContactBicanonicalCoefficients318.branchQ0 c i)
  | none => (Scheme.ΓSpecIso (CommRingCat.of (InfinityGlobalChart318.InfinityOrder c))).inv
      (ContactBicanonicalCoefficients318.infinityQ0 c)
@[expose] def coefficient1 : (i : Option (Fin 4)) → Γ(ContactIntrinsicFrames318.chart c i,⊤)
  | some i => (Scheme.ΓSpecIso (CommRingCat.of (ContactIntrinsicFrames318.BranchRing c i))).inv
      (ContactBicanonicalCoefficients318.branchQ1 c i)
  | none => (Scheme.ΓSpecIso (CommRingCat.of (InfinityGlobalChart318.InfinityOrder c))).inv
      (ContactBicanonicalCoefficients318.infinityQ1 c)

theorem frame_inverse (i : Option (Fin 4)) (a : Γ(ContactIntrinsicFrames318.chart c i,⊤)) :
    (ContactBicanonicalSheaf318.localFrame c i).inv.app ⊤ a =
      a • ContactBicanonicalDerivative318.localSquare c i := by
  have h := (ContactBicanonicalSheaf318.localFrame c i).inv.app_smul a
    (show Γ(ContactIntrinsicFrames318.chart c i,⊤) from 1)
  change (ContactBicanonicalSheaf318.localFrame c i).inv.app ⊤ (show Γ(ContactIntrinsicFrames318.chart c i,⊤) from a*1) =
    a • (ContactBicanonicalSheaf318.localFrame c i).inv.app ⊤
      (show Γ(ContactIntrinsicFrames318.chart c i,⊤) from 1) at h
  simpa only [mul_one,ContactBicanonicalDerivative318.frame_inverse_one] using h

/-- The already constructed local q0 is the displayed regular coefficient
times the square of the actual universal coordinate derivative. -/
theorem q0_normalized (i : Option (Fin 4)) :
    ContactBicanonicalLocalSections318.q0 c i =
      coefficient0 c i • ContactBicanonicalDerivative318.localSquare c i := by
  cases i
  · exact frame_inverse c none (coefficient0 c none)
  · exact frame_inverse c (some _) (coefficient0 c (some _))

/-- The same exact intrinsic identification holds for local q1. This does
not assert whole-intersection compatibility or global gluing. -/
theorem q1_normalized (i : Option (Fin 4)) :
    ContactBicanonicalLocalSections318.q1 c i =
      coefficient1 c i • ContactBicanonicalDerivative318.localSquare c i := by
  cases i
  · exact frame_inverse c none (coefficient1 c none)
  · exact frame_inverse c (some _) (coefficient1 c (some _))
end ContactBicanonicalSectionNormalization318
