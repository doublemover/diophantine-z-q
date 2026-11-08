module
public import ContactBicanonicalSheaf318
public import ContactBicanonicalCoefficients318
public section
noncomputable section
namespace ContactBicanonicalLocalSections318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ)

/-- Actual local sheaf sections. Their full-intersection compatibility is a later theorem. -/
@[expose] def q0 : (i : Option (Fin 4)) →
    Γ((ContactBicanonicalSheaf318.bicanonical c).restrict (ContactIntrinsicFrames318.embedding c i),⊤)
  | some i => (ContactBicanonicalSheaf318.localFrame c (some i)).inv.app ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of (ContactIntrinsicFrames318.BranchRing c i))).inv
        (ContactBicanonicalCoefficients318.branchQ0 c i))
  | none => (ContactBicanonicalSheaf318.localFrame c none).inv.app ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of (InfinityGlobalChart318.InfinityOrder c))).inv
        (ContactBicanonicalCoefficients318.infinityQ0 c))

@[expose] def q1 : (i : Option (Fin 4)) →
    Γ((ContactBicanonicalSheaf318.bicanonical c).restrict (ContactIntrinsicFrames318.embedding c i),⊤)
  | some i => (ContactBicanonicalSheaf318.localFrame c (some i)).inv.app ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of (ContactIntrinsicFrames318.BranchRing c i))).inv
        (ContactBicanonicalCoefficients318.branchQ1 c i))
  | none => (ContactBicanonicalSheaf318.localFrame c none).inv.app ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of (InfinityGlobalChart318.InfinityOrder c))).inv
        (ContactBicanonicalCoefficients318.infinityQ1 c))
end ContactBicanonicalLocalSections318
