module
public import G4Nonvanishing
public import ConcreteG8Domain
public section
namespace ConcreteG4Domain
open ConcreteG8Domain

theorem G4_nonzero (x : K) : G4Nonvanishing.G4 x ≠ 0 :=
  G4Nonvanishing.G4_nonzero (by rw [dimension]; decide) x

/-- Global nonvanishing on the actual rational quadratic field, including
negative real components of the relaxed anchor chart. -/
theorem actual_V0_denominator_nonzero (f0 f1 : ℚ) :
    G4Nonvanishing.G4 (D*(pair f0 f1)^2) ≠ 0 := G4_nonzero _
end ConcreteG4Domain
