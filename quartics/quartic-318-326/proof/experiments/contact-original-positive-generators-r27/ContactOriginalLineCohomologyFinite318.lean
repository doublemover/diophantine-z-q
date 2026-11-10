module
public import ContactOriginalLineSectionsFinite318
public section
noncomputable section
namespace ContactOriginalLineCohomologyFinite318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open OriginalLineRestrictionAdditive318
variable (c : Fin 4 → ℚˣ) (L : Line (ContactProjectiveModel318.model c))

/-- Degree zero remains the original derived Ext carrier with the action
induced by actual original coefficient multiplication. -/
instance : Module ℚ (Sheaf.H (additive L) 0) :=
  OriginalLineRationalCohomology318.cohomologyModule (ContactIntrinsicDifferentials318.structureMap c) L 0

def degreeZeroLinear : Sheaf.H (additive L) 0 →ₗ[ℚ] Γ(L.object,⊤) :=
  (Sheaf.H.equiv₀ (additive L) CategoryTheory.Limits.isTerminalTop).toAddMonoidHom.toRatLinearMap

lemma degreeZero_injective : Function.Injective (degreeZeroLinear c L) :=
  (Sheaf.H.equiv₀ (additive L) CategoryTheory.Limits.isTerminalTop).injective

instance finite_h0 : FiniteDimensional ℚ (Sheaf.H (additive L) 0) :=
  FiniteDimensional.of_injective (degreeZeroLinear c L) (degreeZero_injective c L)

/-- Both original cohomological dimensions are finite for EVERY original
line, with the structural actions fixed before any coordinate comparison. -/
theorem finite_h0_h1 :
    FiniteDimensional ℚ (Sheaf.H (additive L) 0) ∧
    FiniteDimensional ℚ (ContactOriginalCohomologyCoordinates318.H1 c L) :=
  ⟨inferInstance,inferInstance⟩

/-- Degree-zero comparison retains the actual scalar section on the full
original model, agreeing with the independently defined coefficient action. -/
lemma degreeZero_scalar (a : ℚ) (x : Sheaf.H (additive L) 0) :
    degreeZeroLinear c L (a • x) =
      NormalizedStructureTrace318.scalar (ContactIntrinsicDifferentials318.structureMap c) ⊤ a •
        degreeZeroLinear c L x :=
  (degreeZeroLinear c L).map_smul a x
end ContactOriginalLineCohomologyFinite318
