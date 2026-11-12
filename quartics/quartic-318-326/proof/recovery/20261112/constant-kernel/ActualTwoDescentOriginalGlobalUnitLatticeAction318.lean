module
public import ActualTwoDescentOriginalGeometricConstantKernel318
public section
noncomputable section
namespace ActualTwoDescentOriginalGlobalUnitLatticeAction318
open AlgebraicGeometry CategoryTheory
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalSchemeIntegral318
open ActualTwoDescentOriginalDoublePoleLocalGlobal318 ActualTwoDescentOriginalCommonPolarizationLattices318
variable {K : Type*} [Field K] [CharZero K]
local instance (n : K) : Nonempty (⊤ : (originalCubicScheme n).Opens) := ⟨⟨genericPoint _,trivial⟩⟩
/-- Every ACTUAL global regular unit acts on all intrinsic lattices,
through its actual unit germ at each point. -/
lemma preserves (n : K) (s : Γ(originalCubicScheme n,⊤)ˣ)
    (x : originalCubicScheme n) (f : SchemeFunctionField n) :
    f∈pointImage n x ↔
      (originalCubicScheme n).germToFunctionField ⊤ (s:Γ(originalCubicScheme n,⊤))*f∈pointImage n x := by
  let u : ((originalCubicScheme n).presheaf.stalk x)ˣ :=
    Units.map ((originalCubicScheme n).presheaf.germ ⊤ x trivial).hom.toMonoidHom s
  have hu : algebraMap ((originalCubicScheme n).presheaf.stalk x) (SchemeFunctionField n)
      (u:((originalCubicScheme n).presheaf.stalk x))=
      (originalCubicScheme n).germToFunctionField ⊤ (s:Γ(originalCubicScheme n,⊤)) := by
    change algebraMap _ _ ((originalCubicScheme n).presheaf.germ ⊤ x trivial (s:Γ(originalCubicScheme n,⊤)))=_
    rw [Scheme.algebraMap_germ_eq_germToFunctionField]
  simp only [actual_image,lattice]
  rw [←hu]
  exact ActualTwoDescentFractionalLineStabilizerRegularity318.unit_preserves (weight n x) u f
variable [IsAlgClosed K]
def baseUnit (n : K) (c : Kˣ) : (SchemeFunctionField n)ˣ :=
  Units.map (ActualTwoDescentOriginalConstantLatticeUnits318.baseCoefficient n).toMonoidHom c
/-- Conversely EVERY base unit preserves the same line's entire
intrinsic stalk family, not just the selected translation generators. -/
lemma base_preserves (n : K) (c : Kˣ) (x : originalCubicScheme n) (f : SchemeFunctionField n) :
    f∈pointImage n x ↔ (baseUnit n c:SchemeFunctionField n)*f∈pointImage n x := by
  letI : IsProper (structureMap n) := ActualTwoDescentOriginalSeparatedComparison318.proper n
  exact preserves n (Units.map
    (ActualTwoDescentProperClosedFieldConstants318.structural (structureMap n)).toMonoidHom c) x f

end ActualTwoDescentOriginalGlobalUnitLatticeAction318
