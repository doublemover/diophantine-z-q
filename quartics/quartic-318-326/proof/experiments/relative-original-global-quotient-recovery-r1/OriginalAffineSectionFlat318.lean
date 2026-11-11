module
public import AffineSectionQuotientFlat318
public import OriginalAffineSectionZero318
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public section
noncomputable section
namespace OriginalAffineSectionFlat318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open scoped TensorProduct
variable (R B : CommRingCat.{0}) [Algebra ℚ R] [Algebra ℚ B]
local notation "S" => (R ⊗[ℚ] B)
variable (L : Line (Spec (CommRingCat.of S)))
local notation "P" => OriginalLineAffineModel318.sections (CommRingCat.of S) L
variable (s : P)

/-- The actual coefficient-linear evaluation of the SAME original
whole-chart line and section. It is not a replacement trivial line. -/
abbrev evaluation := AffineSectionQuotientFlat318.evaluation R S P s

/-- Exact original zero scheme projection to the coefficient base. -/
@[expose] def projection : OriginalAffineSectionZero318.zeroScheme (CommRingCat.of S) L s ⟶
    Spec R :=
  OriginalAffineSectionZero318.into (CommRingCat.of S) L s ≫
    Spec.map (CommRingCat.ofHom (algebraMap R S))

lemma quotient_flat
    (hf : ∀ m : Ideal R, ∀ _ : m.IsMaximal,
      Function.Injective ((evaluation R B L s).baseChange (R ⧸ m))) :
    Module.Flat R (S ⧸ OriginalAffineSectionZero318.ideal (CommRingCat.of S) L s) := by
  letI : Module.Free R S :=
    Module.Free.of_basis ((Module.Free.chooseBasis ℚ B).baseChange R)
  letI := (OriginalLineAffineModel318.properties (CommRingCat.of S) L).1
  exact AffineSectionQuotientFlat318.flat R S P s hf

/-- The literal quotient/Spec projection is flat when its actual
residue evaluation maps are injective. All original chart module
projectivity and coefficient freeness are constructed internally. -/
lemma projection_flat
    (hf : ∀ m : Ideal R, ∀ _ : m.IsMaximal,
      Function.Injective ((evaluation R B L s).baseChange (R ⧸ m))) :
    Flat (projection R B L s) := by
  letI := quotient_flat R B L s hf
  unfold projection OriginalAffineSectionZero318.into
  rw [← Spec.map_comp]
  apply Flat.SpecMap_iff.mpr
  change (algebraMap R
    (S ⧸ OriginalAffineSectionZero318.ideal (CommRingCat.of S) L s)).Flat
  exact RingHom.flat_algebraMap_iff.mpr inferInstance
end OriginalAffineSectionFlat318
