module
public import OriginalCartierZeroKernelIso318
public import ContactOriginalZeroKernelIso318
public import ContactUniversalCartierCharts318
public import ContactUniversalActualIdealModule318
public section
noncomputable section
namespace ContactUniversalActualIdealLine318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalSectionParameter318
open ContactGeneratedLocalUniversalRegular318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local notation "M" => generatedLine R c L
local instance : Module R Γ(M.object,⊤) := OriginalCoefficientCohomology318.sectionModule R
  (ContactRelativeStructuralHOne318.projection R c) M ⊤
local notation "S" => CommRingCat.of (parameterRing R c M)
local instance : Algebra ℚ S := ((algebraMap R S).comp (algebraMap ℚ R)).toAlgebra
local instance : IsScalarTower ℚ R S := IsScalarTower.of_algebraMap_eq' rfl
local notation "U" => universalLine R c M
local notation "s" => universalSection R c M (properties R c L).1
local notation "p" => ContactGlobalSectionZero318.into S c U s
local notation "I" => FramedLineInverse318.inverse U

/-- UNCONDITIONAL global identification for the SAME actual universal
section on the original Contact model. The actual kernel module, all
zero charts, original affine/frame basis, and its regularity are produced
internally. No extra Regular/kernel/cover premise is passed by the caller. -/
@[expose] def iso : I.object ≅ ContactUniversalActualIdealModule318.object R c L :=
  OriginalCartierZeroKernelIso318.iso U s
    (ContactOriginalZeroKernelIso318.rings S c) (ContactOriginalZeroKernelIso318.charts S c)
    (ContactOriginalZeroKernelIso318.cover S c) p
    (ContactOriginalZeroKernelIso318.zeroCharts S c U s)
    (ContactOriginalZeroKernelIso318.zero_squares S c U s)
    (ContactUniversalCartierCharts318.regular_charts R c L)

/-- The inclusion is the exact global inverse-line contraction previously
constructed from original transition units; the module is not relabeled
IdealSheafData and no nilpotent structure is discarded. -/
@[reassoc] lemma iso_inclusion : (iso R c L).hom ≫
    ContactUniversalActualIdealModule318.inclusion R c L =
      InverseLineSectionContraction318.hom U s :=
  OriginalCartierZeroKernelIso318.iso_inclusion U s
    (ContactOriginalZeroKernelIso318.rings S c) (ContactOriginalZeroKernelIso318.charts S c)
    (ContactOriginalZeroKernelIso318.cover S c) p
    (ContactOriginalZeroKernelIso318.zeroCharts S c U s)
    (ContactOriginalZeroKernelIso318.zero_squares S c U s)
    (ContactUniversalCartierCharts318.regular_charts R c L)

/-- Genuine invertible sheaf structure on the ACTUAL universal zero ideal
module, transported along the proved global identification. This is a
total-family Cartier assertion, not parameter-flatness or regularity of
every specialized section. -/
@[expose] def line : Line (curve S c) where
  object := ContactUniversalActualIdealModule318.object R c L
  Index := I.Index
  opens := I.opens
  cover := I.cover
  frame i := I.frame i ≪≫ (Scheme.Modules.restrictFunctor (I.opens i).ι).mapIso (iso R c L)

lemma line_object : (line R c L).object=ContactUniversalActualIdealModule318.object R c L := rfl
end ContactUniversalActualIdealLine318
