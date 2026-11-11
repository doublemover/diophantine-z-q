module
public import OriginalCartierZeroKernelIso318
public import ContactOriginalZeroKernelIso318
public import ContactResidueCartierCharts318
public import ActualClosedIdealModule318
public section
noncomputable section
namespace ContactResidueActualIdealLine318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalSectionParameter318
open ContactGeneratedLocalUniversalRegular318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (s : Γ(L.object,⊤)) (hs : ContactResidueRegularFlat318.ResidueNonzero R c L s)
local notation "S" => R
local notation "U" => L
local notation "p" => ContactGlobalSectionZero318.into R c L s
local notation "I" => FramedLineInverse318.inverse L

/-- The ORIGINAL inverse line is the ACTUAL zero ideal module for any
original section with nonzero residue fibers. All regular-chart and
original affine-cover inputs are constructed, not assumed separately. -/
@[expose] def iso : I.object ≅ ActualClosedIdealModule318.object p :=
  OriginalCartierZeroKernelIso318.iso U s
    (ContactOriginalZeroKernelIso318.rings S c) (ContactOriginalZeroKernelIso318.charts S c)
    (ContactOriginalZeroKernelIso318.cover S c) p
    (ContactOriginalZeroKernelIso318.zeroCharts S c U s)
    (ContactOriginalZeroKernelIso318.zero_squares S c U s)
    (ContactResidueCartierCharts318.regular_charts R c L s hs)

/-- The inclusion is the exact global inverse-line contraction previously
constructed from original transition units; the module is not relabeled
IdealSheafData and no nilpotent structure is discarded. -/
@[reassoc] lemma iso_inclusion : (iso R c L s hs).hom ≫
    ActualClosedIdealModule318.inclusion p =
      InverseLineSectionContraction318.hom U s :=
  OriginalCartierZeroKernelIso318.iso_inclusion U s
    (ContactOriginalZeroKernelIso318.rings S c) (ContactOriginalZeroKernelIso318.charts S c)
    (ContactOriginalZeroKernelIso318.cover S c) p
    (ContactOriginalZeroKernelIso318.zeroCharts S c U s)
    (ContactOriginalZeroKernelIso318.zero_squares S c U s)
    (ContactResidueCartierCharts318.regular_charts R c L s hs)

/-- Genuine line structure on the actual kernel sheaf of the original
zero embedding, retaining its inclusion and its original inverse-line
class. This works over the whole possibly nonreduced coefficient ring. -/
@[expose] def line : Line (curve S c) where
  object := ActualClosedIdealModule318.object p
  Index := I.Index
  opens := I.opens
  cover := I.cover
  frame i := I.frame i ≪≫ (Scheme.Modules.restrictFunctor (I.opens i).ι).mapIso (iso R c L s hs)

lemma line_object : (line R c L s hs).object=ActualClosedIdealModule318.object p := rfl
end ContactResidueActualIdealLine318
