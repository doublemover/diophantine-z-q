module
public import OriginalChartZeroKernelIso318
public import ContactZeroAffineRefinement318
public section
noncomputable section
namespace ContactOriginalZeroKernelIso318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 SectionZeroAffineRefinement318
open scoped TensorProduct
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)

@[expose] def rings : Fin 2 → CommRingCat.{0} :=
  Fin.cases (CommRingCat.of (R ⊗[ℚ] finiteRing c))
    (fun _ => CommRingCat.of (R ⊗[ℚ] infinityRing c))
@[expose] def charts (i : Fin 2) : Spec (rings R c i) ⟶ curve R c := by
  fin_cases i
  · exact finiteInto R c
  · exact infinityInto R c
instance (i : Fin 2) : IsOpenImmersion (charts R c i) := by
  fin_cases i <;> dsimp [charts] <;> infer_instance

lemma cover : ⊤≤⨆i,(charts R c i).opensRange := by
  intro x _
  have h : x∈(finiteInto R c).opensRange ⊔ (infinityInto R c).opensRange := by
    rw [ContactOriginalRelativePolynomialCharts318.cover]
    trivial
  rcases h with h | h
  · exact Opens.mem_iSup.mpr ⟨0,h⟩
  · exact Opens.mem_iSup.mpr ⟨1,h⟩

variable (L : Line (curve R c)) (s : Γ(L.object,⊤))
local notation "p" => ContactGlobalSectionZero318.into R c L s
@[expose] def zeroCharts (i : Fin 2) :
    Spec (CommRingCat.of (rings R c i⧸sectionIdeal (rings R c i) (charts R c i) L s)) ⟶
      ContactGlobalSectionZero318.scheme R c L s := by
  fin_cases i
  · exact ContactZeroAffineRefinement318.finiteChart R c L s
  · exact ContactZeroAffineRefinement318.infinityChart R c L s

lemma zero_squares (i : Fin 2) : IsPullback
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      (sectionIdeal (rings R c i) (charts R c i) L s)))) (zeroCharts R c L s i) (charts R c i) p := by
  fin_cases i
  · exact ContactZeroAffineRefinement318.finite_square R c L s
  · exact ContactZeroAffineRefinement318.infinity_square R c L s

/-- Regularity concerns the SAME actual section on the internally
produced joint affine basis of the original finite/infinity curve. -/
abbrev Regular := OriginalChartZeroKernelIso318.Regular L s (rings R c) (charts R c)

/-- The actual original section-zero ideal module is globally the inverse
line, provided THIS section is regular on its actual joint affine basis.
All covers, original zero equations and quotient squares are constructed
internally. This is not an unconditional claim for the zero section. -/
@[expose] def iso (hr : Regular R c L s) :
    (FramedLineInverse318.inverse L).object ≅ ActualClosedIdealModule318.object p :=
  OriginalChartZeroKernelIso318.iso L s (rings R c) (charts R c) (cover R c) p
    (zeroCharts R c L s) (zero_squares R c L s) hr

@[reassoc] lemma iso_inclusion (hr : Regular R c L s) :
    (iso R c L s hr).hom ≫ ActualClosedIdealModule318.inclusion p =
      InverseLineSectionContraction318.hom L s :=
  OriginalChartZeroKernelIso318.iso_inclusion L s (rings R c) (charts R c) (cover R c) p
    (zeroCharts R c L s) (zero_squares R c L s) hr
end ContactOriginalZeroKernelIso318
