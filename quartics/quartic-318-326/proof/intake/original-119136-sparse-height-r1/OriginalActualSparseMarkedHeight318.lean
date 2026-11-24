module
public import OriginalActualSparseJetArithmetic318
public import OriginalOneMarkedHeight318

/-! Attaches the first concrete original-point arithmetic certificate to the
conditional finite/arch endpoint. No repeated construction of period or
finite data in this file. Geometric fine-level and polarization transport
is not replaced by equality of moduli invariants. -/
public section
noncomputable section

namespace OriginalActualSparseMarkedHeight318

open OriginalActualSparseJetArithmetic318 OriginalSeparableSexticJet318
open Polynomial NumberField OriginalGlobalHodgeIdealHeight318 OriginalRawScalarCalibration318
open SelectedSameADirectBicanonicalHeight318 OriginalSexticJetMarked318
open scoped TensorProduct nonZeroDivisors

variable {E : Type*} [Field E] [NumberField E]

variable {H2 D2 : Type*} [AddCommGroup H2] [Module E H2] [AddCommGroup D2] [Module E D2]

/-- Concrete sparse reconstructed sextic and its exact ordinary tangent at
T=119136 flow into the original +11 consumer. The geometric identification of
that reconstructed wedge with the actual arithmetic family, the finite
tensor construction, and the matching complex germs remain explicit. The
certificate and its determinant are proved from frozen integer data. -/
theorem lower_for_reconstructed_germ
    (S3 S11 C : Type*) [CommRing S3] [CommRing S11] [CommRing C]
    [Algebra (𝓞 E) S3] [Algebra (𝓞 E) S11] [Algebra (𝓞 E) C]
    [Algebra S3 E] [Algebra S11 E] [Algebra C E] [Algebra S3 C] [Algebra S11 C]
    [IsScalarTower (𝓞 E) S3 E] [IsScalarTower (𝓞 E) S11 E] [IsScalarTower (𝓞 E) C E]
    [IsScalarTower S3 C E] [IsScalarTower S11 C E]
    [IsLocalization.Away (3:𝓞 E) S3] [IsLocalization.Away (11:𝓞 E) S11]
    [IsLocalization.Away (33:𝓞 E) C]
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module S3 M] [Module S11 N]
    [Module.Finite S3 M] [Module.Finite S11 N]
    (f : M →ₗ[S3] E) (g : N →ₗ[S11] E) (nz : ∃ m, f m ≠ 0)
    (mark : C ⊗[S3] M ≃ₗ[C] C ⊗[S11] N)
    (wedge : (OriginalHodgeModuleOverlap318.read (C:=C) g).comp mark.toLinearMap =
      OriginalHodgeModuleOverlap318.read f)
    (z3 : Fin 2 → M ⊗[S3] M) (z11 : Fin 2 → N ⊗[S11] N)
    (η : H2 ≃ₗ[E] E) (dt : D2 ≃ₗ[E] E) (ψ : H2 ≃ₗ[E] D2) (y : Fin 2 → D2)
    (at3 : ∀ i, ψ (η.symm (OriginalTwoMarkedTensorsR8_318.square f (z3 i))) = (210:E) • y i)
    (at11 : ∀ i, ψ (η.symm (OriginalTwoMarkedTensorsR8_318.square g (z11 i))) = (210:E) • y i)
    (readT : ∀ i, P ((119136:ℚ):E) * dt (y i) = coefficients (F:=E) 119136 i)
    (arch : InfinitePlace E → ℝ) (pos : ∀ w, 0 < arch w)
    (L : Lift E) (sameRaw : dt (ψ (η.symm 1)) = literalRawB L)
    (germs : ∀ w : InfinitePlace E, OriginalOneMarkedHeight318.Germ w 119136 (literalRawB L) (arch w)) :
    ∃ (I : FractionalIdeal (𝓞 E)⁰ E) (hn : I ≠ 0),
      (I:Submodule (𝓞 E) E) = f.range.restrictScalars (𝓞 E) ⊓ g.range.restrictScalars (𝓞 E) ∧
      Height.logHeight₁ (3723:ℚ) < 2*(idealFrame I hn arch pos).normalizedDegree + 11 := by
  have hs : P ((119136:ℚ):E) ≠ 0 := by norm_num [P]
  have oneGerm (w : InfinitePlace E) :
      OriginalOneMarkedHeight318.Germ w 119136 (dt (ψ (η.symm 1))) (arch w) := by
    rw [sameRaw]
    exact germs w
  obtain ⟨I, hn, hI, h⟩ := OriginalOneMarkedHeight318.lower_height S3 S11 C f g nz mark wedge
    z3 z11 η dt ψ y at3 at11 119136 hs readT arch pos oneGerm
  exact ⟨I, hn, hI, by simpa only [show (119136:ℚ)/32 = 3723 by norm_num] using h⟩

omit [NumberField E] in
/-- Over every characteristic-zero field containing the three defining
radicals, the three actual comparison entries force this very certificate's
literal arithmetic coefficient. This is a check of the exact geometry
handoff, not construction of the original cup-product comparison. -/
theorem raw_from_entries [CharZero E] (L : Lift E)
    (b00 b01 b11 e actualB : E)
    (hSign : e^2=1) (hActual : actualB = b00*b11-b01^2)
    (h00 : algebraMap E (data L).F.SplittingField b00 =
      algebraMap E (data L).F.SplittingField e * branchMoment (splittingCertificate (data L)) 0)
    (h01 : algebraMap E (data L).F.SplittingField b01 =
      algebraMap E (data L).F.SplittingField e * branchMoment (splittingCertificate (data L)) 1)
    (h11 : algebraMap E (data L).F.SplittingField b11 =
      algebraMap E (data L).F.SplittingField e * branchMoment (splittingCertificate (data L)) 2) :
    actualB = literalRawB L := by
  rw [hActual, ← evaluatedRawB L]
  exact rawB_of_polarized_entries _ _ _ _ _ hSign h00 h01 h11

end OriginalActualSparseMarkedHeight318

#print axioms OriginalActualSparseMarkedHeight318.lower_for_reconstructed_germ

#print axioms OriginalActualSparseMarkedHeight318.raw_from_entries
