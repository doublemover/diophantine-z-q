module
public import SelectedActualWholeNumberFieldRoot318
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import all SelectedGreenLiteralWholeComplexField318
public section
noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial
open SelectedLiteralTorsionKernel318 SelectedPrimitiveOpen318 SelectedPrimitiveAffineSign318
open SelectedPrimitiveFixedX318 SelectedPrimitiveXCharacteristic318
open SelectedActualPrimitiveKernelAffine318 SelectedGreenLiteralWholeComplexField318
open SelectedActualComplexOrdinaryScalar318 SelectedRationalGenericFromComplex318

namespace SelectedLiteralArithmeticChart318

theorem kernelFinite (N : ℕ) : IsFinite (kernelProjection N N) :=
  (native_level_instances N).1

theorem kernelEtale (N : ℕ) : Etale (kernelProjection N N) :=
  (native_level_instances N).2

attribute [local instance] kernelFinite kernelEtale

/-- One complete original chart, fixed before choosing the number
field of the J=1 centres or making a stable-reduction extension. -/
structure Chart (N : ℕ) [NeZero N] (hN : 2 < N) where
  I : Ideal (D N)
  e : PrimitiveScheme N N ≅ Spec (CommRingCat.of (D N ⧸ I))
  hz : intoAffine N N (Nat.lt_of_succ_lt hN) =
    e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  «over» : primitiveProjection N N = e.hom ≫ Spec.algebraMap (R N) (D N ⧸ I)
  sign : (D N ⧸ I) →ₐ[R N] (D N ⧸ I)
  sign_compat : sign.comp (q N I) = (q N I).comp (SelectedPrimitiveAffineSign318.sign N)
  sign_involution : sign.comp sign = AlgHom.id (R N) (D N ⧸ I)
  powers : PowerBasis (R N) (fixed N I sign)
  power_x : powers.gen = coordinate N I sign sign_compat
  p : (R N)[X]
  characteristic :
    letI : Module.Free (R N) (fixed N I sign) := Module.Free.of_basis powers.basis
    letI : Module.Finite (R N) (fixed N I sign) := powers.finite
    p = charPolynomial N I sign sign_compat
  monic : p.Monic
  chartEquiv : AdjoinRoot p ≃ₐ[R N] fixed N I sign
  same_x : chartEquiv (AdjoinRoot.root p) = coordinate N I sign sign_compat
  derivativeUnit : IsUnit (AdjoinRoot.mk p p.derivative)
  complexWhole : IsField (AdjoinRoot (SelectedComplexOrdinaryOneField318.genericPolynomial
    (p.map (toComplex N))))

/-- Creation from the *compiled* full complex root locus; no new
roots, irreducible factors, or coefficient charts enter. -/
theorem chart_nonempty (N : ℕ) [NeZero N] (hN : 2 < N) : Nonempty (Chart N hN) := by
  obtain ⟨I,e,hz,hb,σ,hσ,hi,pb,hpb,hp⟩ := literal_level_whole_field N hN
  letI : Module.Free (R N) (fixed N I σ) := Module.Free.of_basis pb.basis
  letI : Module.Finite (R N) (fixed N I σ) := pb.finite
  obtain ⟨p,hc,hm,ep,hr,hd,hf⟩ := hp
  exact ⟨⟨I,e,hz,hb,σ,hσ,hi,pb,hpb,p,hc,hm,ep,hr,hd,hf⟩⟩

def originalChart (N : ℕ) [NeZero N] (hN : 2 < N) : Chart N hN :=
  Classical.choice (chart_nonempty N hN)

variable {N : ℕ} [NeZero N] {hN : 2 < N}

/-- The exact same polynomial determines the whole rational compact
function field. This applies to every retained chart witness. -/
theorem Chart.rationalWhole (C : Chart N hN) :
    IsField (AdjoinRoot (C.p.map (rationalGenericMap N))) := by
  apply rational_isField N C.p C.monic
  have hf := C.complexWhole
  change IsField (AdjoinRoot (((C.p).map (toComplex N)).map
    (algebraMap SelectedComplexOrdinaryBase318.Base SelectedComplexOrdinaryOneField318.Generic))) at hf
  rw [Polynomial.map_map] at hf
  exact hf

/-- L may be chosen *after* the chart, as the actual J=1 splitting
field or any stable-reduction enlargement. The auxiliary complex
embedding only reflects absolute irreducibility; no selected complex
or arithmetic component is built into the retained chart. -/
theorem Chart.arithmeticWhole (C : Chart N hN) (L : Type) [Field L] [NumberField L] :
    IsField (AdjoinRoot (C.p.map (SelectedActualWholeNumberFieldRoot318.coefficientMap L N))) := by
  let ι : L →ₐ[ℚ] ℂ := IsAlgClosed.lift
  exact SelectedActualWholeNumberFieldRoot318.whole_isField L N ι.toRingHom C.p C.monic C.complexWhole

end SelectedLiteralArithmeticChart318

#print axioms SelectedLiteralArithmeticChart318.chart_nonempty
#print axioms SelectedLiteralArithmeticChart318.Chart.rationalWhole
#print axioms SelectedLiteralArithmeticChart318.Chart.arithmeticWhole
