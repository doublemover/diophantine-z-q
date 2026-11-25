module

public import OriginalThreeElevenNamedProperCentres318
public import OriginalYuanNamedTraitFiniteRealization318

@[expose] public section
noncomputable section

namespace OriginalAllFiniteTrueAffineData318

open AlgebraicGeometry CategoryTheory
open NumberField SectionHeight318
open scoped nonZeroDivisors
open OriginalFineArithmeticPlaceSwitch318 OriginalThreeElevenNamedProperCentres318
open OriginalYuanNamedTraitFiniteRealization318 OriginalExactLocalKSUnit318
open OriginalYuanActualFiniteSectionPayment318 OriginalYuanPulledExactKSImage318
open OriginalYuanOriginalSectionPrincipalOpen318 OriginalYuanMarkedSectionEvaluation318
open OriginalMarkedTraitAffineSectionPull318

universe u

variable {E : Type u} [Field E] [NumberField E]
variable (B : OriginalFineBases.{u}) (m : CommonMark (E:=E) B)

abbrev prime (w : FinitePlace E) := FinitePlace.maximalIdeal w
abbrev lane (w : FinitePlace E) := selected (prime w)
abbrev centreAt (w : FinitePlace E) :
    Spec (CommRingCat.of (localRing w)) ⟶ B.lower (lane w) :=
  namedCentre B m (prime w)

/-- Exact finite models, both chosen from one held mark. The
primitive local Hodge/dualizing frames are sheaf frames there,
not frame choices on independently identified E-lines. The
generic specialization maps to H,C are required to be their
actual canonical linear realizations on the chosen lower model. -/
structure At
    (H C : FrameNorms E) (t : E)
    (Hg Cg : Lane→Type u)
    (heldH : ∀ n,Hg n→E) (heldC : ∀ n,Cg n→E)
    (heldRaw : ∀ n,Hg n→Cg n)
    (w : FinitePlace E) where
  U : (B.lower (lane w)).Opens
  affine : IsAffineOpen U
  closed : @imageOfClosed (localRing w) _ _ (B.lower (lane w)) (centreAt B m w)∈U
  K : Type u
  [fieldK : Field K]
  [chartDomain : IsDomain (chartRing U)]
  [toStructuralField : Algebra (chartRing U) K]
  [fractionK : IsFractionRing (chartRing U) K]
  M : Type u
  N : Type u
  [addM : AddCommGroup M]
  [addN : AddCommGroup N]
  [moduleM : Module (chartRing U) M]
  [moduleN : Module (chartRing U) N]
  frame : N
  a : E
  b : E
  a_ne : a≠0
  b_ne : b≠0
  hodgeNorm : H.finiteNorm w=(w a)⁻¹
  canonicalNorm : C.finiteNorm w=(w b)⁻¹
  hodgeCoeff : ActualTensor w U affine (centreAt B m w) closed M ≃ₗ[localRing w]
    coeffLine (R:=localRing w) (a^2)
  canonicalCoeff : ActualTensor w U affine (centreAt B m w) closed N ≃ₗ[localRing w]
    coeffLine (R:=localRing w) b
  frame_read : (canonicalCoeff (pullFrame w U affine (centreAt B m w) closed frame):E)=b
  raw : M→ₗ[chartRing U]N
  rawInj : Function.Injective raw
  regular210 : Function.Injective (OriginalRawKSPrimitive210318.scale210 : N→ₗ[chartRing U]N)
  rawRange : LinearMap.range raw =
    LinearMap.range (OriginalRawKSPrimitive210318.scale210 : N→ₗ[chartRing U]N)
  genericH : ActualTensor w U affine (centreAt B m w) closed M → Hg (lane w)
  genericC : ActualTensor w U affine (centreAt B m w) closed N → Cg (lane w)
  hodge_generic_read : ∀ z, (hodgeCoeff z:E)=heldH (lane w) (genericH z)
  canonical_generic_read : ∀ z, (canonicalCoeff z:E)=heldC (lane w) (genericC z)
  raw_generic : ∀ z, genericC
    (actualBaseChange w U affine (centreAt B m w) closed raw z)=heldRaw (lane w) (genericH z)
  T : Stalk (g w U affine (centreAt B m w) closed)
  dT : Stalk (g w U affine (centreAt B m w) closed)
  sections : Fin 2→chartRing U
  numerator :
    P (structuralRead (K:=K) (g w U affine (centreAt B m w) closed) T)*
      algebraMap (chartRing U) K (sections 0)=(2765952000:K)^2*
        (structuralRead (K:=K) (g w U affine (centreAt B m w) closed) dT)^2
  ratio : algebraMap (chartRing U) K (sections 1)=
    structuralRead (K:=K) (g w U affine (centreAt B m w) closed) T*
      algebraMap (chartRing U) K (sections 0)
  Tactual : pointRead (g w U affine (centreAt B m w) closed) T=t
  frameActual : b*(pointRead (g w U affine (centreAt B m w) closed) dT)^2=P t

end OriginalAllFiniteTrueAffineData318
