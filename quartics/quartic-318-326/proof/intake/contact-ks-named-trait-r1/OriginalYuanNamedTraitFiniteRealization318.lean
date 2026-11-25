module

public import OriginalYuanActualFiniteSectionPayment318
public import OriginalYuanOriginalSectionPrincipalOpen318

@[expose] public section
noncomputable section

namespace OriginalYuanNamedTraitFiniteRealization318

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open NumberField SectionHeight318
open OriginalMarkedTraitAffineSectionPull318
open OriginalYuanMarkedSectionEvaluation318 OriginalYuanPulledExactKSImage318
open OriginalYuanActualFiniteSectionPayment318 OriginalYuanOriginalSectionPrincipalOpen318
open OriginalYuanAtPlaceFiniteProducer318 OriginalExactLocalKSUnit318
open OriginalRetainedComplexZeroByPasting318 (specOf)

universe u
variable {E K : Type u} [Field E] [NumberField E] [Field K]
variable (w : FinitePlace E)

variable {Y : Scheme.{u}} (U : Y.Opens) (hU : IsAffineOpen U)
variable (centre : Spec (CommRingCat.of (localRing w)) ⟶ Y)
variable (closed : @imageOfClosed (localRing w) _ _ Y centre∈U)
variable [IsDomain (chartRing U)] [Algebra (chartRing U) K] [IsFractionRing (chartRing U) K]

abbrev g : chartRing U→+*E := @sameGenericMap E _ _ w Y U hU centre closed

variable (oldMark : Spec (CommRingCat.of E) ⟶ Y)
variable (keepsMark : specOf (toHeldField w) ≫ centre=oldMark)

variable {M N : Type u}
  [AddCommGroup M] [AddCommGroup N] [Module (chartRing U) M] [Module (chartRing U) N]
variable (frame : N) (H C : FrameNorms E) (a b k : E) (ha : a≠0) (hb : b≠0)
variable (hH : H.finiteNorm w=(w a)⁻¹) (hC : C.finiteNorm w=(w b)⁻¹)
variable (η : ActualTensor w U hU centre closed M ≃ₗ[(localRing w)] coeffLine (R:=(localRing w)) (a^2))
variable (δ : ActualTensor w U hU centre closed N ≃ₗ[(localRing w)] coeffLine (R:=(localRing w)) b)
variable (basis_read : (δ (pullFrame w U hU centre closed frame):E)=b)

def actualBaseChange (raw : M→ₗ[chartRing U]N) :
    ActualTensor w U hU centre closed M →ₗ[(localRing w)] ActualTensor w U hU centre closed N := by
  letI : Algebra (chartRing U) (localRing w) := actualScalar w U hU centre closed
  exact raw.baseChange (localRing w)

variable (raw : M→ₗ[(chartRing U)]N) (injective : Function.Injective raw)
variable (regular : Function.Injective (OriginalRawKSPrimitive210318.scale210 : N→ₗ[(chartRing U)]N))
variable (rangeRaw : LinearMap.range raw=
  LinearMap.range (OriginalRawKSPrimitive210318.scale210 : N→ₗ[(chartRing U)]N))
variable (readRaw : ∀ m : ActualTensor w U hU centre closed M,
  (δ (actualBaseChange w U hU centre closed raw m):E)=(η m:E)*k)

variable (T dT : Stalk (g w U hU centre closed)) (sections : Fin 2→(chartRing U))
variable (num : P (structuralRead (K:=K) (g w U hU centre closed) T)*
  algebraMap (chartRing U) K (sections 0)=(2765952000:K)^2*
    (structuralRead (K:=K) (g w U hU centre closed) dT)^2)
variable (ratio : algebraMap (chartRing U) K (sections 1)=
  structuralRead (K:=K) (g w U hU centre closed) T*algebraMap (chartRing U) K (sections 0))
variable (t : E) (Tactual : pointRead (g w U hU centre closed) T=t)
variable (noncontact : P t≠0)
variable (frameActual : b*(pointRead (g w U hU centre closed) dT)^2=P t)

include basis_read num ratio Tactual noncontact frameActual hb hC in
theorem actual_finite_payment (i : Fin 2) :
    w (![(2765952000:E)^2,t*(2765952000:E)^2] i)*C.finiteNorm w≤1 := by
  let v := g w U hU centre closed
  obtain ⟨π,hπ,T₀,d₀,hT,hd,hnum,hratio⟩ :=
    source_to_named_principal_open (K:=K) v T dT sections num ratio
  let good : IsUnit (v π) := point_unit v ⟨π,hπ⟩
  have ht : dGeneric U hU centre closed (toHeldField w) π good T₀=t := by
    change IsLocalization.Away.lift π (g:=v) good T₀=t
    exact hT.trans Tactual
  have hf : b*(dGeneric U hU centre closed (toHeldField w) π good d₀)^2=P t := by
    change b*(IsLocalization.Away.lift π (g:=v) good d₀)^2=P t
    exact (congrArg (fun z:E=>b*z^2) hd).trans frameActual
  exact literal_pair_paid w U hU centre closed frame b δ basis_read π good
    sections T₀ d₀ t ht noncontact hnum hratio hf C hb hC i

include keepsMark basis_read num ratio Tactual noncontact frameActual readRaw
  injective regular rangeRaw ha hb hH hC in
/-- The unchanged exact two finite slots over the *same* named
original trait. This consumes the real model affine data, not
a postulated local span equation or an independent point. -/
theorem exact_v11_slots :
    Nonempty (OriginalFiveContactExactGauge318.FiniteImage H C k w) ∧
    (specOf (g w U hU centre closed) ≫ hU.fromSpec=oldMark) ∧
    (∀ i : Fin 2, w (![(2765952000:E)^2,t*(2765952000:E)^2] i)*C.finiteNorm w≤1) := by
  letI : Algebra (chartRing U) (localRing w) := actualScalar w U hU centre closed
  exact ⟨⟨exact_place_image w raw injective regular rangeRaw H C a b k ha hb hH hC η δ readRaw⟩,
    generic_section_factor_is_held w U hU centre closed oldMark keepsMark,
    actual_finite_payment w U hU centre closed frame C b hb hC δ basis_read T dT
      sections num ratio t Tactual noncontact frameActual⟩

end OriginalYuanNamedTraitFiniteRealization318
