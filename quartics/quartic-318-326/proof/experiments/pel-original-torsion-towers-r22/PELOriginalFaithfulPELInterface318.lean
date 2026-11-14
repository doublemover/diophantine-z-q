module
public import PELOriginalSurfaceLineInterface318
public import PELOriginalOrderDivisionTorsorIso318
public import PELOriginalOrderAdjointUniqueness318
public import PELOriginalPolarizedOrderAction318
public section
noncomputable section
namespace PELOriginalFaithfulPELInterface318
open AlgebraicGeometry CategoryTheory PELPrincipalOrderCoordinates318
open PELOriginalReducedProjectiveCandidate318 PELOriginalSchemePointGroup318
open PELOriginalOrderSchemeMorphism318 PELOriginalOrderIntegralNorm318
open PELOriginalOrderHermitianAdjoint318
variable (τ : ℂ) (hτ : 0<τ.im)

/-- Exact original PEL/isogeny interface. This packages the faithful
order, positive involution, whole normalized-family comparison, all-test
pairing and native scheme degrees on one identified original surface.
Representability of the dual and theta/Jacobian geometry are separate. -/
structure Certificate : Prop where
  surface_line : PELOriginalSurfaceLineInterface318.Certificate τ hτ
  faithful : Function.Injective (morphism τ hτ)
  positive : ∀ a : order,a≠0 → 0<PELQuaternionAlgebra318.reducedTrace
    ((a:PELQuaternionAlgebra318.B)*(adjoint a:PELQuaternionAlgebra318.B))
  involutive : ∀ a : order,adjoint (adjoint a)=a
  antimultiplicative : ∀ a b : order,adjoint (a*b)=adjoint b*adjoint a
  family_iso : ∀ a : order,Nonempty
    ((PELOriginalRosatiPolarizationFamily318.leftLine τ hτ a).object ≅
      (PELOriginalRosatiPolarizationFamily318.rightLine τ hτ a).object)
  pairing_covariance : ∀ (T : Scheme) (ρ : T⟶Spec (CommRingCat.of ℂ))
    (a b : order) (x y : Points τ hτ T ρ),
    PELOriginalPolarizationBicharacter318.pairing τ hτ ρ
      (PELOriginalUniversalOrderAction318.endomorphism τ hτ ρ a x)
      (PELOriginalUniversalOrderAction318.endomorphism τ hτ ρ b y)=
    PELOriginalPolarizationBicharacter318.pairing τ hτ ρ x
      (PELOriginalUniversalOrderAction318.endomorphism τ hτ ρ (adjoint a*b) y)
  isogeny : ∀ a : order,norm a≠0 →
    IsFinite (morphism τ hτ a) ∧ Etale (morphism τ hτ a) ∧
    Function.Surjective (morphism τ hτ a) ∧
    ∀ y : candidate τ hτ,(morphism τ hτ a).finrank y=(norm a).natAbs^2
  base_change_degree : ∀ (T : Scheme) (p : T⟶candidate τ hτ)
    (a : order),norm a≠0 → ∀ t : T,
    (CategoryTheory.Limits.pullback.snd (morphism τ hτ a) p).finrank t=(norm a).natAbs^2

/-- Concrete construction, not a new unproved PEL or polarization axiom. -/
theorem actual : Certificate τ hτ := by
  refine {
    surface_line := PELOriginalSurfaceLineInterface318.actual τ hτ
    faithful := PELOriginalPolarizedOrderAction318.faithful τ hτ
    positive := PELOriginalOrderPositiveInvolution318.positive
    involutive := PELOriginalOrderPositiveInvolution318.involutive
    antimultiplicative := PELOriginalOrderPositiveInvolution318.antimultiplicative
    family_iso := fun a => ⟨PELOriginalRosatiPolarizationFamily318.iso τ hτ a⟩
    pairing_covariance := fun T ρ a b x y =>
      PELOriginalTwoOrderPairing318.covariance τ hτ a b ρ x y
    isogeny := ?_
    base_change_degree := fun T p a ha t =>
      PELOriginalOrderIsogenyDegree318.baseChange_degree τ hτ a ha p t }
  intro a ha
  obtain ⟨hf,he,hs⟩ := PELOriginalEtaleOrderIsogeny318.finite_etale_surjective τ hτ a ha
  exact ⟨hf,he,hs,PELOriginalOrderIsogenyDegree318.degree τ hτ a ha⟩

/-- The adjoint in the certificate is uniquely determined by the
actual universal line-valued pairing, not by trivial Spec(C) line classes. -/
theorem adjoint_unique (a b : order)
    (h : ∀ (T : Scheme) (ρ : T⟶Spec (CommRingCat.of ℂ)) (x y : Points τ hτ T ρ),
      PELOriginalPolarizationBicharacter318.pairing τ hτ ρ
        (PELOriginalUniversalOrderAction318.endomorphism τ hτ ρ a x) y=
      PELOriginalPolarizationBicharacter318.pairing τ hτ ρ x
        (PELOriginalUniversalOrderAction318.endomorphism τ hτ ρ b y)) : b=adjoint a :=
  PELOriginalOrderAdjointUniqueness318.unique τ hτ a b h
end PELOriginalFaithfulPELInterface318
