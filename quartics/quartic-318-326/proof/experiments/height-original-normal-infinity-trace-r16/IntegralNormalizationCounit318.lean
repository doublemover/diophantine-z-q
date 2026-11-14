module
public import FiniteDualRestriction318
public import IntegralNormalizationFiniteDual318
public section
noncomputable section
namespace IntegralNormalizationCounit318
open Polynomial IntegralDistinctContactOpen318
variable (R : Type*) [CommRing R] [IsDomain R] [CharZero R]
  [IsNoetherianRing R] [IsIntegrallyClosed R[X]] (a d : Fin 4 → R)
  [IsDomain (OpenOrder R a d)] (hd : ∀ i,d i ≠ 0)
local notation "P" => Polynomial R
local notation "A" => Source R a d
local notation "B" => OpenOrder R a d
local notation "N" => IntegralFourRootNormalizationConductor318.normalOrder R a d
local notation "L" => NormalTraceDualModule318.lattice (F:=Base R a d) N
local notation "inc" => IntegralFourRootNormalizationConductor318.inclusion R a d
local notation "into" => IntegralFourRootNormalizationConductor318.intoNormal R a d
local notation "δ" => IntegralFourRootNormalizationConductor318.different R a d

abbrev rawFrame := FourRootIntegralDuality318.frame
  (DistinctContactIntegralDomain318.coefficient R a d)

@[expose] def coordinate :
    letI : Module A (FiniteDualModuleAction318.Dual P N) := Module.compHom _ into.toRingHom
    FiniteDualModuleAction318.Dual P N →ₗ[A] A :=
  FiniteDualRestriction318.coordinate into (rawFrame R a d)

/-- The normalization counit has literal raw coefficient δ*z for
EVERY normal dual element. It is obtained by restriction on all raw-order
arguments; the different is not silently absorbed in the normalization. -/
theorem coefficient_formula (z : L) :
    inc (coordinate R a d (IntegralNormalizationFiniteDual318.equivalence R a d hd z))=
      δ*z.val := by
  let zJ := IntegralNormalizationTraceFunctional318.differentEquiv R a d z
  obtain ⟨c,hc,hcval⟩ := (IntegralNormalizationConductorDual318.data R a d hd).value zJ 1
  have hc' : inc c=δ*z.val := by
    change inc c=(δ*z.val)*1 at hc
    simpa only [mul_one] using hc
  have hf : FiniteDualRestriction318.restriction into
      (IntegralNormalizationFiniteDual318.equivalence R a d hd z)=
      FiniteDualModuleAction318.frame P A (rawFrame R a d) c := by
    apply LinearMap.ext
    intro x
    obtain ⟨v,hv,he⟩ := (IntegralNormalizationConductorDual318.data R a d hd).value zJ (into x)
    have hv' : v=c*x := by
      apply IntegralNormalizationRawEmbedding318.inclusion_injective R a d hd
      rw [map_mul,hc']
      exact hv
    change (IntegralNormalizationConductorDual318.data R a d hd).equivalence zJ (into x)=
      (rawFrame R a d).coefficient (c*x)
    rw [he,hv']
    rfl
  have hcoord : coordinate R a d (IntegralNormalizationFiniteDual318.equivalence R a d hd z)=c := by
    apply (FiniteDualModuleAction318.frame P A (rawFrame R a d)).injective
    exact (FiniteDualRestriction318.frame_coordinate into (rawFrame R a d) _).trans hf
  rw [hcoord]
  exact hc'

include hd in
/-- The full normalization counit is injective. This uses the actual
ambient unit δ and the produced entire trace-dual equivalence, not a
rank argument or normal-order projectivity. -/
theorem coordinate_injective : Function.Injective (coordinate R a d) := by
  intro f g h
  let E := IntegralNormalizationFiniteDual318.equivalence R a d hd
  have he : (E.symm f).val=(E.symm g).val := by
    apply (IntegralFourRootNormalizationConductor318.different_isUnit R a d).mul_left_cancel
    have hf := coefficient_formula R a d hd (E.symm f)
    have hg := coefficient_formula R a d hd (E.symm g)
    rw [LinearEquiv.apply_symm_apply] at hf hg
    exact hf.symm.trans ((congrArg inc h).trans hg)
  have hs : E.symm f=E.symm g := Subtype.ext he
  exact E.symm.injective hs
end IntegralNormalizationCounit318
