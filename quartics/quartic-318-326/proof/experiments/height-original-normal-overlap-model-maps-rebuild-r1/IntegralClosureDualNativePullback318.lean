module
public import IntegralClosureNativeDualLocalization318
public import NativeTildeLocalizedModule318
public import Mathlib.AlgebraicGeometry.OpenImmersion
public section
noncomputable section
namespace IntegralClosureDualNativePullback318
open AlgebraicGeometry CategoryTheory
universe u
variable {P Q B : Type u} [CommRing P] [CommRing Q] [CommRing B]
  [Algebra P Q] [Algebra P B] [Algebra Q B] [IsScalarTower P Q B]
  (s : P) [IsLocalization.Away s Q]
local notation "N" => integralClosure P B
local notation "O" => integralClosure Q B
local notation "i" => IntegralClosureLocalizationMap318.inclusion (P:=P) (Q:=Q) (B:=B)
local notation "φ" => CommRingCat.ofHom i.toRingHom
local notation "D" => ModuleCat.of N (FiniteDualModuleAction318.Dual P N)
local notation "L" => ModuleCat.of O (FiniteDualModuleAction318.Dual Q O)

/-- Full native pullback of the OLD normal-order dual sheaf along the
actual normal-order inclusion. The target is the entire Q-valued dual. -/
@[expose] def iso [Module.FinitePresentation P N] :
    (Scheme.Modules.pullback (Spec.map φ)).obj (tilde D) ≅ tilde L :=
  NativeTildeLocalizedModule318.pullbackIso φ D L
    (IntegralClosureNativeDualLocalization318.moduleIso (Q:=Q) (B:=B) s)

lemma hom_formula [Module.FinitePresentation P N] :
    (iso (Q:=Q) (B:=B) s).hom=
      (TildePullback318.pullbackIso φ).hom.app D ≫
      (tilde.functor (CommRingCat.of O)).map
        (IntegralClosureNativeDualLocalization318.moduleIso (Q:=Q) (B:=B) s).hom := rfl
include s in
lemma isOpen : IsOpenImmersion (Spec.map φ) := by
  letI : Algebra N O := IntegralClosureLocalizationMap318.normalAlgebra
  letI := IntegralClosurePrincipalLocalization318.localization (Q:=Q) (B:=B) s
  exact IsOpenImmersion.of_isLocalization (S:=O) (algebraMap P N s)

/-- Genuine open restriction, with open immersion PRODUCED from the
whole integral-closure localization, not provided as a new hypothesis. -/
@[expose] def restrictionIso [Module.FinitePresentation P N] :
    letI : IsOpenImmersion (Spec.map φ) := isOpen (Q:=Q) (B:=B) s
    (Scheme.Modules.restrictFunctor (Spec.map φ)).obj (tilde D) ≅ tilde L := by
  letI : IsOpenImmersion (Spec.map φ) := isOpen (Q:=Q) (B:=B) s
  exact NativeTildeLocalizedModule318.restrictionIso φ D L
    (IntegralClosureNativeDualLocalization318.moduleIso (Q:=Q) (B:=B) s)
end IntegralClosureDualNativePullback318
