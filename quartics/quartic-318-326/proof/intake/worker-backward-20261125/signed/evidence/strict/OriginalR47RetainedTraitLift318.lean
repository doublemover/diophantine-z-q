module
public import OriginalR47TraitRoundKernel318
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public section
noncomputable section

namespace OriginalR47RetainedTraitLift318

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open OriginalR47TraitRoundKernel318 (base trait brace)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {R : Type u} [CommRing R]

abbrev eta : Spec (CommRingCat.of (FractionRing R)) ⟶ base (R:=R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))

section Domain
variable [IsDomain R] (v : Ideal R) [v.IsPrime]

abbrev etaAt : Spec (CommRingCat.of (FractionRing R)) ⟶ trait v :=
  Spec.map (CommRingCat.ofHom (algebraMap (Localization.AtPrime v) (FractionRing R)))

theorem etaAt_read : etaAt v ≫ brace v = eta (R:=R) := by
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact (IsScalarTower.algebraMap_apply R (Localization.AtPrime v) (FractionRing R) x).symm

end Domain

variable (v : Ideal R) [v.IsPrime]
variable {X Y U : Scheme.{u}} (r : Y ⟶ X)
variable (s : U ⟶ X)
variable (P : base (R:=R) ⟶ X)

/-- Obtain the true generic lift of the retained section from the exact
unchanged open of the round; this does not assume that any closed value
of P avoids a thick node. -/
theorem generic (a : U ⟶ Y) (h : IsPullback a (𝟙 U) r s)
    [IsOpenImmersion s]
    (hP : Set.range (eta (R:=R) ≫ P) ⊆ Set.range s) :
    ∃ Pη : Spec (CommRingCat.of (FractionRing R)) ⟶ Y,
      Pη ≫ r = eta (R:=R) ≫ P := by
  let u := IsOpenImmersion.lift s (eta (R:=R) ≫ P) hP
  refine ⟨u ≫ a,?_⟩
  rw [Category.assoc,h.w,Category.id_comp]
  exact IsOpenImmersion.lift_fac _ _ _

/-- The actual new proper round has a unique lift over each original
arithmetic local trait, with the same generic Pη and same base
fraction field. Both structural arrows are fixed, not just its point. -/
theorem «local» [IsDedekindDomain R] [IsProper r] (hv : v ≠ ⊥)
    (Pη : Spec (CommRingCat.of (FractionRing R)) ⟶ Y)
    (hPη : Pη ≫ r = eta (R:=R) ≫ P) :
    ∃! Q : trait v ⟶ Y,
      etaAt v ≫ Q = Pη ∧ Q ≫ r = brace v ≫ P := by
  let : IsDiscreteValuationRing (Localization.AtPrime v) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hv _
  let V : ValuativeCommSq r :=
    { R := Localization.AtPrime v
      K := FractionRing R
      i₁ := Pη
      i₂ := brace v ≫ P
      commSq := ⟨by rw [hPη, ← Category.assoc, etaAt_read]⟩ }
  have HP : IsProper r := inferInstance
  rw [IsProper.eq_valuativeCriterion] at HP
  have H : ValuativeCriterion r := HP.1.1.1
  obtain ⟨L⟩ := H V
  refine ⟨L.default.l, ⟨L.default.fac_left,L.default.fac_right⟩,?_⟩
  intro Q hQ
  let b : V.commSq.LiftStruct := ⟨Q,hQ.1,hQ.2⟩
  exact congrArg CommSq.LiftStruct.l (L.uniq b)

end OriginalR47RetainedTraitLift318

#print axioms OriginalR47RetainedTraitLift318.etaAt_read
#print axioms OriginalR47RetainedTraitLift318.generic
#print axioms OriginalR47RetainedTraitLift318.local
