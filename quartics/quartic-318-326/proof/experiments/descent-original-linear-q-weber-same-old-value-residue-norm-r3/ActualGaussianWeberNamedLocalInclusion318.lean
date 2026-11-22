module
public import ActualGaussianWeberActualLocalizedFrob318
public import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.Filtration
public section
noncomputable section

namespace ActualGaussianWeberNamedLocalInclusion318

open NumberField IntermediateField IsLocalRing IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open ActualGaussianWeberSelectedGaussianPrime318 ActualGaussianWeberChosenPlaceLift318
open ActualGaussianWeberIntegerModel318 ActualGaussianWeberCanonicalRingFrob318
open ActualGaussianWeberActualLocalizedFrob318

variable (L : Type*) [Field L] [NumberField L] [Algebra Base L]
variable (W : IntermediateField Base L) [NumberField W]
variable (v : HeightOneSpectrum (𝓞 W)) (w : HeightOneSpectrum (𝓞 L))

abbrev OldLocal := Localization.AtPrime v.asIdeal

/-- The actual integral inclusion of the specified subfield. -/
@[expose] def intInclusion : (𝓞 W)→+*(𝓞 L) :=
  RingOfIntegers.mapRingHom (algebraMap W L)

theorem intInclusion_eq_algebraMap : intInclusion L W=algebraMap (𝓞 W) (𝓞 L) := rfl

/-- Contraction along precisely the original inclusion, without
an abstract isomorphic copy of the old field. -/
abbrev SameContraction : Prop := w.asIdeal.comap (intInclusion L W)=v.asIdeal

theorem sameContraction_of_under (h : w.asIdeal.under (𝓞 W)=v.asIdeal) :
    SameContraction L W v w := h

@[expose] def integralAtActualPlace : (𝓞 W)→+*AtPlace L w :=
  (algebraMap (𝓞 L) (AtPlace L w)).comp (intInclusion L W)

theorem actual_denominator_unit (hwv : SameContraction L W v w) (s : v.asIdeal.primeCompl) :
    IsUnit (integralAtActualPlace L W w s) := by
  change IsUnit (algebraMap (𝓞 L) (AtPlace L w) (intInclusion L W s))
  apply (IsLocalization.AtPrime.isUnit_to_map_iff (AtPlace L w) w.asIdeal _).mpr
  apply Ideal.mem_primeCompl_iff.mpr
  intro h
  have h' : (s : 𝓞 W)∈w.asIdeal.comap (intInclusion L W) := h
  rw [hwv] at h'
  exact (Ideal.mem_primeCompl_iff.mp s.property) h'

/-- The canonical map from the stock localization at the named v
to the actual valuation subring at the named w. -/
@[expose] def actualLocalInclusion (hwv : SameContraction L W v w) :
    OldLocal L W v→+*AtPlace L w :=
  IsLocalization.lift (M:=v.asIdeal.primeCompl) (S:=OldLocal L W v)
    (g:=integralAtActualPlace L W w) (actual_denominator_unit L W v w hwv)

theorem actualLocalInclusion_integral (hwv : SameContraction L W v w) (x : 𝓞 W) :
    actualLocalInclusion L W v w hwv (algebraMap (𝓞 W) (OldLocal L W v) x)=
      integralAtActualPlace L W w x := by
  unfold actualLocalInclusion
  exact IsLocalization.lift_eq (M:=v.asIdeal.primeCompl)
    (actual_denominator_unit L W v w hwv) x

theorem old_denominator_unit (s : v.asIdeal.primeCompl) :
    IsUnit (algebraMap (𝓞 W) W (s:𝓞 W)) := by
  apply isUnit_iff_ne_zero.mpr
  intro h
  have h0 : (s:𝓞 W)=0 := RingOfIntegers.coe_injective (h.trans (map_zero (algebraMap (𝓞 W) W)).symm)
  exact (Ideal.mem_primeCompl_iff.mp s.property) (h0.symm ▸ v.asIdeal.zero_mem)

@[expose] def oldLocalToField : OldLocal L W v→+*W :=
  IsLocalization.lift (M:=v.asIdeal.primeCompl) (S:=OldLocal L W v)
    (g:=algebraMap (𝓞 W) W) (old_denominator_unit L W v)

theorem oldLocalToField_integral (x : 𝓞 W) :
    oldLocalToField L W v (algebraMap (𝓞 W) (OldLocal L W v) x)=algebraMap (𝓞 W) W x := by
  unfold oldLocalToField
  exact IsLocalization.lift_eq (M:=v.asIdeal.primeCompl) (old_denominator_unit L W v) x

/-- Both maps are compared as stock localization maps, after
restricting to the very same original ring of integers. -/
theorem actualLocalInclusion_field_triangle (hwv : SameContraction L W v w) :
    ((AtPlace L w).subtype).comp (actualLocalInclusion L W v w hwv)=
      (algebraMap W L).comp (oldLocalToField L W v) := by
  apply IsLocalization.ringHom_ext v.asIdeal.primeCompl
  apply RingHom.ext
  intro x
  change (AtPlace L w).subtype (actualLocalInclusion L W v w hwv
      (algebraMap (𝓞 W) (OldLocal L W v) x))=
    algebraMap W L (oldLocalToField L W v (algebraMap (𝓞 W) (OldLocal L W v) x))
  rw [actualLocalInclusion_integral,oldLocalToField_integral]
  change algebraMap (AtPlace L w) L (algebraMap (𝓞 L) (AtPlace L w) (intInclusion L W x))=
    algebraMap W L (algebraMap (𝓞 W) W x)
  rw [←IsScalarTower.algebraMap_apply (𝓞 L) (AtPlace L w) L]
  exact RingOfIntegers.mapRingHom_apply (algebraMap W L) x

theorem old_prime_maps_zero (hwv : SameContraction L W v w) (x : 𝓞 W)
    (hx : x∈v.asIdeal) : residue (AtPlace L w) (integralAtActualPlace L W w x)=0 := by
  apply (residue_eq_zero_iff _).mpr
  change algebraMap (𝓞 L) (AtPlace L w) (intInclusion L W x)∈maximalIdeal (AtPlace L w)
  apply (IsLocalization.AtPrime.to_map_mem_maximal_iff (AtPlace L w) w.asIdeal _).mpr
  change x∈w.asIdeal.comap (intInclusion L W)
  rw [hwv]
  exact hx

/-- The old residue field enters the actual residue field at w
through the same inclusion of integral representatives. -/
@[expose] def oldQuotientIntoActualResidue (hwv : SameContraction L W v w) :
    (𝓞 W ⧸ v.asIdeal)→+*ResidueField (AtPlace L w) :=
  Ideal.Quotient.lift v.asIdeal
    ((residue (AtPlace L w)).comp (integralAtActualPlace L W w))
    (old_prime_maps_zero L W v w hwv)

theorem oldQuotientIntoActualResidue_mk (hwv : SameContraction L W v w) (x : 𝓞 W) :
    oldQuotientIntoActualResidue L W v w hwv (Ideal.Quotient.mk v.asIdeal x)=
      residue (AtPlace L w) (integralAtActualPlace L W w x) := by
  unfold oldQuotientIntoActualResidue
  rw [Ideal.Quotient.lift_mk] <;> rfl

@[expose] def oldLocalResidue : OldLocal L W v→+*(𝓞 W ⧸ v.asIdeal) :=
  ((IsLocalization.AtPrime.equivQuotMaximalIdeal v.asIdeal (OldLocal L W v)).symm.toRingHom).comp
    (residue (OldLocal L W v))

theorem oldLocalResidue_integral (x : 𝓞 W) :
    oldLocalResidue L W v (algebraMap (𝓞 W) (OldLocal L W v) x)=Ideal.Quotient.mk v.asIdeal x := by
  let A := OldLocal L W v
  let E := IsLocalization.AtPrime.equivQuotMaximalIdeal v.asIdeal A
  change E.symm (Ideal.Quotient.mk (maximalIdeal A) (algebraMap (𝓞 W) A x))=
    Ideal.Quotient.mk v.asIdeal x
  have hE : E (Ideal.Quotient.mk v.asIdeal x)=
      Ideal.Quotient.mk (maximalIdeal A) (algebraMap (𝓞 W) A x) :=
    IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk v.asIdeal A x
  rw [←hE,AlgEquiv.symm_apply_apply]

/-- The exact commutative residue square. This is not just a
cardinality comparison of the two residue fields. -/
theorem actualLocalInclusion_residue_square (hwv : SameContraction L W v w) :
    (residue (AtPlace L w)).comp (actualLocalInclusion L W v w hwv)=
      (oldQuotientIntoActualResidue L W v w hwv).comp (oldLocalResidue L W v) := by
  apply IsLocalization.ringHom_ext v.asIdeal.primeCompl
  apply RingHom.ext
  intro x
  change residue (AtPlace L w) (actualLocalInclusion L W v w hwv
      (algebraMap (𝓞 W) (OldLocal L W v) x))=
    oldQuotientIntoActualResidue L W v w hwv
      (oldLocalResidue L W v (algebraMap (𝓞 W) (OldLocal L W v) x))
  rw [actualLocalInclusion_integral,oldLocalResidue_integral,oldQuotientIntoActualResidue_mk]

section Frobenius

variable [FiniteDimensional Base L] [IsGalois Base L]
variable {p : ℕ} [Fact p.Prime] (j : ZMod p) (hj : j^2= -1)
variable (hUnder : SignedAt L w j hj)

theorem actualLocalInclusion_residue_frobenius_fixed (hwv : SameContraction L W v w)
    (hSplit : ∀ x : 𝓞 W ⧸ v.asIdeal, x^p=x) (x : OldLocal L W v) :
    residue (AtPlace L w) (localFrob L w j hj hUnder
        (actualLocalInclusion L W v w hwv x))=
      residue (AtPlace L w) (actualLocalInclusion L W v w hwv x) := by
  let B := AtPlace L w
  let F := actualLocalInclusion L W v w hwv
  let e := oldQuotientIntoActualResidue L W v w hwv
  let u := oldLocalResidue L W v x
  have h : residue B (F x)=e u :=
    DFunLike.congr_fun (actualLocalInclusion_residue_square L W v w hwv) x
  change residue B (localFrob L w j hj hUnder (F x))=residue B (F x)
  rw [localFrob_residue_pow L w j hj hUnder (F x),h,←map_pow,hSplit u]

/-- Native uniqueness of two local maps with the same residue.
The only arithmetic geometric hypothesis beyond split residual
Frobenius is the literal unramifiedness at this same old prime. -/
theorem actualLocalFrob_fixes_old_local_image [Algebra.IsUnramifiedAt ℤ v.asIdeal]
    (hwv : SameContraction L W v w) (hSplit : ∀ x : 𝓞 W ⧸ v.asIdeal, x^p=x)
    (x : OldLocal L W v) :
    localFrob L w j hj hUnder (actualLocalInclusion L W v w hwv x)=
      actualLocalInclusion L W v w hwv x := by
  let A := OldLocal L W v
  let B := AtPlace L w
  let F : A→+*B := actualLocalInclusion L W v w hwv
  let f : A→ₐ[ℤ]B := {
    F with
    commutes' := fun n => by
      calc
        F (algebraMap ℤ A n) = F (n:A) := congrArg F (eq_intCast (algebraMap ℤ A) n)
        _ = (n:B) := map_intCast F n
        _ = algebraMap ℤ B n := (eq_intCast (algebraMap ℤ B) n).symm }
  let g : B→ₐ[ℤ]B := (localFrob L w j hj hUnder).toRingHom.toIntAlgHom
  have hf (a : A) : f a=F a := rfl
  have hg (b : B) : g b=localFrob L w j hj hUnder b := rfl
  letI : Algebra.FormallyUnramified ℤ A := inferInstanceAs
    (Algebra.IsUnramifiedAt ℤ v.asIdeal)
  have hMax : (maximalIdeal B : Ideal B)≠⊤ := Ideal.IsPrime.ne_top'
  have hEq : g.comp f=f := by
    apply Algebra.FormallyUnramified.ext_of_iInf (maximalIdeal B)
      (Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal B) hMax)
    intro a
    have h := actualLocalInclusion_residue_frobenius_fixed L W v w j hj hUnder hwv hSplit a
    change Ideal.Quotient.mk (maximalIdeal B) (localFrob L w j hj hUnder (F a))=
      Ideal.Quotient.mk (maximalIdeal B) (F a) at h
    rw [AlgHom.comp_apply,hf,hg]
    exact h
  have hx := AlgHom.congr_fun hEq x
  rw [AlgHom.comp_apply,hf,hg] at hx
  exact hx

end Frobenius

end ActualGaussianWeberNamedLocalInclusion318
