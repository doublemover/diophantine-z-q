module
public import ActualSelectedIndexedFrickeTrace318
public import ActualCMLatticeDualOrientation318
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Normal.Basic
import all ActualTwoDescentEllipticModel318
import all ActualTwoDescentGaloisPointAction318
public section
noncomputable section

namespace ActualSelectedArtinOrbit318
open ActualTwoDescentEllipticModel318 ActualTwoDescentAlgebraicClosureHalving318
open ActualTwoDescentGaloisPointAction318 ActualTwoDescentGaloisFixedRational318
open ActualSelectedIndexedFrickeTrace318

local instance : DecidableEq Qbar := Classical.decEq _

abbrev baseObject (κ : Qbar) : IntermediateField ℚ Qbar :=
  IntermediateField.adjoin ℚ ({κ} : Set Qbar)

abbrev FixingBase (κ : Qbar) := ↥((baseObject κ).fixingSubgroup)

abbrev toGalQ {κ : Qbar} (g : FixingBase κ) : GalQ := g.val

/-- The given square root chooses the actual fixing subgroup of Qbar/Q. -/
theorem fixes_generator_iff (κ : Qbar) (σ : GalQ) :
    σ ∈ (baseObject κ).fixingSubgroup ↔ σ κ = κ := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h
    exact h κ (IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton κ))
  · intro h x hx
    refine IntermediateField.adjoin_induction ℚ (motive := fun z _ => σ z = z) ?_ ?_ ?_ ?_ ?_ hx
    · intro z hz
      exact (Set.mem_singleton_iff.mp hz).symm ▸ h
    · intro z
      exact σ.commutes z
    · intro a b _ _ ha hb
      rw [map_add, ha, hb]
    · intro a _ ha
      rw [map_inv₀, ha]
    · intro a b _ _ ha hb
      rw [map_mul, ha, hb]

section NormalField

variable (κ : Qbar) (H : IntermediateField (BaseField κ) Qbar)
variable [Normal (BaseField κ) H]

/-- Literal restriction to the same embedded normal H over the same K. -/
@[expose] def restriction : FixingBase κ →* (H ≃ₐ[BaseField κ] H) :=
  ((AlgEquiv.restrictNormalHom H) :
      (Qbar ≃ₐ[BaseField κ] Qbar) →* (H ≃ₐ[BaseField κ] H)).comp
    (baseObject κ).fixingSubgroupEquiv.toMonoidHom

theorem restriction_surjective : Function.Surjective (restriction κ H) := by
  letI : IsAlgClosure (BaseField κ) Qbar :=
    ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) (BaseField κ)⟩
  have h : Function.Surjective
      (((AlgEquiv.restrictNormalHom H) :
        (Qbar ≃ₐ[BaseField κ] Qbar) →* (H ≃ₐ[BaseField κ] H))) :=
    AlgEquiv.restrictNormalHom_surjective H
  exact h.comp (baseObject κ).fixingSubgroupEquiv.surjective

lemma restriction_coordinate (g : FixingBase κ) (x : H) :
    ((restriction κ H g) x : Qbar) = toGalQ g (x : Qbar) :=
  AlgEquiv.restrictNormalHom_apply H ((baseObject κ).fixingSubgroupEquiv g) x

/-- This is an exact point predicate, using both coordinates in the actual H. -/
@[expose] def definedOver (n : ℚ) : Point (algebraMap ℚ Qbar n) → Prop
  | .zero => True
  | .some x y _ => x ∈ H ∧ y ∈ H

theorem kernel_fixes_defined_point (n : ℚ) (hn : n ≠ 0)
    (P : Point (algebraMap ℚ Qbar n)) (hP : definedOver κ H n P)
    (g : FixingBase κ) (hg : restriction κ H g = 1) :
    galoisPointHom (toGalQ g) n hn P = P := by
  have hcoord (x : Qbar) (hx : x ∈ H) : toGalQ g x = x := by
    calc
      _ = ((restriction κ H g) ⟨x, hx⟩ : Qbar) :=
        (restriction_coordinate κ H g ⟨x, hx⟩).symm
      _ = x := congrArg (fun f : H ≃ₐ[BaseField κ] H => (f ⟨x, hx⟩ : Qbar)) hg
  cases P with
  | zero => rfl
  | some x y h =>
    change x ∈ H ∧ y ∈ H at hP
    simp only [galoisPointHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      galoisPoint, point, hcoord x hP.1, hcoord y hP.2]

/-- Evaluation of the same H-point is independent of which absolute lift
of its finite automorphism was chosen. -/
theorem action_eq_of_restriction_eq (n : ℚ) (hn : n ≠ 0)
    (P : Point (algebraMap ℚ Qbar n)) (hP : definedOver κ H n P)
    (g h : FixingBase κ) (he : restriction κ H g = restriction κ H h) :
    galoisPointHom (toGalQ g) n hn P = galoisPointHom (toGalQ h) n hn P := by
  have hker : restriction κ H (h⁻¹ * g) = 1 := by
    rw [map_mul, map_inv, he, inv_mul_cancel]
  have hk := kernel_fixes_defined_point κ H n hn P hP (h⁻¹ * g) hker
  calc
    _ = galoisPointHom (toGalQ (h * (h⁻¹ * g))) n hn P := by
      rw [← mul_assoc, mul_inv_cancel, one_mul]
    _ = galoisPointHom (toGalQ h) n hn
          (galoisPointHom (toGalQ (h⁻¹ * g)) n hn P) :=
      actual_galois_mul (toGalQ h) (toGalQ (h⁻¹ * g)) n hn P
    _ = _ := by rw [hk]

variable (artin : Index κ ≃* (H ≃ₐ[BaseField κ] H))

@[expose] def liftClass (A : Index κ) : FixingBase κ :=
  Classical.choose (restriction_surjective κ H (artin A))

lemma restrict_liftClass (A : Index κ) :
    restriction κ H (liftClass κ H artin A) = artin A :=
  Classical.choose_spec (restriction_surjective κ H (artin A))

/-- The entire orbit is produced from the one actual geometric base point,
not supplied as a collection of unrelated witnesses. -/
@[expose] def orbitPoint (n : ℚ) (hn : n ≠ 0)
    (P : Point (algebraMap ℚ Qbar n)) (A : Index κ) : Point (algebraMap ℚ Qbar n) :=
  galoisPointHom (toGalQ (liftClass κ H artin A)) n hn P

theorem orbit_one (n : ℚ) (hn : n ≠ 0)
    (P : Point (algebraMap ℚ Qbar n)) (hP : definedOver κ H n P) :
    orbitPoint κ H artin n hn P 1 = P := by
  unfold orbitPoint
  exact kernel_fixes_defined_point κ H n hn P hP (liftClass κ H artin 1) (by
    rw [restrict_liftClass, map_one])

/-- The same-orientation translation follows from the actual restriction
and Artin map, with commutativity used only on the actual ideal classes. -/
theorem acts_on_orbit (n : ℚ) (hn : n ≠ 0)
    (P : Point (algebraMap ℚ Qbar n)) (hP : definedOver κ H n P)
    (g : FixingBase κ) (A : Index κ) :
    galoisPointHom (toGalQ g) n hn (orbitPoint κ H artin n hn P A) =
      orbitPoint κ H artin n hn P (A * artin.symm (restriction κ H g)) := by
  let u := artin.symm (restriction κ H g)
  have hu : artin u = restriction κ H g := artin.apply_symm_apply _
  have he :
      restriction κ H (g * liftClass κ H artin A) =
        restriction κ H (liftClass κ H artin (A * u)) := by
    calc
      _ = restriction κ H g * artin A := by rw [map_mul, restrict_liftClass]
      _ = artin (u * A) := by rw [map_mul, hu]
      _ = _ := by rw [mul_comm u A, restrict_liftClass]
  unfold orbitPoint
  rw [← actual_galois_mul]
  exact action_eq_of_restriction_eq κ H n hn P hP
    (g * liftClass κ H artin A) (liftClass κ H artin (A * u)) he

end NormalField

lemma inverse_reversing_generator (κ : Qbar) (c : GalQ) (hc : c κ = -κ) :
    c⁻¹ κ = -κ := by
  have h : c (-κ) = κ := by rw [map_neg, hc, neg_neg]
  change c.symm κ = -κ
  calc
    _ = c.symm (c (-κ)) := congrArg (fun y : Qbar => c.symm y) h.symm
    _ = _ := AlgEquiv.symm_apply_apply c (-κ)

/-- The conjugated lift is still a lift over K, inferred from its action on
the same defining square root. -/
def conjugateFixing (κ : Qbar) (c : GalQ) (hc : c κ = -κ)
    (g : FixingBase κ) : FixingBase κ := by
  refine ⟨c * toGalQ g * c⁻¹, (fixes_generator_iff κ _).mpr ?_⟩
  have hg := (fixes_generator_iff κ (toGalQ g)).mp g.property
  change c (toGalQ g (c⁻¹ κ)) = κ
  rw [inverse_reversing_generator κ c hc, map_neg, hg, map_neg, hc, neg_neg]

section Reversal

variable (κ : Qbar) (H : IntermediateField (BaseField κ) Qbar)
variable [Normal (BaseField κ) H]
variable (artin : Index κ ≃* (H ≃ₐ[BaseField κ] H))
variable (n : ℚ) (hn : n ≠ 0)
variable (P : Point (algebraMap ℚ Qbar n)) (hP : definedOver κ H n P)
variable (c : GalQ) (hc : c κ = -κ)
variable (T : Point n)
variable (𝔫 : ActualCMLatticeDualOrientation318.FractionalUnit (BaseField κ))

abbrev normClass : Index κ := ClassGroup.mk (BaseField κ) 𝔫

include hP

/-- From the actual finite Artin conjugation rule and just the principal
class pointwise Fricke identity, derive the entire reversed orbit. The
Artin isomorphism and its arithmetic conjugation comparison remain inputs. -/
theorem conjugation_on_orbit
    (hInv : ∀ g : FixingBase κ,
      restriction κ H (conjugateFixing κ c hc g) = (restriction κ H g)⁻¹)
    (hBase : galoisPointHom c n hn P =
      orbitPoint κ H artin n hn P (normClass κ 𝔫) + rationalPointMap n hn T)
    (A : Index κ) :
    galoisPointHom c n hn (orbitPoint κ H artin n hn P A) =
      orbitPoint κ H artin n hn P (A⁻¹ * normClass κ 𝔫) + rationalPointMap n hn T := by
  let g := liftClass κ H artin A
  let τ := conjugateFixing κ c hc g
  have hprod : c * toGalQ g = toGalQ τ * c := by
    change c * toGalQ g = (c * toGalQ g * c⁻¹) * c
    rw [mul_assoc (c * toGalQ g), inv_mul_cancel, mul_one]
  have hu : artin.symm (restriction κ H τ) = A⁻¹ := by
    change artin.symm (restriction κ H (conjugateFixing κ c hc (liftClass κ H artin A))) = A⁻¹
    rw [hInv, restrict_liftClass, map_inv, artin.symm_apply_apply]
  change galoisPointHom c n hn (galoisPointHom (toGalQ g) n hn P) = _
  rw [← actual_galois_mul, hprod, actual_galois_mul, hBase, map_add,
    acts_on_orbit κ H artin n hn P hP τ, actual_rational_point_fixed, hu,
    mul_comm (normClass κ 𝔫) A⁻¹]

/-- Supply the already-occurring indexed action, with no independent class
point family and no supplied equation for the sum. -/
def indexedActionOfArtin
    (hInv : ∀ g : FixingBase κ,
      restriction κ H (conjugateFixing κ c hc g) = (restriction κ H g)⁻¹)
    (hBase : galoisPointHom c n hn P =
      orbitPoint κ H artin n hn P (normClass κ 𝔫) + rationalPointMap n hn T) :
    IndexedAction κ n hn where
  point := orbitPoint κ H artin n hn P
  cusp := T
  fixedOrientation σ hσ := by
    let g : FixingBase κ := ⟨σ, (fixes_generator_iff κ σ).mpr hσ⟩
    exact ⟨artin.symm (restriction κ H g), acts_on_orbit κ H artin n hn P hP g⟩
  conjugation := c
  conjugationSign := hc
  reversedShift := normClass κ 𝔫
  reversedOrientation := conjugation_on_orbit κ H artin n hn P hP c hc T 𝔫 hInv hBase

/-- Transport the exact indexed trace to the original even multiplier.
The one rational Fricke cusp is the same T used in the principal relation. -/
theorem orbitTrace_killed_by_old_even
    (hInv : ∀ g : FixingBase κ,
      restriction κ H (conjugateFixing κ c hc g) = (restriction κ H g)⁻¹)
    (hBase : galoisPointHom c n hn P =
      orbitPoint κ H artin n hn P (normClass κ 𝔫) + rationalPointMap n hn T)
    (d : ℚ) (hκ : κ ^ 2 = algebraMap ℚ Qbar d)
    (L : ℕ) (hL : 2 ∣ L) (hT : (2 : ℕ) • T = 0) :
    ∀ σ : GalQ, L •
      (galoisPointHom σ n hn (trace κ n (orbitPoint κ H artin n hn P)) -
        trace κ n (orbitPoint κ H artin n hn P)) = 0 := by
  let D := indexedActionOfArtin κ H artin n hn P hP c hc T 𝔫 hInv hBase
  have ht : L • D.cusp = 0 := by
    change L • T = 0
    obtain ⟨k, hk⟩ := hL
    rw [hk, Nat.mul_comm 2 k, mul_nsmul, hT, nsmul_zero]
  exact trace_killed_translates d κ hκ n hn D L ht

end Reversal
end ActualSelectedArtinOrbit318
