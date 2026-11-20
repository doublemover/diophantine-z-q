module
public import CTActualGlobalReciprocity318
import all CTActualGlobalReciprocity318
import all CTContinuousFieldHTwo318
import all CTFieldPrimitiveBoundary318
public section
noncomputable section

namespace CTActualCorrectedGlobalValue318

open CategoryTheory groupCohomology
open CTFieldPrimitiveRestriction318 CTContinuousFieldHTwo318 CTLocalInvariantDescent318
open CTActualGlobalReciprocity318
open scoped BigOperators

local instance (p : PrimePlace) : Fact p.val.Prime := ⟨p.property⟩
local instance (p : PrimePlace) : DecidableEq ℚ_[p.val] := Classical.decEq _
local instance : DecidableEq ℝ := Classical.decEq _

private def correctedAt (K : Type) [Field K] [CharZero K] [DecidableEq K] (f : ℚ →+* K)
    (e : CTFieldPrimitiveBoundary318.continuousTwo)
    (eta : (Fin 3 → Gal ℚ) → FieldUnitRep ℚ)
    (hPrim : inhomogeneousCochains.d (FieldUnitRep ℚ) 2 e.val=eta)
    (raw : (Fin 2 → Gal K) → FieldUnitRep K) (hC : IsLocallyConstant raw)
    (hRaw : inhomogeneousCochains.d (FieldUnitRep K) 2 raw=restrictCochain f 3 eta) :
    continuousCycles K :=
  ⟨raw-restrictCochain f 2 e.val,⟨by rw [map_sub,hRaw,restrict_d,hPrim,sub_self],
    (hC.prodMk (restrict_locallyConstant f 2 e.val e.property)).comp (fun z => z.1-z.2)⟩⟩

/-- Construct all real and p-adic continuous cycles from the literal
signed differentials and the same global primitive. -/
theorem corrected_actual_places
    (e : CTFieldPrimitiveBoundary318.continuousTwo)
    (eta : (Fin 3 → Gal ℚ) → FieldUnitRep ℚ)
    (hPrim : inhomogeneousCochains.d (FieldUnitRep ℚ) 2 e.val=eta)
    (raw : LocalRaw)
    (hLC : IsLocallyConstant raw.1 ∧ ∀ p, IsLocallyConstant (raw.2 p))
    (hRaw : inhomogeneousCochains.d (FieldUnitRep ℝ) 2 raw.1 =
        restrictCochain (algebraMap ℚ ℝ) 3 eta ∧
      ∀ p : PrimePlace, inhomogeneousCochains.d (FieldUnitRep ℚ_[p.val]) 2 (raw.2 p) =
        restrictCochain (algebraMap ℚ ℚ_[p.val]) 3 eta) :
    ∃ z : LocalCycles, CorrectedFromRaw raw e z := by
  refine ⟨⟨correctedAt ℝ (algebraMap ℚ ℝ) e eta hPrim raw.1 hLC.1 hRaw.1,
    fun p => correctedAt ℚ_[p.val] (algebraMap ℚ ℚ_[p.val])
      e eta hPrim (raw.2 p) (hLC.2 p) (hRaw.2 p)⟩,⟨rfl,fun _ => rfl⟩⟩

/-- A genuine boundary away from the finite exceptional p's
implies arithmetic invariant support, once actual local homs
are specified. The real class remains in the total. -/
theorem finite_corrected_total
    (I : LocalInvariants) (raw : LocalRaw) (e : CTFieldPrimitiveBoundary318.continuousTwo)
    (z : LocalCycles) (hz : CorrectedFromRaw raw e z)
    (S : Finset PrimePlace)
    (hAway : ∀ p : PrimePlace, p∉S →
      ∃ b : (Fin 1 → Gal ℚ_[p.val]) → FieldUnitRep ℚ_[p.val], IsLocallyConstant b ∧
        inhomogeneousCochains.d (FieldUnitRep ℚ_[p.val]) 1 b =
          raw.2 p-restrictCochain (algebraMap ℚ ℚ_[p.val]) 2 e.val) :
    ∃ h : FiniteProfile (localProfile I z),
      finiteTotal (localProfile I z) h =
        I.real (classOf ℝ z.1) + ∑ p ∈ S, I.finite p (classOf ℚ_[p.val] (z.2 p)) := by
  classical
  let T : Finset Place := insert none (S.image Option.some)
  have hSupp : SupportedOn (localProfile I z) T := by
    intro v h
    cases v with
    | none => exact (h (Finset.mem_insert_self _ _)).elim
    | some p =>
      have hp : p∉S := fun hx =>
        h (Finset.mem_insert_of_mem (Finset.mem_image_of_mem Option.some hx))
      obtain ⟨b,hb,he⟩ := hAway p hp
      have h0 : classOf ℚ_[p.val] (z.2 p)=0 :=
        (class_zero_iff ℚ_[p.val] (z.2 p)).2 ⟨⟨b,hb⟩,(hz.2 p).trans he.symm⟩
      change I.finite p (classOf ℚ_[p.val] (z.2 p))=0
      rw [h0,map_zero]
  let h : FiniteProfile (localProfile I z) := ⟨T,hSupp⟩
  refine ⟨h,(finiteTotal_on _ h T hSupp).trans ?_⟩
  have hNone : (none : Place) ∉ S.image Option.some := by simp
  change (∑ v ∈ insert none (S.image Option.some), localProfile I z v) = _
  rw [Finset.sum_insert hNone]
  have hImage : (∑ v ∈ S.image Option.some, localProfile I z v) =
      ∑ p ∈ S, localProfile I z (some p) :=
    Finset.sum_image (fun _ _ _ _ he => Option.some.inj he)
  rw [hImage] <;> rfl

/-- Arithmetic order-two target at the real place and full Q/Z
target at every p-adic place. This is an input interface for
actual Brauer theorems, not their construction. The type of the
p-adic isomorphism alone does not assert Frobenius normalization. -/
def RealInvariantTarget : AddSubgroup InvValues :=
  (nsmulAddMonoidHom InvValues (2 : ℕ)).ker

structure ArithmeticInvariantIsomorphisms where
  real : ContH2 ℝ ≃+ RealInvariantTarget
  finite : (p : PrimePlace) → ContH2 ℚ_[p.val] ≃+ InvValues

def ArithmeticInvariantIsomorphisms.toLocalInvariants
    (I : ArithmeticInvariantIsomorphisms) : LocalInvariants :=
  ⟨RealInvariantTarget.subtype.comp I.real.toAddMonoidHom,
    fun p => (I.finite p).toAddMonoidHom⟩

/-- The exact pointwise global arithmetic pairing VALUE for a
supplied signed cochain representative, prior to choice and
bilinearity descent on Sha. The supplied local isomorphisms
require independent arithmetic normalization. -/
theorem actual_global_pair_value
    (I : ArithmeticInvariantIsomorphisms)
    (e : CTFieldPrimitiveBoundary318.continuousTwo)
    (eta : (Fin 3 → Gal ℚ) → FieldUnitRep ℚ)
    (hPrim : inhomogeneousCochains.d (FieldUnitRep ℚ) 2 e.val=eta)
    (raw : LocalRaw)
    (hLC : IsLocallyConstant raw.1 ∧ ∀ p, IsLocallyConstant (raw.2 p))
    (hRaw : inhomogeneousCochains.d (FieldUnitRep ℝ) 2 raw.1 =
        restrictCochain (algebraMap ℚ ℝ) 3 eta ∧
      ∀ p : PrimePlace, inhomogeneousCochains.d (FieldUnitRep ℚ_[p.val]) 2 (raw.2 p) =
        restrictCochain (algebraMap ℚ ℚ_[p.val]) 3 eta)
    (S : Finset PrimePlace)
    (hAway : ∀ p : PrimePlace, p∉S →
      ∃ b : (Fin 1 → Gal ℚ_[p.val]) → FieldUnitRep ℚ_[p.val], IsLocallyConstant b ∧
        inhomogeneousCochains.d (FieldUnitRep ℚ_[p.val]) 1 b =
          raw.2 p-restrictCochain (algebraMap ℚ ℚ_[p.val]) 2 e.val) :
    ∃ z : LocalCycles, CorrectedFromRaw raw e z ∧
      ∃ h : FiniteProfile (localProfile I.toLocalInvariants z),
        finiteTotal (localProfile I.toLocalInvariants z) h =
          (I.real (classOf ℝ z.1)).val + ∑ p ∈ S, I.finite p (classOf ℚ_[p.val] (z.2 p)) := by
  obtain ⟨z,hz⟩ := corrected_actual_places e eta hPrim raw hLC hRaw
  exact ⟨z,hz,finite_corrected_total I.toLocalInvariants raw e z hz S hAway⟩

/-- If reciprocity is supplied for the specified arithmetic maps, every
other primitive of the same global defect gives the same total on the
same raw cups. No finite-support input for the second correction. -/
theorem actual_global_pair_value_change_primitive
    (I : ArithmeticInvariantIsomorphisms)
    (hR : BrauerReciprocity I.toLocalInvariants)
    (e e' : CTFieldPrimitiveBoundary318.continuousTwo)
    (eta : (Fin 3 → Gal ℚ) → FieldUnitRep ℚ)
    (hPrim : inhomogeneousCochains.d (FieldUnitRep ℚ) 2 e.val=eta)
    (hPrim' : inhomogeneousCochains.d (FieldUnitRep ℚ) 2 e'.val=eta)
    (raw : LocalRaw) (z : LocalCycles) (hz : CorrectedFromRaw raw e z)
    (hFin : FiniteProfile (localProfile I.toLocalInvariants z)) :
    ∃ z' : LocalCycles, CorrectedFromRaw raw e' z' ∧
      ∃ h' : FiniteProfile (localProfile I.toLocalInvariants z'),
        finiteTotal (localProfile I.toLocalInvariants z') h' =
          finiteTotal (localProfile I.toLocalInvariants z) hFin :=
  corrected_total_change_primitive I.toLocalInvariants hR raw e e'
    (hPrim'.trans hPrim.symm) z hz hFin

end CTActualCorrectedGlobalValue318
