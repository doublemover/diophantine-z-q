module
public import OriginalBranchCechCalculus318
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public section
noncomputable section
namespace OriginalBranchPlaneLocal318
open MvPolynomial
variable {k : Type*} [Field k]
abbrev Plane := MvPolynomial (Fin 2) k
abbrev A (I : Ideal (Plane (k:=k))) := Plane (k:=k) ⧸ I
@[expose] def gen (I : Ideal (Plane (k:=k))) (i : Fin 2) : A I := Ideal.Quotient.mk I (X i)
@[expose] def co (I : Ideal (Plane (k:=k))) (a : k) : A I := algebraMap k (A I) a
/-- The rational point of any represented plane curve at (α,0) has precisely
the two expected coordinate generators; no regularity premise. -/
theorem point_ker (I : Ideal (Plane (k:=k))) (φ : A I→ₐ[k]k) (α : k)
    (hx : φ (gen I 0)=α) (hy : φ (gen I 1)=0) :
    RingHom.ker φ.toRingHom=Ideal.span ({gen I 0-co I α,gen I 1}:Set (A I)) := by
  let m:=Ideal.span ({gen I 0-co I α,gen I 1}:Set (A I))
  let π:=Ideal.Quotient.mkₐ k m
  have he₁ : π (gen I 0) = π (co I α) := by
    apply sub_eq_zero.mp
    rw [←map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have he₂ : π (gen I 1)=0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hh : π.comp ((Algebra.ofId k (A I)).comp φ) = π := by
    apply Ideal.Quotient.algHom_ext k
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · change π (co I (φ (gen I 0))) = π (gen I 0)
      rw [hx,he₁]
    · change π (co I (φ (gen I 1))) = π (gen I 1)
      rw [hy,he₂]; simp [co]
  apply le_antisymm
  · intro a ha
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change π a=0
    rw [←hh]
    change π (co I (φ a))=0
    rw [show φ a=0 from ha]; simp [co]
  · apply Ideal.span_le.mpr
    intro u hu
    rcases hu with rfl | h
    · change φ (gen I 0-co I α)=0
      rw [map_sub,hx]; exact sub_eq_zero.mpr (φ.commutes α).symm
    · exact (Set.mem_singleton_iff.mp h) ▸ hy

abbrev pointPrime (I : Ideal (Plane (k:=k))) (φ : A I→ₐ[k]k) := RingHom.ker φ.toRingHom
instance pointPrime_isPrime (I : Ideal (Plane (k:=k))) (φ : A I→ₐ[k]k) :
    (pointPrime I φ).IsPrime := RingHom.ker_isPrime _

/-- At a genuine simple root, y itself generates the maximal ideal of the actual
localized plane-coordinate ring. No square root of the branch unit is adjoined. -/
theorem uniformizer (I : Ideal (Plane (k:=k))) (φ : A I→ₐ[k]k) (α : k) (F : Polynomial k)
    (hx : φ (gen I 0)=α) (hy : φ (gen I 1)=0)
    (hF : (gen I 1)^2=Polynomial.aeval (gen I 0) F) (hz : F.eval α=0)
    (hn : F.derivative.eval α≠0) :
    IsLocalRing.maximalIdeal (Localization.AtPrime (pointPrime I φ))=
      Ideal.span ({algebraMap (A I) (Localization.AtPrime (pointPrime I φ)) (gen I 1)}:Set (Localization.AtPrime (pointPrime I φ))) := by
  let S:=Localization.AtPrime (pointPrime I φ)
  let ι:=algebraMap (A I) S
  obtain ⟨g,hg⟩:=Polynomial.dvd_iff_isRoot.mpr hz
  have eg : g.eval α=F.derivative.eval α := by rw [hg,Polynomial.derivative_mul]; simp
  have hi : IsUnit (ι (Polynomial.aeval (gen I 0) g)) := by
    apply (IsLocalization.AtPrime.isUnit_to_map_iff S (pointPrime I φ) _).mpr
    change φ (Polynomial.aeval (gen I 0) g)≠0
    rw [←Polynomial.aeval_algHom_apply,hx,Polynomial.aeval_def,Algebra.algebraMap_self,Polynomial.eval₂_id,eg]
    exact hn
  have r : ι (gen I 1)^2=ι (gen I 0-co I α)*ι (Polynomial.aeval (gen I 0) g) := by
    rw [←map_pow,hF,hg,map_mul]
    simp [co]
  change IsLocalRing.maximalIdeal S=_
  rw [←IsLocalization.AtPrime.map_eq_maximalIdeal (pointPrime I φ) S]
  change Ideal.map ι (RingHom.ker φ.toRingHom)=_
  rw [point_ker I φ α hx hy,Ideal.map_span,Set.image_pair]
  exact OriginalBranchCechCalculus318.branch_parameter (A:=S) (ι (gen I 0-co I α)) (ι (gen I 1)) (ι (Polynomial.aeval (gen I 0) g)) r hi
end OriginalBranchPlaneLocal318
#print axioms OriginalBranchPlaneLocal318.uniformizer
