module
public import SelectedHorizontalResidueTrace318
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public section
noncomputable section

open SelectedHorizontalResidueTrace318

namespace SelectedHorizontalResidueCRT318

variable {k C : Type*} [Field k] [CharZero k] [CommRing C] [Algebra k C]
variable [FiniteDimensional k C]

attribute [local instance] Ideal.Quotient.field

/-- In the genuine finite residue algebra, an element nonzero at one
maximal ideal has a multiple with nonzero trace. Use the actual CRT
to multiply to 1 at that maximal ideal and 0 at the rest. Nilpotents
in the special fiber are retained, so no étaleness is assumed. -/
theorem exists_multiple_trace_ne_zero (P : MaximalSpectrum C) (a : C)
    (ha : a ∉ P.asIdeal) : ∃ t : C, Algebra.trace k C (t*a) ≠ 0 := by
  classical
  letI : IsArtinianRing C := IsArtinianRing.of_finite k C
  let f : (Q : MaximalSpectrum C) → C ⧸ Q.asIdeal :=
    fun Q => if Q=P then (Ideal.Quotient.mk Q.asIdeal a)⁻¹ else 0
  have hc : Pairwise (Function.onFun IsCoprime (fun Q : MaximalSpectrum C => Q.asIdeal)) := by
    intro Q Q' hQ
    exact Ideal.isCoprime_iff_sup_eq.mpr
      (Q.isMaximal.coprime_of_ne Q'.isMaximal (fun h => hQ (MaximalSpectrum.ext h)))
  obtain ⟨t,ht⟩ := Ideal.pi_quotient_surjective hc f
  have hP : Ideal.Quotient.mk P.asIdeal (t*a)=1 := by
    rw [map_mul,ht P]
    simp only [f,if_pos rfl]
    exact inv_mul_cancel₀ (fun hz => ha (Ideal.Quotient.eq_zero_iff_mem.mp hz))
  have hQ (Q : MaximalSpectrum C) (h : Q≠P) :
      Ideal.Quotient.mk Q.asIdeal (t*a)=0 := by
    rw [map_mul,ht Q]
    simp only [f,if_neg h,zero_mul]
  have hn : ¬IsNilpotent (t*a) := by
    intro h
    have hh := h.map (Ideal.Quotient.mk P.asIdeal)
    rw [hP] at hh
    exact not_isNilpotent_one hh
  have hd : IsNilpotent ((t*a)*(1-t*a)) := by
    apply nilpotent_deviation_of_residues
    intro I hI
    by_cases he : I=P.asIdeal
    · subst I
      right
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_sub,map_one,hP,sub_self]
    · letI : I.IsPrime := hI
      let Q : MaximalSpectrum C := ⟨I,IsArtinianRing.isMaximal_of_isPrime I⟩
      have h : Q≠P := fun hp => he (congrArg MaximalSpectrum.asIdeal hp)
      exact Or.inl (Ideal.Quotient.eq_zero_iff_mem.mp (hQ Q h))
  exact ⟨t,trace_ne_zero (t*a) hd hn⟩

end SelectedHorizontalResidueCRT318

#print axioms SelectedHorizontalResidueCRT318.exists_multiple_trace_ne_zero
