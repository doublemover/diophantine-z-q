module
public import SelectedHorizontalResidueCRT318
public import SelectedDedekindFractionWitness318
public import SelectedTraceDualNormalization318
public import Mathlib.RingTheory.Trace.Quotient
public import Mathlib.RingTheory.Ideal.GoingUp
public section
noncomputable section

open SelectedTraceDualNormalization318 SelectedHorizontalResidueCRT318
open SelectedDedekindFractionWitness318

namespace SelectedHorizontalNormalDual318

variable {R K F : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable [Field F] [Algebra K F] [Algebra R F] [IsScalarTower R K F]
variable [FiniteDimensional K F] [Algebra.IsSeparable K F]
variable [CharZero (IsLocalRing.ResidueField R)]

/-- At the genuine horizontal normal chart, the uniformizer of the
base clears the normal trace dual. In fact any element of the base
maximal ideal clears it. Nilpotents in the residue algebra are
retained and char zero is used only by the trace obstruction. No
specific ramification index, completed branch, or Galois extension. -/
theorem clears_of_residueCharZero (π : R) (hπ : π ∈ IsLocalRing.maximalIdeal R)
    (x : F) (hx : x ∈ complementary K (integralClosure R F)) :
    algebraMap R F π*x ∈ integralClosure R F := by
  classical
  let B := ↥(integralClosure R F)
  let m := IsLocalRing.maximalIdeal R
  let J : Ideal B := m.map (algebraMap R B)
  let k := R ⧸ m
  let C := B ⧸ J
  letI : Field k := inferInstanceAs (Field (IsLocalRing.ResidueField R))
  letI : CharZero k := inferInstanceAs (CharZero (IsLocalRing.ResidueField R))
  letI : IsDedekindDomain R :=
    ((IsDiscreteValuationRing.TFAE R (IsDiscreteValuationRing.not_isField R)).out 1 3).mp
      (inferInstance : IsDiscreteValuationRing R)
  letI : IsDedekindDomain B := integralClosure.isDedekindDomain R K F
  letI : IsFractionRing B F := integralClosure.isFractionRing_of_finite_extension (A:=R) K F
  letI : Module.Finite R B := IsIntegralClosure.finite R K F B
  letI : Module.IsTorsionFree R F := .trans_faithfulSMul R K F
  letI : Module.IsTorsionFree R B := IsIntegralClosure.isTorsionFree R F
  letI : Algebra.IsIntegral R B := IsIntegralClosure.isIntegral_algebra R F
  letI : Algebra k C := inferInstanceAs (Algebra (R ⧸ m) (B ⧸ m.map (algebraMap R B)))
  letI : IsScalarTower R k C := inferInstanceAs
    (IsScalarTower R (R ⧸ m) (B ⧸ m.map (algebraMap R B)))
  letI : Module.Finite k C := Module.Finite.of_restrictScalars_finite R k C
  by_contra h
  let z : F := algebraMap R F π*x
  have hz : ¬IsLocalization.IsInteger B z := by
    rintro ⟨y,hy⟩
    exact h (show z∈integralClosure R F from hy ▸ y.2)
  obtain ⟨P,a,s,hs,hEq⟩ := exists_integral_multiple_residue z hz
  have hmax : (P.asIdeal.under R).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal P.asIdeal
  have hJP : J≤P.asIdeal := by
    apply Ideal.map_le_iff_le_comap.mpr
    exact (IsLocalRing.eq_maximalIdeal hmax).ge
  have hker : RingHom.ker (Ideal.Quotient.mk J) ≤ P.asIdeal := by
    rw [Ideal.mk_ker]
    exact hJP
  let Pbar : MaximalSpectrum C := ⟨P.asIdeal.map (Ideal.Quotient.mk J),
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective hker⟩
  have hsBar : Ideal.Quotient.mk J s ∉ Pbar.asIdeal := by
    intro hs1
    have hs2 : s∈(P.asIdeal.map (Ideal.Quotient.mk J)).comap (Ideal.Quotient.mk J) := hs1
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ←RingHom.ker_eq_comap_bot, sup_of_le_left hker] at hs2
    exact hs hs2
  obtain ⟨tbar,ht⟩ := exists_multiple_trace_ne_zero (k:=k) Pbar (Ideal.Quotient.mk J s) hsBar
  obtain ⟨t,rfl⟩ := Ideal.Quotient.mk_surjective tbar
  have htA : algebraMap B F (t*a)∈integralClosure R F := (t*a).2
  obtain ⟨c,hc⟩ := Submodule.mem_one.mp (mem_complementary.mp hx (algebraMap B F (t*a)) htA)
  have hEq' : algebraMap B F (t*s) = algebraMap R F π*(x*algebraMap B F (t*a)) := by
    rw [map_mul,map_mul,←hEq]
    change algebraMap B F t *((algebraMap R F π*x)*algebraMap B F a) = _
    ac_rfl
  have hTr : Algebra.trace K F (algebraMap B F (t*s)) = algebraMap R K (π*c) := calc
    Algebra.trace K F (algebraMap B F (t*s)) =
        Algebra.trace K F ((algebraMap R K π) • (x*algebraMap B F (t*a))) := by
      rw [hEq', Algebra.smul_def, ←IsScalarTower.algebraMap_apply R K F]
    _ = algebraMap R K (π*c) := by
      rw [map_smul,smul_eq_mul,←hc,map_mul]
  have hInt : Algebra.intTrace R B (t*s) = π*c := by
    apply IsFractionRing.injective R K
    exact (Algebra.algebraMap_intTrace (K:=K) (L:=F) (t*s)).trans hTr
  have hZero : Ideal.Quotient.mk m (Algebra.intTrace R B (t*s)) = 0 := by
    rw [hInt,map_mul,Ideal.Quotient.eq_zero_iff_mem.mpr hπ,zero_mul]
  have hSpecial : Algebra.trace k C (Ideal.Quotient.mk J (t*s)) =
      Ideal.Quotient.mk m (Algebra.intTrace R B (t*s)) :=
    Algebra.trace_quotient_eq_of_isDedekindDomain (R:=R) (S:=B) (p:=m) (x:=t*s)
  apply ht
  rw [←map_mul,hSpecial,hZero]

end SelectedHorizontalNormalDual318

#print axioms SelectedHorizontalNormalDual318.clears_of_residueCharZero
