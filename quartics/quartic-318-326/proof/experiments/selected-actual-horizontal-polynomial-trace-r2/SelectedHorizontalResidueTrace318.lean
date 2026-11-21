module
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.Algebra.Ring.Idempotent
public import Mathlib.Tactic.Ring
public section
noncomputable section

namespace SelectedHorizontalResidueTrace318

section Lift
variable {C : Type*} [CommRing C]

/-- A literal partial residue characteristic function lifts to an
idempotent in the same finite quotient, without completeness or a
Henselian splitting. Bezout of positive powers gives the lift. -/
theorem lift_almost_idempotent (y : C) (hy : IsNilpotent (y*(1-y))) :
    ∃ e : C, IsIdempotentElem e ∧ IsNilpotent (y-e) := by
  obtain ⟨n,hn⟩ := hy
  have hzero : (y*(1-y))^(n+1)=0 := by
    rw [pow_succ,hn,zero_mul]
  have hcop : IsCoprime y (1-y) := ⟨1,1,by ring⟩
  have hpow : IsCoprime (y^(n+1)) ((1-y)^(n+1)) := hcop.pow
  obtain ⟨a,b,hsum⟩ := hpow
  let e : C := a*y^(n+1)
  have hone : e+b*(1-y)^(n+1)=1 := hsum
  have hcomp : 1-e=b*(1-y)^(n+1) := calc
    1-e = (e+b*(1-y)^(n+1))-e := congrArg (fun z : C => z-e) hone.symm
    _ = _ := by ring
  refine ⟨e,?_,?_⟩
  · apply isIdempotentElem_iff_mul_one_sub_self.mpr
    rw [hcomp]
    change (a*y^(n+1))*(b*(1-y)^(n+1))=0
    calc
      (a*y^(n+1))*(b*(1-y)^(n+1)) = (a*b)*(y*(1-y))^(n+1) := by rw [mul_pow]; ring
      _ = 0 := by rw [hzero,mul_zero]
  · have hd : y-e = (y*(1-y))*(b*(1-y)^n-a*y^n) := calc
      y-e = (1-e)*y-e*(1-y) := by ring
      _ = _ := by
        rw [hcomp]
        change (b*(1-y)^(n+1))*y-(a*y^(n+1))*(1-y) = _
        rw [pow_succ (1-y) n,pow_succ y n]
        ring
    exact ⟨n,by rw [hd,mul_pow,hn,zero_mul]⟩

/-- Apply to the actual element y=πxb in the finite residue algebra.
It is enough to know its residue is 0 or 1 at each prime; its
potentially nonreduced ring is not replaced by a residue field. -/
theorem nilpotent_deviation_of_residues (y : C)
    (h : ∀ P : Ideal C, P.IsPrime → y∈P ∨ 1-y∈P) :
    IsNilpotent (y*(1-y)) := by
  apply nilpotent_iff_mem_prime.mpr
  intro P hP
  exact (h P hP).elim (fun hy => P.mul_mem_right _ hy) (fun hy => P.mul_mem_left _ hy)

end Lift

variable {k C : Type*} [Field k] [CharZero k] [CommRing C] [Algebra k C]
variable [FiniteDimensional k C]

/-- The genuine trace of an almost idempotent that is nonzero in some
field quotient cannot vanish in characteristic zero. This is the
algebraic replacement for a completed tame-ramification calculation. -/
theorem trace_ne_zero (y : C) (hy : IsNilpotent (y*(1-y))) (hyn : ¬ IsNilpotent y) :
    Algebra.trace k C y ≠ 0 := by
  obtain ⟨e,he,hn⟩ := lift_almost_idempotent y hy
  have he0 : e≠0 := by
    intro h
    apply hyn
    simpa only [h,sub_zero] using hn
  have hn0 : Algebra.trace k C (y-e)=0 :=
    isNilpotent_iff_eq_zero.mp (Algebra.isNilpotent_trace_of_isNilpotent hn)
  have hmul : IsIdempotentElem (Algebra.lmul k C e) := by
    change Algebra.lmul k C e * Algebra.lmul k C e = Algebra.lmul k C e
    rw [←map_mul,he.eq]
  intro ht
  have hz : LinearMap.trace k C (Algebra.lmul k C e)=0 := by
    rw [←Algebra.trace_apply]
    exact (sub_eq_zero.mp (by simpa only [map_sub] using hn0)).symm.trans ht
  have h0 : Algebra.lmul k C e = 0 :=
    LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero hmul hz
  apply he0
  have h1 := DFunLike.congr_fun h0 (1:C)
  change e * (1 : C) = 0 at h1
  exact (mul_one e).symm.trans h1

end SelectedHorizontalResidueTrace318

#print axioms SelectedHorizontalResidueTrace318.lift_almost_idempotent
#print axioms SelectedHorizontalResidueTrace318.nilpotent_deviation_of_residues
#print axioms SelectedHorizontalResidueTrace318.trace_ne_zero
