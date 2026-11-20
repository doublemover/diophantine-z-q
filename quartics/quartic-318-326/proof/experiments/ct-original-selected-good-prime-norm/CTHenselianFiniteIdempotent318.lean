module
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.Tactic.LinearCombination
public section
noncomputable section

namespace CTHenselianFiniteIdempotent318

open Polynomial IsLocalRing
open scoped Polynomial

/-- Characteristic two is allowed: the derivative at the residual
idempotent is a unit because (2e−1)²=1, not because 2 is invertible. -/
theorem lift_idempotent {R : Type*} [CommRing R] (I : Ideal R) [HenselianRing R I]
    (e : R ⧸ I) (he : IsIdempotentElem e) :
    ∃ x : R, IsIdempotentElem x ∧ Ideal.Quotient.mk I x = e := by
  obtain ⟨x,hx⟩ := Ideal.Quotient.mk_surjective e
  let f := (X : R[X]) ^ 2 - X
  have hf : f.Monic := Polynomial.monic_X_pow_sub
    (lt_of_le_of_lt Polynomial.degree_X_le (by decide : (1 : WithBot ℕ) < 2))
  have hs : (2*e-1)*(2*e-1) = 1 := by
    have h : e*e=e := he
    linear_combination 4*h
  have hh : f.eval x ∈ I := by
    have h : e^2=e := by simpa only [pow_two] using he
    apply (Ideal.Quotient.eq_zero_iff_mem).1
    simp only [f,eval_sub,eval_pow,eval_X,map_sub,map_pow,hx,h,sub_self]
  have hu : IsUnit (Ideal.Quotient.mk I (f.derivative.eval x)) := by
    change IsUnit (Ideal.Quotient.mk I (derivative ((X : R[X])^2-X) |>.eval x))
    simp only [derivative_sub,derivative_X_sq,derivative_X,eval_sub,eval_mul,eval_C,eval_X,
      eval_one,map_sub,map_mul,map_ofNat,map_one,hx]
    exact ⟨⟨2*e-1,2*e-1,hs,hs⟩,rfl⟩
  obtain ⟨y,hy,hyx⟩ := HenselianRing.is_henselian (R := R) (I := I) f hf x hh hu
  have hy' : y*y=y := by
    change f.eval y = 0 at hy
    exact sub_eq_zero.1 (by simpa only [f,eval_sub,eval_pow,eval_X,pow_two] using hy)
  exact ⟨y,hy',((Ideal.Quotient.mk_eq_mk_iff_sub_mem (I := I) y x).2 hyx).trans hx⟩

/-- A second actual Artinian maximal factor supplies a nontrivial
idempotent. Use the pinned decomposition by a positive power of the
nilradical, so reducedness is not an extra premise. -/
theorem subsingleton_maximalSpectrum_of_trivial_idempotents
    (T : Type*) [CommRing T] [IsArtinianRing T]
    (hTriv : ∀ x : T, IsIdempotentElem x → x=0 ∨ x=1) :
    Subsingleton (MaximalSpectrum T) := by
  classical
  obtain ⟨n,hn⟩ := IsArtinianRing.isNilpotent_nilradical (R := T)
  have hN : (nilradical T)^(n+1) = (⊥ : Ideal T) := by
    rw [pow_succ,hn,zero_mul] <;> rfl
  let E : T ≃ₐ[T] ∀ m : MaximalSpectrum T, T ⧸ m.asIdeal^(n+1) :=
    (AlgEquiv.quotientBot T T).symm.trans
      ((Ideal.quotientEquivAlgOfEq T hN.symm).trans
        (IsArtinianRing.quotNilradicalPowEquivPi T (n+1)))
  constructor
  intro m k
  by_contra hmk
  let v : ∀ i : MaximalSpectrum T, T ⧸ i.asIdeal^(n+1) :=
    fun i => if i=m then 1 else 0
  have hV : IsIdempotentElem v := by
    change v*v=v
    funext i
    by_cases hi : i=m <;> simp [v,hi]
  have ht : IsIdempotentElem (E.symm v) := by
    change E.symm v * E.symm v = E.symm v
    rw [← map_mul,show v*v=v from hV]
  have hnz (i : MaximalSpectrum T) : (1 : T ⧸ i.asIdeal^(n+1)) ≠ 0 := by
    have hi : i.asIdeal^(n+1) ≤ i.asIdeal := by
      calc
        i.asIdeal^(n+1) ≤ i.asIdeal^1 :=
          Ideal.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le n))
        _ = i.asIdeal := pow_one _
    letI : Nontrivial (T ⧸ i.asIdeal^(n+1)) :=
      Ideal.Quotient.nontrivial_iff.2 (ne_top_of_le_ne_top i.isMaximal.ne_top hi)
    exact one_ne_zero
  rcases hTriv _ ht with h0 | h1
  · apply hnz m
    have h := congrArg (fun z : T => E z m) h0
    simpa [v] using h
  · apply hnz k
    have h := congrArg (fun z : T => E z k) h1
    simpa [v,Ne.symm hmk] using h.symm

/-- A domain Henselian at an ideal with Artinian quotient is local.
This is exactly the finite-domain/local-component step; no arbitrary
localization is asserted to be finite. -/
theorem domain_local_of_henselian_artinian_quotient
    (R : Type*) [CommRing R] [IsDomain R] (I : Ideal R) [HenselianRing R I]
    [IsArtinianRing (R ⧸ I)] : IsLocalRing R := by
  have hs : Subsingleton (MaximalSpectrum (R ⧸ I)) := by
    apply subsingleton_maximalSpectrum_of_trivial_idempotents
    intro e he
    obtain ⟨x,hx,rfl⟩ := lift_idempotent I e he
    have hh : x*(x-1)=0 := by rw [mul_sub,mul_one,show x*x=x from hx,sub_self]
    rcases mul_eq_zero.1 hh with h|h
    · left; rw [h,map_zero]
    · right; rw [sub_eq_zero.1 h,map_one]
  have hIK (P : Ideal R) (hP : P.IsMaximal) : I ≤ P := by
    apply (HenselianRing.jac (R := R) (I := I)).trans
    rw [Ideal.jacobson]
    exact sInf_le ⟨bot_le,hP⟩
  obtain ⟨M,hM⟩ := Ideal.exists_maximal R
  apply IsLocalRing.of_unique_max_ideal
  refine ⟨M,hM,?_⟩
  intro P hP
  letI : M.IsMaximal := hM
  letI : P.IsMaximal := hP
  let m := Ideal.Quotient.mk I
  have hmap (Q : Ideal R) [Q.IsMaximal] : (Q.map m).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (by change RingHom.ker (Ideal.Quotient.mk I) ≤ Q
          rw [Ideal.mk_ker]
          exact hIK Q inferInstance)
  let p' : MaximalSpectrum (R ⧸ I) := ⟨P.map m,hmap P⟩
  let m' : MaximalSpectrum (R ⧸ I) := ⟨M.map m,hmap M⟩
  have he : P.map (Ideal.Quotient.mk I) = M.map (Ideal.Quotient.mk I) :=
    congrArg MaximalSpectrum.asIdeal (hs.elim p' m')
  rw [← Ideal.comap_map_mk (hIK P hP),he,Ideal.comap_map_mk (hIK M hM)]

end CTHenselianFiniteIdempotent318
