module
public import FourRootActualFiniteRamification318
public import FourRootSquaredInfinityBase318
public section
noncomputable section
namespace FourRootReciprocalBranchData318
variable (b:Fin 4→ℂ) (hb:Function.Injective b)
@[expose] def difference (k:Fin 3):ℂ:=b 0-b k.succ
lemma difference_ne_zero (k:Fin 3):difference b k≠0:=by
  intro h
  exact (Fin.succ_ne_zero k) (hb (sub_eq_zero.mp h)).symm
/-- Actual reciprocal projective coordinate v=u². The new branch values
are the images of the original finite contacts under v=1/(t-b0). -/
@[expose] def branches:Fin 4→ℂ:=Fin.cases 0 (fun k=>-(difference b k)⁻¹)
lemma branches_zero:branches b 0=0:=rfl
lemma branches_succ (k:Fin 3):branches b k.succ=-(difference b k)⁻¹:=rfl
lemma branch_ne_zero (k:Fin 3):branches b k.succ≠0:=
  neg_ne_zero.mpr (inv_ne_zero (difference_ne_zero b hb k))
lemma branches_injective:Function.Injective (branches b):=by
  intro i
  refine Fin.cases ?_ (fun k=>?_) i
  · intro j
    refine Fin.cases (fun _=>rfl) (fun l h=>?_) j
    exact False.elim (branch_ne_zero b hb l h.symm)
  · intro j
    refine Fin.cases (fun h=>False.elim (branch_ne_zero b hb k h)) (fun l h=>?_) j
    have hd:difference b k=difference b l:=inv_injective (neg_injective h)
    have he:b k.succ=b l.succ:=by dsimp [difference] at hd;linear_combination -hd
    exact hb he

@[expose] def scale (k:Fin 3):ℂ:=
  (IsAlgClosed.exists_pow_nat_eq (difference b k) (by decide:0<2)).choose
lemma scale_square (k:Fin 3):scale b k^2=difference b k:=
  (IsAlgClosed.exists_pow_nat_eq (difference b k) (by decide:0<2)).choose_spec
lemma scale_ne_zero (k:Fin 3):scale b k≠0:=by
  intro h
  apply difference_ne_zero b hb k
  rw [←scale_square,h,zero_pow (by decide:2≠0)]
lemma inv_scale_square (k:Fin 3):(scale b k)⁻¹^2=(difference b k)⁻¹:=by
  rw [inv_pow,scale_square]
lemma difference_inv_scale_square (k:Fin 3):difference b k*(scale b k)⁻¹^2=1:=by
  rw [inv_scale_square,mul_inv_cancel₀ (difference_ne_zero b hb k)]
end FourRootReciprocalBranchData318
