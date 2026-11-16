module
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.Tactic
public section
noncomputable section
namespace EvenContactEtale318
open Polynomial
set_option maxHeartbeats 0
variable {R:Type*} [CommRing R]

@[expose] def polynomial (u:Rˣ) : R[X] := X^2-C (u:R)

theorem monic (u:Rˣ) : (polynomial u).Monic := monic_X_pow_sub_C _ (by decide)

abbrev RootRing (u:Rˣ):=AdjoinRoot (polynomial u)
@[expose] def root (u:Rˣ):RootRing u := AdjoinRoot.root (polynomial u)

theorem root_square (u:Rˣ) : (root u)^2=algebraMap R (RootRing u) (u:R) := by
  have h:=AdjoinRoot.mk_self (f:=polynomial u)
  change AdjoinRoot.mk (polynomial u) (X^2-C (u:R))=0 at h
  rw [map_sub,map_pow,AdjoinRoot.mk_X,AdjoinRoot.mk_C,sub_eq_zero] at h
  exact h

theorem root_isUnit (u:Rˣ) : IsUnit (root u) := by
  apply (isUnit_pow_iff (by decide : 2≠0)).mp
  rw [root_square]
  exact u.isUnit.map (algebraMap R (RootRing u))

theorem derivative_isUnit (u:Rˣ) (h2:IsUnit (2:R)) :
    IsUnit (AdjoinRoot.mk (polynomial u) (polynomial u).derivative) := by
  have h:AdjoinRoot.mk (polynomial u) (polynomial u).derivative=2*root u := by
    have hd:(polynomial u).derivative=C (2:R)*X := by simp [polynomial,derivative_pow]
    rw [hd,map_mul,AdjoinRoot.mk_C,AdjoinRoot.mk_X]
    change (AdjoinRoot.of (polynomial u)) 2*root u=2*root u
    rw [map_ofNat]
  rw [h]
  have hh:IsUnit (2:RootRing u):=by
    have hm:=h2.map (algebraMap R (RootRing u))
    rw [map_ofNat] at hm
    exact hm
  exact hh.mul (root_isUnit u)

@[expose] def pair (u:Rˣ) : StandardEtalePair R where
  f:=polynomial u
  monic_f:=monic u
  g:=(polynomial u).derivative
  cond:=⟨1,0,1,by simp⟩

/-- The derivative localization in the standard etale presentation is trivial,
because its derivative is an actual unit in the actual quadratic root algebra. -/
@[expose] def standardEquiv (u:Rˣ) (h2:IsUnit (2:R)) :
    (pair u).Ring ≃ₐ[R] RootRing u :=
  (pair u).equivAwayAdjoinRoot.trans
    ((IsLocalization.atUnit (RootRing u)
      (Localization.Away (AdjoinRoot.mk (polynomial u) (polynomial u).derivative))
      _ (derivative_isUnit u h2)).symm.restrictScalars R)

theorem rootRing_etale (u:Rˣ) (h2:IsUnit (2:R)) : Algebra.Etale R (RootRing u) :=
  Algebra.Etale.of_equiv (standardEquiv u h2)

theorem rootRing_finite (u:Rˣ) : Module.Finite R (RootRing u) :=
  (monic u).finite_adjoinRoot

theorem rootRing_free (u:Rˣ) : Module.Free R (RootRing u) :=
  (monic u).free_adjoinRoot

theorem rootRing_nontrivial [Nontrivial R] (u:Rˣ) : Nontrivial (RootRing u) := by
  apply (AdjoinRoot.nontrivial_iff_of_monic (monic u)).mpr
  rw [←Polynomial.natDegree_pos_iff_degree_pos]
  simp [polynomial]

theorem rootRing_rank_two [Nontrivial R] (u:Rˣ) :
    Module.finrank R (RootRing u)=2 := by
  rw [Module.finrank_eq_card_basis (AdjoinRoot.powerBasis' (monic u)).basis,Fintype.card_fin]
  change (polynomial u).natDegree=2
  simp [polynomial]

/-- The constructed finite etale algebra is an actual faithfully flat cover. -/
theorem rootRing_faithfullyFlat [Nontrivial R] (u:Rˣ) :
    Module.FaithfullyFlat R (RootRing u) := by
  let:=rootRing_nontrivial u
  let:=rootRing_free u
  infer_instance

/-- The actual normalized etale root algebra contains a root of every even
contact u*pi^(2k), with no Henselian or square-root-existence input. -/
theorem even_contact_root (u:Rˣ) (pi:R) (k:ℕ) :
    (root u*algebraMap R (RootRing u) pi^k)^2=
      algebraMap R (RootRing u) ((u:R)*pi^(2*k)) := by
  rw [mul_pow,root_square,map_mul,map_pow,←pow_mul]
  congr 2
  omega

/-- Every field-valued root with nonzero parameter image factors through the
constructed finite etale cover, not merely one selected generic-fiber branch. -/
theorem factor_even_contact_point (u:Rˣ) (pi:R) (k:ℕ)
    (L:Type*) [Field L] [Algebra R L]
    (hpi:algebraMap R L pi≠0) (y:L)
    (hy:y^2=algebraMap R L ((u:R)*pi^(2*k))) :
    ∃f:RootRing u→ₐ[R]L,
      f (root u*algebraMap R (RootRing u) pi^k)=y := by
  let a:L:=y/(algebraMap R L pi)^k
  have ha:a^2=algebraMap R L (u:R) := by
    dsimp [a]
    rw [div_pow]
    apply (div_eq_iff (pow_ne_zero 2 (pow_ne_zero k hpi))).mpr
    rw [hy,map_mul,map_pow]
    congr 1
    rw [←pow_mul]
    congr 1
    omega
  have hpoly:aeval a (polynomial u)=0 := by
    simp only [polynomial,map_sub,map_pow,aeval_X,aeval_C]
    exact sub_eq_zero.mpr ha
  let f:RootRing u→ₐ[R]L:=AdjoinRoot.liftAlgHom (polynomial u)
    (Algebra.ofId R L) a hpoly
  refine ⟨f,?_⟩
  rw [map_mul,map_pow,AlgHom.commutes]
  have hf:f (root u)=a := AdjoinRoot.liftAlgHom_root (polynomial u) (Algebra.ofId R L) a hpoly
  rw [hf]
  exact div_mul_cancel₀ _ (pow_ne_zero k hpi)

end EvenContactEtale318
