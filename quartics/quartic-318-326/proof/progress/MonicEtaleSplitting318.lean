module
public import MonicRootEtale318
public section
noncomputable section
namespace MonicEtaleSplitting318
open Polynomial
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u

/-- An actual finite-etale faithfully-flat extension and a complete linear
factorization. Its construction is supplied below, not assumed. -/
structure Splitting {R:Type u} [CommRing R] (p:R[X]) (n:ℕ) where
  S:Type u
  [commRing:CommRing S]
  [algebra:Algebra R S]
  [nontrivial:Nontrivial S]
  [finite:Module.Finite R S]
  [etale:Algebra.Etale R S]
  [faithfullyFlat:Module.FaithfullyFlat R S]
  roots:Fin n→S
  factorization:p.map (algebraMap R S)=∏i, (X-C (roots i))
attribute [instance] Splitting.commRing Splitting.algebra Splitting.nontrivial
  Splitting.finite Splitting.etale Splitting.faithfullyFlat

/-- Adjoin a root, divide by its monic linear factor and repeat. Every
step is an actual finite-free etale algebra, so the final extension is
finite etale and faithfully flat over the original ring. -/
theorem exists_splitting (n:ℕ) :
    ∀ (R:Type u) [CommRing R] [Nontrivial R] (p:R[X]),
      p.Monic → p.Separable → p.natDegree=n → Nonempty (Splitting p n) := by
  induction n with
  | zero =>
    intro R _ _ p hp hs hn
    have hp1:p=1:=hp.natDegree_eq_zero.mp hn
    refine ⟨{S:=R,roots:=fun i=>Fin.elim0 i,factorization:=?_}⟩
    simp [hp1]
  | succ n ih =>
    intro R _ _ p hp hs hn
    let A:=AdjoinRoot p
    letI:Module.Finite R A:=hp.finite_adjoinRoot
    letI:Algebra.Etale R A:=MonicRootEtale318.root_etale p hp hs
    letI:Module.FaithfullyFlat R A:=MonicRootEtale318.root_faithfullyFlat p hp (by omega)
    letI:Nontrivial A:=(AdjoinRoot.nontrivial_iff_of_monic hp).mpr
      (Polynomial.natDegree_pos_iff_degree_pos.mp (by omega))
    let q:Polynomial A:=p.map (algebraMap R A) /ₘ (X-C (AdjoinRoot.root p))
    have hfac:(X-C (AdjoinRoot.root p))*q=p.map (algebraMap R A):=
      Polynomial.mul_divByMonic_eq_iff_isRoot.mpr (AdjoinRoot.isRoot_root p)
    have hq:q.Monic := (monic_X_sub_C _).of_mul_monic_left (hfac.symm ▸ hp.map _)
    have hqs:q.Separable := (hfac.symm ▸ hs.map).of_mul_right
    have hqn:q.natDegree=n := by
      dsimp only [q]
      rw [natDegree_divByMonic _ (monic_X_sub_C _),hp.natDegree_map,natDegree_X_sub_C,hn]
      omega
    obtain ⟨d⟩:=ih A q hq hqs hqn
    letI:Algebra R d.S:=((algebraMap A d.S).comp (algebraMap R A)).toAlgebra
    letI:IsScalarTower R A d.S:=IsScalarTower.of_algebraMap_eq' rfl
    letI:Module.Finite R d.S:=Module.Finite.trans A d.S
    letI:Algebra.Etale R d.S:=Algebra.Etale.comp R A d.S
    letI:Module.FaithfullyFlat R d.S:=Module.FaithfullyFlat.trans R A d.S
    refine ⟨{
      S := d.S
      roots := Fin.cons (algebraMap A d.S (AdjoinRoot.root p)) d.roots
      factorization := ?_ }⟩
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero,Fin.cons_succ]
    have hh:=congrArg (Polynomial.map (algebraMap A d.S)) hfac
    rw [Polynomial.map_mul,Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C,
      d.factorization] at hh
    rw [IsScalarTower.algebraMap_eq R A d.S,←Polynomial.map_map]
    exact hh.symm

@[expose] def splitting {R:Type u} [CommRing R] [Nontrivial R]
    (p:R[X]) (hp:p.Monic) (hs:p.Separable) : Splitting p p.natDegree :=
  Classical.choice (exists_splitting p.natDegree R p hp hs rfl)

end MonicEtaleSplitting318
