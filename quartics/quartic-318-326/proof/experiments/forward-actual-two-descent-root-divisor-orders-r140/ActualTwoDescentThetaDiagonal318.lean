module
public import ActualTwoDescentEnlargementIndex318
public section
noncomputable section
namespace ActualTwoDescentThetaDiagonal318
open ActualTwoDescentDiagonalExtension318 ActualTwoDescentEnlargementIndex318
open scoped Matrix
set_option maxHeartbeats 16000000

/-- Every actual old/theta matrix admits a diagonal toggle confined to
its theta coordinates. This is the earlier constructive Schur proof on the
literal new support, with original indices fixed, not a cardinality claim. -/
theorem actual_theta_diagonal {U J : Type*} [Fintype U] [DecidableEq U]
    [Fintype J] [DecidableEq J] (M : Matrix (U ⊕ J) (U ⊕ J) (ZMod 2))
    (hM : IsUnit (M.submatrix Sum.inl Sum.inl)) :
    ∃ t : J → ZMod 2, IsUnit (M+Matrix.diagonal (Sum.elim (fun _ : U => 0) t)) := by
  let e := supportEquiv U J
  let R : Matrix (Index U (Fintype.card J)) (Index U (Fintype.card J)) (ZMod 2) :=
    (Matrix.reindexRingEquiv (ZMod 2) e.symm) M
  have hbase : R.submatrix (baseEmbed U (Fintype.card J)) (baseEmbed U (Fintype.card J))=
      M.submatrix Sum.inl Sum.inl := by
    ext i j
    change M (e (baseEmbed U (Fintype.card J) i)) (e (baseEmbed U (Fintype.card J) j))=
      M (Sum.inl i) (Sum.inl j)
    rw [supportEquiv_base,supportEquiv_base]
  obtain ⟨t,ht,hunit⟩ := actual_diagonal_toggle (Fintype.card J) R (by rw [hbase]; exact hM)
  let tJ : J → ZMod 2 := fun j => t (e.symm (Sum.inr j))
  refine ⟨tJ,?_⟩
  have hu := hunit.map (Matrix.reindexRingEquiv (ZMod 2) e).toMonoidHom
  have he : (Matrix.reindexRingEquiv (ZMod 2) e) (R+Matrix.diagonal t)=
      M+Matrix.diagonal (Sum.elim (fun _ : U => 0) tJ) := by
    ext i j
    change M (e (e.symm i)) (e (e.symm j))+
      Matrix.diagonal t (e.symm i) (e.symm j)=
      M i j+Matrix.diagonal (Sum.elim (fun _ : U => 0) tJ) i j
    rw [Equiv.apply_symm_apply,Equiv.apply_symm_apply]
    by_cases hij : i=j
    · subst j
      rw [Matrix.diagonal_apply_eq,Matrix.diagonal_apply_eq]
      congr 1
      cases i with
      | inl u =>
        change t ((supportEquiv U J).symm (Sum.inl u))=0
        rw [supportEquiv_symm_inl,ht]
      | inr j => rfl
    · have hn : e.symm i ≠ e.symm j := fun h => hij (e.symm.injective h)
      rw [Matrix.diagonal_apply_ne _ hn,Matrix.diagonal_apply_ne _ hij]
  rw [he] at hu
  exact hu

end ActualTwoDescentThetaDiagonal318
