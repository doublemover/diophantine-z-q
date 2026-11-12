module
public import RankTwoComplexHalfPeriods318
public import Mathlib.GroupTheory.QuotientGroup.Basic
public section
noncomputable section
namespace RankTwoComplexTwoTorsion318
open ComplexAffineFreeTranslation318 RankTwoComplexHalfPeriods318
set_option maxHeartbeats 2400000
variable (L : AddSubgroup ℂ) (basis : Coordinates ≃+ L)

@[expose] def torsion : AddSubgroup (Torus L) where
  carrier := {p | (2:ℤ) • p=0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy; simpa [smul_add,hx,hy]
  neg_mem' := by intro x hx; simpa [smul_neg,hx]
@[expose] def toTorsion : Coordinates →+ torsion L where
  toFun a := ⟨halfPeriod L basis a,half_killed L basis a⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ a b)
lemma toTorsion_surjective : Function.Surjective (toTorsion L basis) := by
  intro p
  obtain ⟨a,ha⟩ := half_surjective L basis p.val p.property
  exact ⟨a,Subtype.ext ha⟩

@[expose] def reduction : Coordinates →+ (Fin 2→ZMod 2) where
  toFun a i := a i
  map_zero' := by ext i; simp
  map_add' a b := by ext i; simp
lemma reduction_surjective : Function.Surjective reduction := by
  intro x
  have hx : ∀ i,∃ a : ℤ,(a:ZMod 2)=x i := fun i => ZMod.intCast_surjective (x i)
  choose a ha using hx
  exact ⟨a,funext ha⟩
lemma reduction_kernel (a : Coordinates) : reduction a=0 ↔ ∃ b,a=(2:ℤ) • b := by
  constructor
  · intro h
    have hd : ∀ i,(2:ℤ)∣a i := fun i =>
      (ZMod.intCast_zmod_eq_zero_iff_dvd (a i) 2).mp (congrFun h i)
    choose b hb using hd
    refine ⟨b,?_⟩
    ext i
    simpa only [Pi.smul_apply,zsmul_eq_mul] using hb i
  · rintro ⟨b,rfl⟩
    ext i
    simp [reduction,Pi.smul_apply,zsmul_eq_mul]

lemma equal_kernels : reduction.ker=(toTorsion L basis).ker := by
  ext a
  change reduction a=0 ↔ toTorsion L basis a=0
  rw [reduction_kernel]
  constructor
  · intro h
    exact Subtype.ext ((half_kernel L basis a).mpr h)
  · intro h
    exact (half_kernel L basis a).mp (congrArg Subtype.val h)

/-- An explicit equivalence with the ENTIRE two-torsion subgroup using
the specified rank-two lattice; no torsion-cardinality assumption. -/
@[expose] def torsionEquiv : (Fin 2→ZMod 2) ≃ torsion L :=
  ((QuotientAddGroup.quotientKerEquivOfSurjective reduction reduction_surjective).toEquiv.symm).trans
    ((Equiv.cast (congrArg (fun K : AddSubgroup Coordinates => Coordinates ⧸ K)
      (equal_kernels L basis))).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective (toTorsion L basis)
        (toTorsion_surjective L basis)).toEquiv)

include basis in
theorem torsion_finite : Finite (torsion L) :=
  Finite.of_equiv (Fin 2→ZMod 2) (torsionEquiv L basis)

include basis in
theorem torsion_card : Nat.card (torsion L)=4 := by
  rw [←Nat.card_congr (torsionEquiv L basis),Nat.card_eq_fintype_card]
  norm_num [Fintype.card_fun]
end RankTwoComplexTwoTorsion318
