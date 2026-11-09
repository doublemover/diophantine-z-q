module
public import FourRootSignBaseChange318
public section
noncomputable section
namespace FourRootPointTorsor318
open FourRootOrder318 FourRootOrderSigns318
set_option maxHeartbeats 500000
variable {R F : Type*} [CommRing R] [Field F] [CharZero F] [Algebra R F]
  (a : Fin 4 → R) (ha : ∀ i, algebraMap R F (a i) ≠ 0)
  (p : Order a →ₐ[R] F)

include ha in
omit [CharZero F] in
theorem root_ne_zero (i : Fin 4) : p (generator a i) ≠ 0 := by
  intro h
  have hs : p (generator a i)^2 = algebraMap R F (a i) := by
    rw [← map_pow, generator_square, AlgHom.commutes]
  rw [h, zero_pow (by decide : 2 ≠ 0)] at hs
  exact ha i hs.symm

omit [CharZero F] in
/-- Every point of the same nonbranch fiber is obtained by actual root signs. -/
theorem orbit_surjective : Function.Surjective
    (fun s : Fin 4 → Bool => p.comp (signEquiv a s).toAlgHom) := by
  classical
  intro q
  have hs (i : Fin 4) : ∃ b : Bool,
      q (generator a i) = if b then -p (generator a i) else p (generator a i) := by
    have he : q (generator a i)^2 = p (generator a i)^2 := by
      rw [← map_pow, ← map_pow, generator_square, AlgHom.commutes, AlgHom.commutes]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with h | h
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  choose s hs using hs
  refine ⟨s, ?_⟩
  apply FourRootSignBaseChange318.hom_ext
  intro i
  change p (signEquiv a s (generator a i)) = q (generator a i)
  rw [signEquiv_generator]
  cases h : s i <;> simpa [h] using (hs i).symm

include ha in
/-- The actual sign action is free whenever all four fiber coefficients are nonzero. -/
theorem orbit_injective : Function.Injective
    (fun s : Fin 4 → Bool => p.comp (signEquiv a s).toAlgHom) := by
  intro s t he
  funext i
  have h := congrArg (fun q : Order a →ₐ[R] F => q (generator a i)) he
  change p (signEquiv a s (generator a i)) = p (signEquiv a t (generator a i)) at h
  rw [signEquiv_generator, signEquiv_generator] at h
  cases hs : s i <;> cases ht : t i
  · rfl
  · exfalso
    simp only [hs, ht, Bool.false_eq_true, ite_false, ite_true, map_neg] at h
    have hz : (2 : F) * p (generator a i) = 0 := by linear_combination h
    exact mul_ne_zero (by norm_num) (root_ne_zero a ha p i) hz
  · exfalso
    simp only [hs, ht, Bool.false_eq_true, ite_false, ite_true, map_neg] at h
    have hz : (2 : F) * p (generator a i) = 0 := by linear_combination -h
    exact mul_ne_zero (by norm_num) (root_ne_zero a ha p i) hz
  · rfl

/-- The existing point identifies all points of the actual fiber with the
sixteen literal sign patterns, without an algebraic-closure assumption. -/
@[expose] def orbitEquiv : (Fin 4 → Bool) ≃ (Order a →ₐ[R] F) :=
  Equiv.ofBijective _ ⟨orbit_injective a ha p, orbit_surjective a p⟩

include ha p in
theorem point_card : Nat.card (Order a →ₐ[R] F) = 16 := by
  rw [← Nat.card_congr (orbitEquiv a ha p)]
  norm_num [Nat.card_eq_fintype_card]

end FourRootPointTorsor318
