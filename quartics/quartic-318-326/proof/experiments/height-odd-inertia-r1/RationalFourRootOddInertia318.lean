module
public import RationalFourRootInertia318
public import SquareRootInertiaBound318
public section
noncomputable section
namespace RationalFourRootOddInertia318
open NumberField RationalFourRootFiber318 FourRootOrderSigns318
open scoped NumberField
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
variable (a : Fin 4 → ℚ)
abbrev L := PointField a
abbrev G := L a ≃ₐ[ℚ] L a

/-- The original scaled roots, in the original maximal residue field. -/
@[expose] def scaledRoot (d : ℚ) (i : Fin 4) : L a := algebraMap ℚ (L a) d * root a i

lemma scaledRoot_square (d : ℚ) (b : Fin 4 → ℤ)
    (hab : ∀ i, d^2*a i = (b i : ℚ)) (i : Fin 4) :
    scaledRoot a d i ^ 2 = (b i : L a) := by
  rw [scaledRoot, mul_pow, root_square, ← map_pow, ← map_mul, hab]
  simp

lemma eq_one_of_scaledRoots_fixed (d : ℚ) (hd : d ≠ 0) (s : G a)
    (hs : ∀ i, s (scaledRoot a d i) = scaledRoot a d i) : s = 1 := by
  have hroot (i : Fin 4) : s (root a i) = root a i := by
    have hdL : algebraMap ℚ (L a) d ≠ 0 := by
      simpa only [map_zero] using (algebraMap ℚ (L a)).injective.ne hd
    apply mul_left_cancel₀ hdL
    simpa only [scaledRoot, map_mul, AlgEquiv.commutes] using hs i
  have hpoint : s.toAlgHom.comp (point a) = point a := by
    apply FourRootSignBaseChange318.hom_ext
    exact hroot
  apply AlgEquiv.ext
  intro y
  obtain ⟨z, rfl⟩ := point_surjective a y
  exact AlgHom.congr_fun hpoint z

/-- Actual inertia at every odd rational prime has at most two elements.
This includes primes in the contact support. No abstract sign group replaces
the actual action on the ring of integers of the original quotient field. -/
theorem inertia_card_le_two (d : ℚ) (hd : d ≠ 0) (b : Fin 4 → ℤ)
    (hb : ∀ i, b i ≠ 0) (hab : ∀ i, d^2*a i = (b i : ℚ))
    (p : ℕ) [Fact p.Prime] (h2 : ¬(p : ℤ) ∣ 2)
    (P : Ideal (𝓞 (L a))) [P.IsPrime]
    (hover : P.under ℤ = Ideal.span {(p : ℤ)}) :
    Nat.card (P.inertia (G a)) ≤ 2 := by
  classical
  by_cases he : ∀ i, Even (padicValInt p (b i))
  · rw [RationalFourRootInertia318.inertia_eq_bot a d hd b hb hab p h2 he P hover]
    simp
  push Not at he
  obtain ⟨j, hj⟩ := he
  have hjo : Odd (padicValInt p (b j)) := Nat.not_even_iff_odd.mp hj
  let x := scaledRoot a d j
  have hx : x^2 = (b j : L a) := scaledRoot_square a d b hab j
  have hkernel (s : G a) (hs : s ∈ P.inertia (G a)) (hfix : s x = x) : s = 1 := by
    apply eq_one_of_scaledRoots_fixed a d hd s
    intro i
    exact SquareRootInertiaBound318.fixes_of_fixed_odd_root p P hover h2
      (b i) (b j) (hb i) (hb j) hjo (scaledRoot a d i) x
      (scaledRoot_square a d b hab i) hx s hs hfix
  have hinj : Function.Injective (fun s : P.inertia (G a) => s.val x) := by
    intro s t hst
    change s.val x = t.val x at hst
    have hfix : (t.val⁻¹ * s.val) x = x := by
      change t.val.symm (s.val x) = x
      rw [hst, AlgEquiv.symm_apply_apply]
    have h := hkernel _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ t.property) s.property) hfix
    exact Subtype.ext (inv_mul_eq_one.mp h).symm
  have hsign (s : P.inertia (G a)) : s.val x = x ∨ s.val x = -x := by
    apply sq_eq_sq_iff_eq_or_eq_neg.mp
    rw [← map_pow, hx, map_intCast]
  let code (s : P.inertia (G a)) : Bool := if s.val x = x then false else true
  have hcode : Function.Injective code := by
    intro s t hst
    apply hinj
    by_cases hs : s.val x = x <;> by_cases ht : t.val x = x
    · exact hs.trans ht.symm
    · simp [code, hs, ht] at hst
    · simp [code, hs, ht] at hst
    · exact ((hsign s).resolve_left hs).trans ((hsign t).resolve_left ht).symm
  have hcard := Nat.card_le_card_of_injective code hcode
  simpa using hcard

end RationalFourRootOddInertia318
