module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# The literal dual-number closed fibre has all actual thickened points
-/

public section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MulOpposite

namespace SelectedSameADualNumberPointSurjectivity318

universe u

variable (k : Type u) [Field k]

abbrev reductionMap : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (TrivSqZeroExt k k)) :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)

/-- Every prime contains the actual square-zero kernel. This is
point-surjectivity, not an assertion that the reduction is an isomorphism. -/
theorem reduction_surjective : Surjective (reductionMap k) := by
  let f : TrivSqZeroExt k k →+* k := (TrivSqZeroExt.fstHom k k k).toRingHom
  have hs : Function.Surjective f := by
    intro x
    refine ⟨(TrivSqZeroExt.inl x : TrivSqZeroExt k k), ?_⟩
    change (TrivSqZeroExt.inl x : TrivSqZeroExt k k).fst = x
    exact TrivSqZeroExt.fst_inl k x
  constructor
  change Function.Surjective (PrimeSpectrum.comap f)
  rw [← Set.range_eq_univ, range_comap_of_surjective _ f hs]
  apply Set.eq_univ_of_forall
  intro p
  apply (PrimeSpectrum.mem_zeroLocus p _).2
  intro x hx
  have hx0 : x.fst = 0 := RingHom.mem_ker.mp hx
  have hnil : IsNilpotent x := by
    refine ⟨2, ?_⟩
    rw [pow_two]
    apply TrivSqZeroExt.ext <;> simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul,
      TrivSqZeroExt.fst_zero, TrivSqZeroExt.snd_zero, hx0, zero_mul, MulOpposite.op_zero, zero_smul, zero_add]
  exact nilradical_le_prime p.asIdeal (mem_nilradical.mpr hnil)

theorem dual_number_scheme_subsingleton :
    Subsingleton (Spec (CommRingCat.of (TrivSqZeroExt k k))) := by
  letI := reduction_surjective k
  constructor
  intro x y
  obtain ⟨a, rfl⟩ := (reductionMap k).surjective x
  obtain ⟨b, rfl⟩ := (reductionMap k).surjective y
  exact congrArg (reductionMap k) (Subsingleton.elim a b)

/-- The actual pullback closed fibre has all points of the same
infinitesimal scheme. The pullback itself remains nontrivial as a scheme. -/
theorem closed_points_onto {X A : Scheme.{u}}
    (q : X ⟶ Spec (CommRingCat.of (TrivSqZeroExt k k)))
    (i : A ⟶ X) (p : A ⟶ Spec (CommRingCat.of k))
    (H : IsPullback i p q (reductionMap k)) :
    Function.Surjective i := by
  letI : Surjective i := MorphismProperty.of_isPullback H.flip (reduction_surjective k)
  exact i.surjective

end SelectedSameADualNumberPointSurjectivity318
