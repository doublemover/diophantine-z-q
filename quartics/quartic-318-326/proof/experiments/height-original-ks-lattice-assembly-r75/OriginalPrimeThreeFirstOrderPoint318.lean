module
public import OriginalPrimeThreeNormalizedSpecialFiber318
public import IntegralRootPointMaps318
public import DualNumberCotangentCertificate318
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Data.ZMod.Basic
public section
noncomputable section
namespace OriginalPrimeThreeFirstOrderPoint318
open Polynomial
open OriginalPrimeThreeActualQuotient318
open PrimeThreeLocalizationQuotient318

/-- The residue field is constructed, not postulated. No element of F3
has square two, so this quadratic algebra is the field with nine elements. -/
abbrev K := QuadraticAlgebra (ZMod 3) 2 0
local instance nonsquare : Fact (∀ r : ZMod 3, r ^ 2 ≠ 2 + 0 * r) :=
  ⟨by intro r; fin_cases r <;> norm_num⟩
instance residueField : Field K := inferInstance
abbrev D := DualNumber K
@[expose] def alpha : K := QuadraticAlgebra.omega

theorem alpha_square : alpha ^ 2 = 2 := by
  simp [alpha, QuadraticAlgebra.omega_pow_two_eq_add, Algebra.smul_def]

theorem three_K : (3 : K) = 0 := by
  apply QuadraticAlgebra.ext <;> norm_num

theorem three_D : (3 : D) = 0 := by
  apply TrivSqZeroExt.ext <;> simp [three_K]

/-- The actual parameter specializes to 2. All first-order directions
below are in the three roots whose contact values coincide modulo 3. -/
@[expose] def polynomialAlgebra : Algebra ℤ[X] D :=
  (Polynomial.eval₂RingHom (Int.castRingHom D) 2).toAlgebra
attribute [local instance] polynomialAlgebra

@[expose] def values (v : Fin 3 → K) : Fin 4 → D :=
  ![TrivSqZeroExt.inl alpha, TrivSqZeroExt.inr (v 0),
    TrivSqZeroExt.inr (v 1), TrivSqZeroExt.inr (v 2)]

theorem values_square (v : Fin 3 → K) (i : Fin 4) :
    values v i ^ 2 = algebraMap ℤ[X] D
      (OriginalIntegerAffineModel318.coefficient twist i) := by
  rw [untwisted_coefficient]
  change values v i ^ 2 =
    Polynomial.eval₂ (Int.castRingHom D) 2
      (X - C (OriginalIntegerAffineModel318.contacts i))
  fin_cases i
  · simp [values, OriginalIntegerAffineModel318.contacts, ← TrivSqZeroExt.inl_pow,
      alpha_square]
  · norm_num [values, OriginalIntegerAffineModel318.contacts, pow_two,
      TrivSqZeroExt.inr_mul_inr, show (32 : D) = 2 by
        have h := three_D; linear_combination 10 * h]
  · norm_num [values, OriginalIntegerAffineModel318.contacts, pow_two,
      TrivSqZeroExt.inr_mul_inr, show (76832 : D) = 2 by
        have h := three_D; linear_combination 25610 * h]
  · norm_num [values, OriginalIntegerAffineModel318.contacts, pow_two,
      TrivSqZeroExt.inr_mul_inr, show (-343 : D) = 2 by
        have h := three_D; linear_combination -115 * h]

@[expose] def originalRoot (i : Fin 4) : Order :=
  FourRootOrderSigns318.generator (OriginalIntegerAffineModel318.coefficient twist) i

/-- Actual homomorphisms from the original order to dual numbers, one
for EVERY triple of root velocities, not merely formal polynomial vectors. -/
@[expose] def originalLift (v : Fin 3 → K) : Order →+* D :=
  (IntegralRootPointMaps318.fourMap
    (OriginalIntegerAffineModel318.coefficient twist) (values v) (values_square v)).toRingHom

@[simp] theorem originalLift_root (v : Fin 3 → K) (i : Fin 4) :
    originalLift v (originalRoot i) = values v i :=
  IntegralRootPointMaps318.fourMap_generator _ _ _ i

theorem originalLift_polynomial (v : Fin 3 → K) (p : ℤ[X]) :
    originalLift v (algebraMap ℤ[X] Order p) = algebraMap ℤ[X] D p :=
  (IntegralRootPointMaps318.fourMap
    (OriginalIntegerAffineModel318.coefficient twist) (values v) (values_square v)).commutes p

@[expose] def projection : D →+* K :=
  (TrivSqZeroExt.fstHom K K K).toRingHom
@[expose] def originalPoint : Order →+* K :=
  projection.comp (originalLift 0)

theorem originalLift_fst (v : Fin 3 → K) (x : Order) :
    (originalLift v x).fst = originalPoint x := by
  have h : projection.comp (originalLift v) = originalPoint := by
    apply IntegralRootPointMaps318.four_ringHom_ext
    · apply RingHom.ext
      intro p
      change projection (originalLift v (algebraMap ℤ[X] Order p)) =
        projection (originalLift 0 (algebraMap ℤ[X] Order p))
      rw [originalLift_polynomial, originalLift_polynomial]
    · intro i
      change (originalLift v (originalRoot i)).fst = (originalLift 0 (originalRoot i)).fst
      rw [originalLift_root, originalLift_root]
      fin_cases i <;> rfl
  exact RingHom.congr_fun h x

/-- The point is a closed point of the literal original affine chart:
its map onto the explicit residue field is surjective. -/
theorem originalPoint_surjective : Function.Surjective originalPoint := by
  intro z
  refine ⟨(z.re.val : Order) + (z.im.val : Order) * originalRoot 0, ?_⟩
  have hroot : originalPoint (originalRoot 0) = alpha := by
    change (originalLift 0 (originalRoot 0)).fst = alpha
    rw [originalLift_root]
    rfl
  rw [map_add, map_mul, map_natCast, map_natCast, hroot]
  have hre : (z.re.val : K) = algebraMap (ZMod 3) K z.re := by
    simpa only [ZMod.natCast_zmod_val] using
      (map_natCast (algebraMap (ZMod 3) K) z.re.val).symm
  have him : (z.im.val : K) = algebraMap (ZMod 3) K z.im := by
    simpa only [ZMod.natCast_zmod_val] using
      (map_natCast (algebraMap (ZMod 3) K) z.im.val).symm
  rw [hre, him]
  simpa only [Algebra.smul_def, mul_one, alpha] using
    QuadraticAlgebra.re_smul_add_im_smul z

@[expose] def quotientLift (v : Fin 3 → K) : Fiber Order →+* D :=
  Ideal.Quotient.lift (threeIdeal Order) (originalLift v) (by
    change threeIdeal Order ≤ RingHom.ker (originalLift v)
    apply Ideal.span_le.mpr
    intro x hx
    have hx' : x = 3 := Set.mem_singleton_iff.mp hx
    subst x
    change originalLift v 3 = 0
    rw [map_ofNat, three_D])

abbrev Closure := OriginalPrimeThreeNormalizedLocalIdentification318.Closure
attribute [local instance] OriginalIntegerNormalizationMap318.closureAlgebra

/-- Transport through the proven canonical special-fiber identification
puts every first-order lift on the ACTUAL normalization, not just the order. -/
@[expose] def normalizedLift (v : Fin 3 → K) : Closure →+* D :=
  (quotientLift v).comp
    (OriginalPrimeThreeNormalizedSpecialFiber318.normalizedFiberEquiv.symm.toRingHom.comp
      (Ideal.Quotient.mk (threeIdeal Closure)))

@[expose] def normalizedPoint : Closure →+* K :=
  projection.comp (normalizedLift 0)

theorem normalizedLift_on_order (v : Fin 3 → K) (a : Order) :
    normalizedLift v (algebraMap Order Closure a) = originalLift v a := by
  change quotientLift v
    (OriginalPrimeThreeNormalizedSpecialFiber318.normalizedFiberEquiv.symm
      (Ideal.Quotient.mk (threeIdeal Closure) (algebraMap Order Closure a))) = _
  rw [← OriginalPrimeThreeNormalizedSpecialFiber318.normalizedFiberEquiv_on_order,
    RingEquiv.symm_apply_apply]
  rfl

theorem normalizedLift_fst (v : Fin 3 → K) (z : Closure) :
    (normalizedLift v z).fst = normalizedPoint z := by
  let x := OriginalPrimeThreeNormalizedSpecialFiber318.normalizedFiberEquiv.symm
    (Ideal.Quotient.mk (threeIdeal Closure) z)
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective x
  change (quotientLift v x).fst = (quotientLift 0 x).fst
  rw [← ha]
  exact originalLift_fst v a

theorem normalizedPoint_on_order (a : Order) :
    normalizedPoint (algebraMap Order Closure a) = originalPoint a := by
  change (normalizedLift 0 (algebraMap Order Closure a)).fst = originalPoint a
  rw [normalizedLift_on_order]
  rfl

theorem normalizedPoint_surjective : Function.Surjective normalizedPoint := by
  intro z
  obtain ⟨a, ha⟩ := originalPoint_surjective z
  exact ⟨algebraMap Order Closure a, (normalizedPoint_on_order a).trans ha⟩

@[expose] def normalizedRoot (i : Fin 3) : Closure :=
  algebraMap Order Closure (originalRoot i.succ)
@[expose] def tangentLift (j : Fin 3) : Closure →+* D :=
  normalizedLift (fun i => if i = j then 1 else 0)

theorem tangentLift_root (j i : Fin 3) :
    tangentLift j (normalizedRoot i) =
      TrivSqZeroExt.inr (if i = j then (1 : K) else 0) := by
  rw [tangentLift, normalizedRoot, normalizedLift_on_order, originalLift_root]
  fin_cases i <;> rfl

/-- Three genuinely independent cotangent directions at the constructed
point of the ACTUAL normalized affine chart. This is the precise relation
certificate; no cotangent-dimension or regularity premise is assumed. -/
theorem normalized_roots_independent_mod_square (a : Fin 3 → Closure)
    (ha : (∑ i, a i * normalizedRoot i) ∈ (RingHom.ker normalizedPoint) ^ 2) :
    ∀ j, normalizedPoint (a j) = 0 :=
  DualNumberCotangentCertificate318.independent_mod_square normalizedPoint tangentLift
    (fun _ x => normalizedLift_fst _ x) normalizedRoot tangentLift_root a ha

theorem normalized_root_mem_point (i : Fin 3) :
    normalizedRoot i ∈ RingHom.ker normalizedPoint :=
  DualNumberCotangentCertificate318.root_mem_kernel normalizedPoint tangentLift
    (fun _ x => normalizedLift_fst _ x) normalizedRoot tangentLift_root i

end OriginalPrimeThreeFirstOrderPoint318
