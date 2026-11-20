module
public import ActualMillerGeometricDivisor318
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum
import all ActualMillerGeometricDivisor318
import all ActualMillerAffineLocalChart318
import all ActualMillerAffineValuation318
import all ActualMillerInfinityNormalization318
import all ActualTwoDescentEllipticModel318
import all ActualTwoDescentOriginalFunctionFieldTheta318
import all ActualTwoDescentOriginalNativeFunctionFieldEquivalence318
import all ActualMillerInfinityChartMap318
import all ActualTwoDescentInfinityChartRing318
import all ActualTwoDescentInfinityLocalParameter318
import all ActualTwoDescentInfinityNativeFractionFunctions318
public section
noncomputable section

namespace ActualMillerProduct318

open ActualTwoDescentEllipticModel318 ActualTwoDescentInfinityChartRing318
open ActualTwoDescentInfinityLocalParameter318 ActualTwoDescentInfinityNativeFractionFunctions318
open ActualTwoDescentOriginalFunctionFieldTheta318
open ActualTwoDescentOriginalNativeFunctionFieldEquivalence318
open ActualTwoDescentOriginalGlobalInfinityPoleUnit318
open ActualMillerGeometricDivisor318 ActualMillerInfinityNormalization318
open ActualMillerAffineLocalChart318 ActualMillerAffineValuation318

private theorem map_pow_unit {A F : Type*} [CommRing A] [Field F]
    (g : A →+* F) (u : Aˣ) (b : ℤ) :
    g (↑(u ^ b) : A) = (g (u : A))^b := by
  calc
    _ = (↑(Units.map g.toMonoidHom (u ^ b)) : F) := rfl
    _ = (↑(Units.map g.toMonoidHom u ^ b) : F) := by rw [map_zpow]
    _ = _ := Units.val_zpow_eq_zpow_val _ _

/-- The needed compatibility is association of uniformizers, not
a new uniqueness oracle for valuations. It retains an actual unit
even when b is negative. -/
theorem multiply_dvr_factors {A F : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field F] (g : A →+* F) (hg : Function.Injective g)
    (p q : A) (hp : Irreducible p) (hq : Irreducible q) (e d : Aˣ) (a b : ℤ) :
    ∃ w : Aˣ, (g (e : A) * (g p)^a) * (g (d : A) * (g q)^b) =
      g (w : A) * (g p)^(a+b) := by
  obtain ⟨u, hu⟩ := IsDiscreteValuationRing.associated_of_irreducible A hp hq
  have hp₀ : g p ≠ 0 := fun hz => hp.ne_zero (hg (hz.trans g.map_zero.symm))
  refine ⟨e * d * u^b, ?_⟩
  rw [← hu, map_mul g p, mul_zpow, zpow_add₀ hp₀]
  change (g (e : A) * (g p)^a) * (g (d : A) * ((g p)^b * (g (u : A))^b)) =
    g (((e : A) * (d : A)) * (↑(u^b) : A)) * ((g p)^a * (g p)^b)
  rw [map_mul, map_mul, map_pow_unit]
  ac_rfl

variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]

theorem geometric_order_mul (n : K) (hn : n ≠ 0) {f g : OriginalFunctionField n}
    {R : Point n} {a b : ℤ} (hf : HasGeometricOrder n f R a)
    (hg : HasGeometricOrder n g R b) : HasGeometricOrder n (f*g) R (a+b) := by
  cases R with
  | zero =>
    obtain ⟨e,he⟩ := hf
    obtain ⟨d,hd⟩ := hg
    have ht : originT n ≠ 0 := neg_ne_zero.mpr (actual_infinity_fraction_u_nonzero n)
    refine ⟨e * d, ?_⟩
    change originalNativeFunctionFieldEquiv n (f*g) =
      infinityFractionMap n ((e : InfinityLocalRing n) * (d : InfinityLocalRing n)) *
        (originT n)^(a+b)
    rw [map_mul, he, hd, map_mul, zpow_add₀ ht]
    ac_rfl
  | some x y hs =>
    letI := actual_affine_local_DVR n x y hn hs.left
    obtain ⟨p,hp,e,he⟩ := hf
    obtain ⟨q,hq,d,hd⟩ := hg
    let φ := toLocalField n x y hs.left
    obtain ⟨w,hw⟩ := multiply_dvr_factors φ
      (IsFractionRing.injective (AffineLocal n x y hs.left) (LocalField n x y hs.left))
      p q hp hq e d a b
    refine ⟨p,hp,w,?_⟩
    change localFieldEquiv n x y hs.left (f*g) = φ (w : AffineLocal n x y hs.left) * (φ p)^(a+b)
    rw [map_mul, he, hd]
    exact hw

/-- Monicity at O is stronger than the local order there: after
removal of the exact signed power of t, the same function is a
quotient of two actual chart terms, each evaluating to exactly one. -/
def HasMonicOrigin (n : K) (f : OriginalFunctionField n) (k : ℤ) : Prop :=
  ∃ N D : InfinityChart n, originEvaluation n N = 1 ∧ originEvaluation n D = 1 ∧
    (originT n)^(-k) * originalNativeFunctionFieldEquiv n f =
      chartFieldMap n N / chartFieldMap n D

private theorem monic_origin_one (n : K) : HasMonicOrigin n 1 0 := by
  refine ⟨1,1,map_one _,map_one _,?_⟩
  simp only [neg_zero, zpow_zero, map_one, one_mul, div_one]

theorem monic_origin_nonzero (n : K) {f : OriginalFunctionField n} {k : ℤ}
    (h : HasMonicOrigin n f k) : f ≠ 0 := by
  obtain ⟨N,D,hN,hD,h⟩ := h
  have hN₀ : chartFieldMap n N ≠ 0 :=
    ((origin_one_local_unit n N hN).map (infinityFractionMap n)).ne_zero
  have hD₀ : chartFieldMap n D ≠ 0 :=
    ((origin_one_local_unit n D hD).map (infinityFractionMap n)).ne_zero
  intro hf
  apply div_ne_zero hN₀ hD₀
  rw [← h,hf,map_zero,mul_zero]

theorem monic_origin_mul (n : K) {f g : OriginalFunctionField n} {a b : ℤ}
    (hf : HasMonicOrigin n f a) (hg : HasMonicOrigin n g b) :
    HasMonicOrigin n (f*g) (a+b) := by
  obtain ⟨N,D,hN,hD,hf⟩ := hf
  obtain ⟨N',D',hN',hD',hg⟩ := hg
  refine ⟨N*N',D*D',by rw [map_mul,hN,hN',one_mul],
    by rw [map_mul,hD,hD',one_mul],?_⟩
  have ht : originT n ≠ 0 := neg_ne_zero.mpr (actual_infinity_fraction_u_nonzero n)
  rw [show -(a+b) = -a + -b by abel, zpow_add₀ ht,
    map_mul, map_mul, map_mul, ← div_mul_div_comm]
  calc
    (originT n)^(-a) * (originT n)^(-b) *
        (originalNativeFunctionFieldEquiv n f * originalNativeFunctionFieldEquiv n g) =
      ((originT n)^(-a) * originalNativeFunctionFieldEquiv n f) *
        ((originT n)^(-b) * originalNativeFunctionFieldEquiv n g) := by ac_rfl
    _ = _ := by rw [hf,hg]

theorem one_monic_step (n : K) (P Q : Point n) :
    HasMonicOrigin n (millerFunction n P Q) (geometricDivisor n P Q 0) := by
  cases P with
  | zero =>
    have h : geometricDivisor n 0 Q = 0 := by
      simp only [geometricDivisor, zero_add] <;> abel
    simpa only [millerFunction, h, Finsupp.zero_apply] using monic_origin_one n
  | some x y hP =>
    let P : Point n := .some x y hP
    cases Q with
    | zero =>
      have h : geometricDivisor n P 0 = 0 := by
        simp only [geometricDivisor, add_zero] <;> abel
      change HasMonicOrigin n 1 (geometricDivisor n P 0 0)
      simpa only [h, Finsupp.zero_apply] using monic_origin_one n
    | some x' y' hQ =>
      let Q : Point n := .some x' y' hQ
      have hPo : P ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero hP
      have hQo : Q ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero hQ
      change HasMonicOrigin n (millerFunction n P Q) (geometricDivisor n P Q 0)
      by_cases hv : x = x' ∧ y = (curve n).toAffine.negY x' y'
      · have hf : millerFunction n P Q = rootFunction n x := by
          simp only [P,Q,millerFunction,if_pos hv]
        have hS : P + Q = 0 := WeierstrassCurve.Affine.Point.add_of_Y_eq hv.1 hv.2
        have hk : geometricDivisor n P Q 0 = -2 := by
          simp only [geometricDivisor,hS,Finsupp.add_apply,Finsupp.sub_apply,
            Finsupp.single_eq_of_ne' hPo,Finsupp.single_eq_of_ne' hQo,
            Finsupp.single_eq_same] <;> norm_num
        rw [hf,hk]
        obtain ⟨h,hD⟩ := actual_vertical_miller_origin n x
        refine ⟨clearedDenominator n x,1,hD,map_one _,?_⟩
        simpa only [neg_neg,zpow_natCast,map_one,div_one] using h
      · let W := (curve n).toAffine
        let a := W.slope x x' y y'
        let z := W.addX x x' a
        have hf : millerFunction n P Q = nonverticalFunction n x y a z := by
          simp only [P,Q,millerFunction,if_neg hv,W,a,z]
        have hS : P + Q ≠ 0 := by
          rw [WeierstrassCurve.Affine.Point.add_some hv]
          exact WeierstrassCurve.Affine.Point.some_ne_zero _
        have hk : geometricDivisor n P Q 0 = -1 := by
          simp only [geometricDivisor,Finsupp.add_apply,Finsupp.sub_apply,
            Finsupp.single_eq_of_ne' hPo,Finsupp.single_eq_of_ne' hQo,
            Finsupp.single_eq_of_ne' hS,Finsupp.single_eq_same] <;> norm_num
        rw [hf,hk]
        obtain ⟨h,hN,hD⟩ := actual_nonvertical_miller_origin n x y a z
        refine ⟨clearedNumerator n x y a,clearedDenominator n z,hN,hD,?_⟩
        simpa only [neg_neg,zpow_one] using h

private def marker (n : K) (P : Point n) : Point n →₀ ℤ := Finsupp.single P 1

/-- The partial divisor is m([P]-[O])+[O]-[[m]P].  In particular
the missing [m]P is not replaced by O before assuming actual torsion. -/
def partialDivisor (n : K) (P : Point n) (m : ℕ) : Point n →₀ ℤ :=
  m • (marker n P - marker n 0) + marker n 0 - marker n (m • P)

theorem partial_divisor_zero (n : K) (P : Point n) : partialDivisor n P 0 = 0 := by
  simp [partialDivisor]

theorem partial_divisor_one (n : K) (P : Point n) : partialDivisor n P 1 = 0 := by
  simp only [partialDivisor, one_nsmul] <;> abel

theorem partial_divisor_add (n : K) (P : Point n) (r s : ℕ) :
    partialDivisor n P (r+s) =
      partialDivisor n P r + partialDivisor n P s + geometricDivisor n (r • P) (s • P) := by
  simp only [partialDivisor, geometricDivisor, marker, add_nsmul] <;> abel

theorem partial_divisor_torsion (n : K) (P : Point n) (m : ℕ) (hP : m • P = 0) :
    partialDivisor n P m = m • (Finsupp.single P 1 - Finsupp.single 0 1) := by
  simp only [partialDivisor, hP, add_sub_cancel_right, marker]

def Certificate (n : K) (P : Point n) (m : ℕ) (f : OriginalFunctionField n) : Prop :=
  (∀ R : Point n, HasGeometricOrder n f R (partialDivisor n P m R)) ∧
  HasMonicOrigin n f (partialDivisor n P m 0)

private theorem certificate_one (n : K) (hn : n ≠ 0) (P : Point n) :
    Certificate n P 1 1 := by
  have h : geometricDivisor n (0 : Point n) 0 = 0 := by
    simp only [geometricDivisor,zero_add] <;> abel
  constructor
  · intro R
    have hs := geometric_divisor_agrees n hn 0 0 R
    simpa only [millerFunction,h,partial_divisor_one,Finsupp.zero_apply] using hs
  · simpa only [partial_divisor_one,Finsupp.zero_apply] using monic_origin_one n

/-- The fundamental addition-chain composition. The two product
factors and one actual signed line are the functions used, not
arbitrary representatives of linear-equivalence classes. -/
theorem certificate_add (n : K) (hn : n ≠ 0) (P : Point n) {r s : ℕ}
    {f g : OriginalFunctionField n} (hf : Certificate n P r f)
    (hg : Certificate n P s g) :
    Certificate n P (r+s) (f * g * millerFunction n (r • P) (s • P)) := by
  constructor
  · intro R
    rw [partial_divisor_add,Finsupp.add_apply,Finsupp.add_apply]
    exact geometric_order_mul n hn (geometric_order_mul n hn (hf.1 R) (hg.1 R))
      (geometric_divisor_agrees n hn (r • P) (s • P) R)
  · rw [partial_divisor_add,Finsupp.add_apply,Finsupp.add_apply]
    exact monic_origin_mul n (monic_origin_mul n hf.2 hg.2)
      (one_monic_step n (r • P) (s • P))

/-- A fixed finite product for all m. Use certificate_add directly for
faster addition chains (in particular doubling), with the same signs. -/
def millerProduct (n : K) (P : Point n) : ℕ → OriginalFunctionField n
  | 0 => 1
  | m+1 => millerProduct n P m * millerFunction n (m • P) P

theorem miller_product_certificate (n : K) (hn : n ≠ 0) (P : Point n) (m : ℕ) :
    Certificate n P m (millerProduct n P m) := by
  induction m with
  | zero =>
    have h : geometricDivisor n (0 : Point n) 0 = 0 := by
      simp only [geometricDivisor,zero_add] <;> abel
    constructor
    · intro R
      have hs := geometric_divisor_agrees n hn 0 0 R
      simpa only [millerProduct,millerFunction,h,partial_divisor_zero,Finsupp.zero_apply] using hs
    · simpa only [millerProduct,partial_divisor_zero,Finsupp.zero_apply] using monic_origin_one n
  | succ m hm =>
    have hs := certificate_add n hn P hm (certificate_one n hn P)
    simpa only [millerProduct,one_nsmul,mul_one] using hs

/-- The actual O(k)-step dyadic chain for m=2^k, the levels
used by the higher 2-primary pairing. -/
def millerDyadic (n : K) (P : Point n) : ℕ → OriginalFunctionField n
  | 0 => 1
  | k+1 => millerDyadic n P k * millerDyadic n P k *
      millerFunction n ((2^k : ℕ) • P) ((2^k : ℕ) • P)

theorem miller_dyadic_certificate (n : K) (hn : n ≠ 0) (P : Point n) (k : ℕ) :
    Certificate n P (2^k) (millerDyadic n P k) := by
  induction k with
  | zero => simpa only [pow_zero,millerDyadic] using certificate_one n hn P
  | succ k hk =>
    rw [show (2^(k+1) : ℕ) = 2^k + 2^k by rw [pow_succ,Nat.mul_two]]
    simpa only [millerDyadic] using certificate_add n hn P hk hk

theorem miller_dyadic_torsion (n : K) (hn : n ≠ 0) (P : Point n) (k : ℕ)
    (hP : (2^k : ℕ) • P = 0) :
    let D : Point n →₀ ℤ := (2^k : ℕ) • (Finsupp.single P 1 - Finsupp.single 0 1)
    (∀ R : Point n, HasGeometricOrder n (millerDyadic n P k) R (D R)) ∧
      HasMonicOrigin n (millerDyadic n P k) (D 0) := by
  have hs := miller_dyadic_certificate n hn P k
  simpa only [Certificate,partial_divisor_torsion n P (2^k) hP] using hs

/-- At actual m-torsion, both the divisor and leading coefficient
of the literal fixed product are certified. No disjoint-support
assumption excludes coincident factors or intermediate verticals. -/
theorem miller_product_torsion (n : K) (hn : n ≠ 0) (P : Point n) (m : ℕ)
    (hP : m • P = 0) :
    let D : Point n →₀ ℤ := m • (Finsupp.single P 1 - Finsupp.single 0 1)
    (∀ R : Point n, HasGeometricOrder n (millerProduct n P m) R (D R)) ∧
      HasMonicOrigin n (millerProduct n P m) (D 0) := by
  have hs := miller_product_certificate n hn P m
  simpa only [Certificate,partial_divisor_torsion n P m hP] using hs

end ActualMillerProduct318
