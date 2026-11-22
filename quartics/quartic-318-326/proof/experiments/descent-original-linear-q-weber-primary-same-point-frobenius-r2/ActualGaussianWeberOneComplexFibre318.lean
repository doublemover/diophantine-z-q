module
public import ActualGaussianWeberComplexFibreSeed318
public import ActualGaussianWeberArcFunctionEmbedding318
public import ActualGaussianWeberOddNormGeneric318
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public section
noncomputable section

namespace ActualGaussianWeberOneComplexFibre318

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open ActualGaussianWeberHenselianPointMap318 ActualGaussianWeberPlaceEquivariance318
open ActualGaussianWeberStockCoordinateHom318 ActualGaussianWeberGaussianScalarSpecialization318
open ActualGaussianWeberQuadraticGenericChart318 ActualGaussianWeberGaussLocalization318
open ActualGaussianWeberTranslationFunctionField318 ActualGaussianWeberOddNormGeneric318
open ActualGaussianWeberArcFunctionEmbedding318 ActualGaussianWeberComplexFibreSeed318

variable {K : Type*} [Field K] [Algebra K ℂ]
variable [DecidableEq (FunctionField K)] [DecidableEq ℂ]

/-- Zero at infinity only as a totalized coordinate. All points chosen
to inject one inverse abscissa into the fibre are actual affine points. -/
@[expose] def xCoord : WP ℂ → ℂ
  | Point.zero => 0
  | Point.some x _ _ => x

private theorem xCoord_neg (P : WP ℂ) : xCoord (-P) = xCoord P := by
  cases P with
  | zero => rfl
  | some x y h => rw [Point.neg_some] <;> rfl

private theorem square_sign {z w : ℂ} (h : z^2 = w^2) : z = w ∨ z = -w := by
  have hs : (z-w)*(z+w)=0 := by
    calc
      _ = z^2-w^2 := by ring
      _ = 0 := sub_eq_zero.mpr h
  rcases mul_eq_zero.mp hs with hs|hs
  · exact Or.inl (sub_eq_zero.mp hs)
  · exact Or.inr (by linear_combination hs)

/-- At a transcendental complex inverse abscissa, it is legitimate to
push the original *generic* point relation directly into the complex
curve. No Laurent arc, local coordinate choice, or continuity is used. -/
private theorem actual_image_at_root
    (hK : (2 : K) ≠ 0) (hC : (2 : ℂ) ≠ 0) (i : K) (hi : i^2 = -1) (a b : ℤ)
    (A B : K[X]) (hAB : IsCoprime A B)
    (u v : FunctionField K) (huv : (curve (FunctionField K)).toAffine.Nonsingular u v)
    (hGen : gaussian (function_two_ne K hK) (constGeneric K i)
        (by simpa only [map_pow,map_neg,map_one] using congrArg (constGeneric K) hi)
        a b (genericPoint K hK) = Point.some u v huv)
    (hRat : u = fractionMap K (AdjoinRoot.of (relation K) A) /
        fractionMap K (AdjoinRoot.of (relation K) B))
    (c x y : ℂ) (hc : Transcendental K c)
    (hx : A.eval₂ (algebraMap K ℂ) x = c * B.eval₂ (algebraMap K ℂ) x)
    (hy : y^2 = x^3 - x) :
    let f := algebraMap K ℂ
    let hj : (f i)^2 = -1 := by
      simpa only [map_pow,map_neg,map_one] using congrArg f hi
    let G := gaussian hC (f i) hj a b
    ∃ z : ℂ, ∃ hZ : (curve ℂ).toAffine.Nonsingular c z,
      G (Point.some x y (nonsing_of_equation hC hy)) = Point.some c z hZ := by
  dsimp only
  let f := algebraMap K ℂ
  obtain ⟨hb,hinj⟩ := fibre_root_transcendental A B hAB hc hx
  let m := arcEmbedding f x y hy hinj
  let hF := function_two_ne K hK
  let F := coordinateHom m hC
  let j := constGeneric K i
  have hj : j^2 = -1 := by
    simpa only [j,map_pow,map_neg,map_one] using congrArg (constGeneric K) hi
  have hiC : (f i)^2 = -1 := by
    simpa only [map_pow,map_neg,map_one] using congrArg f hi
  let G := gaussian hC (f i) hiC a b
  let hT := nonsing_of_equation hF (equation_generic K)
  let hP := nonsing_of_equation hC hy
  let hUV := mapped_nonsingular m hC huv
  have hTmap : F (genericPoint K hK) = Point.some x y hP := by
    change onCurvePoint m hC (Point.some (xGeneric K) (yGeneric K) hT) = _
    rw [point_some m hC hT]
    exact some_congr (arcEmbedding_x f x y hy hinj) (arcEmbedding_y f x y hy hinj)
  have hScalar : F (gaussian hF j hj a b (genericPoint K hK)) =
      G (F (genericPoint K hK)) :=
    coordinate_gaussian m hF hC j (f i) hj hiC (arcEmbedding_const f x y hy hinj i)
      a b (genericPoint K hK)
  have hMapped : F (Point.some u v huv) = Point.some (m u) (m v) hUV :=
    point_some m hC huv
  have hExact : G (Point.some x y hP) = Point.some (m u) (m v) hUV := by
    calc
      _ = G (F (genericPoint K hK)) := congrArg G hTmap.symm
      _ = F (gaussian hF j hj a b (genericPoint K hK)) := hScalar.symm
      _ = F (Point.some u v huv) := congrArg F hGen
      _ = _ := hMapped
  have hX : m u = c := by
    calc
      _ = m (fractionMap K (AdjoinRoot.of (relation K) A)) /
          m (fractionMap K (AdjoinRoot.of (relation K) B)) := by rw [hRat,map_div₀]
      _ = A.eval₂ f x / B.eval₂ f x := by
        rw [arcEmbedding_polynomial f x y hy hinj A,
            arcEmbedding_polynomial f x y hy hinj B]
      _ = c := (div_eq_iff hb).mpr hx
  have hZ : (curve ℂ).toAffine.Nonsingular c (m v) := by
    rw [←hX]
    exact hUV
  exact ⟨m v,hZ,hExact.trans (some_congr hX rfl)⟩

/-- Count the distinct roots by injecting them into **one** actual
fibre of the original complex Gaussian map. Given the true complex
point-fibre size for this same map, this does not assume a rational
map degree or a bound on a different map. The chosen image Q has the
fixed, supplied transcendental abscissa c. -/
theorem roots_embed_and_card_le
    (hK : (2 : K) ≠ 0) (hC : (2 : ℂ) ≠ 0) (i : K) (hi : i^2 = -1) (a b : ℤ)
    (A B : K[X]) (hAB : IsCoprime A B)
    (u v : FunctionField K) (huv : (curve (FunctionField K)).toAffine.Nonsingular u v)
    (hGen : gaussian (function_two_ne K hK) (constGeneric K i)
        (by simpa only [map_pow,map_neg,map_one] using congrArg (constGeneric K) hi)
        a b (genericPoint K hK) = Point.some u v huv)
    (hRat : u = fractionMap K (AdjoinRoot.of (relation K) A) /
        fractionMap K (AdjoinRoot.of (relation K) B))
    (c : ℂ) (hc : Transcendental K c) (n : ℕ)
    (torus :
      let f := algebraMap K ℂ
      let hj : (f i)^2 = -1 := by
        simpa only [map_pow,map_neg,map_one] using congrArg f hi
      let G := gaussian hC (f i) hj a b
      ∀ Q : WP ℂ, Finite {P : WP ℂ // G P = Q} ∧ Nat.card {P : WP ℂ // G P = Q} = n) :
    let f := algebraMap K ℂ
    let hj : (f i)^2 = -1 := by
      simpa only [map_pow,map_neg,map_one] using congrArg f hi
    let G := gaussian hC (f i) hj a b
    let R := ((A.map f) - C c * (B.map f)).roots.toFinset
    ∃ Q : WP ℂ, xCoord Q = c ∧
      Nonempty (↥R ↪ {P : WP ℂ // G P = Q}) ∧ R.card ≤ n := by
  classical
  let f := algebraMap K ℂ
  have hj : (f i)^2 = -1 := by
    simpa only [map_pow,map_neg,map_one] using congrArg f hi
  let G := gaussian hC (f i) hj a b
  let H := A.map f - C c * B.map f
  let R := H.roots.toFinset
  change ∃ Q : WP ℂ, xCoord Q = c ∧
    Nonempty (↥R ↪ {P : WP ℂ // G P = Q}) ∧ R.card ≤ n
  obtain ⟨w,hw⟩ := IsAlgClosed.exists_pow_nat_eq (c^3-c) (by decide : 0 < (2:ℕ))
  let hQ := nonsing_of_equation hC hw
  let hNQ := nonsing_of_equation hC ((neg_sq w).trans hw)
  let Q : WP ℂ := Point.some c w hQ
  have hNegQ : -Q = Point.some c (-w) hNQ := by
    change -(Point.some c w hQ) = _
    rw [Point.neg_some]
    exact some_congr rfl (ActualGaussianWeberOrdinarySlope318.literal_negY ℂ c w)
  have produce (x : ↥R) : ∃ S : WP ℂ, xCoord S = x.val ∧ G S = Q := by
    have hroots : x.val ∈ H.roots := Multiset.mem_toFinset.mp x.property
    have hH : H ≠ 0 := by
      intro he
      have hzero : x.val ∈ (0 : Multiset ℂ) := by simpa only [he,roots_zero] using hroots
      exact (by simp : x.val ∉ (0 : Multiset ℂ)) hzero
    have he := (Polynomial.mem_roots hH).mp hroots
    have hx : A.eval₂ f x.val = c * B.eval₂ f x.val := by
      apply sub_eq_zero.mp
      simpa only [H,IsRoot,eval_sub,eval_mul,eval_C,eval_map] using he
    obtain ⟨y,hy⟩ := IsAlgClosed.exists_pow_nat_eq (x.val^3-x.val) (by decide : 0 < (2:ℕ))
    let P : WP ℂ := Point.some x.val y (nonsing_of_equation hC hy)
    obtain ⟨z,hZ,hP⟩ := actual_image_at_root hK hC i hi a b A B hAB u v huv hGen hRat
      c x.val y hc hx hy
    have hM : G P = Point.some c z hZ := hP
    have hSq : z^2 = w^2 := ((literal_equation c z).mp hZ.1).trans hw.symm
    rcases square_sign hSq with h|h
    · exact ⟨P,rfl,hM.trans (some_congr rfl h)⟩
    · have hOpp : G P = -Q := hM.trans ((some_congr rfl h).trans hNegQ.symm)
      refine ⟨-P,?_,?_⟩
      · change xCoord (-P) = xCoord P
        exact xCoord_neg P
      · rw [map_neg,hOpp,neg_neg]
  let P (x : ↥R) := Classical.choose (produce x)
  have hPx (x : ↥R) : xCoord (P x) = x.val := (Classical.choose_spec (produce x)).1
  have hPg (x : ↥R) : G (P x) = Q := (Classical.choose_spec (produce x)).2
  let E : ↥R ↪ {P : WP ℂ // G P = Q} :=
    ⟨fun x => ⟨P x,hPg x⟩,by
      intro x y h
      apply Subtype.ext
      have h' := congrArg (fun P : {P : WP ℂ // G P = Q} => xCoord P.val) h
      exact (hPx x).symm.trans (h'.trans (hPx y))⟩
  have hT := torus Q
  letI : Finite {P : WP ℂ // G P = Q} := hT.1
  have hBound := Nat.card_le_card_of_injective E E.injective
  have hSize : Nat.card (↥R) = R.card := by rw [Nat.card_eq_fintype_card,Fintype.card_coe]
  have hFibre : Nat.card {P : WP ℂ // G P = Q} = n := hT.2
  rw [hSize,hFibre] at hBound
  exact ⟨Q,rfl,⟨E⟩,hBound⟩

end ActualGaussianWeberOneComplexFibre318
