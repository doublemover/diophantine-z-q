module
public import ActualGaussianWeberNoArcFiniteGenericScalar318
public import ActualGaussianWeberOriginalAbscissaHeight318
public import ActualGaussianWeberNormalizedAbscissaDegree318
public import Mathlib.FieldTheory.RatFunc.Basic
public section
noncomputable section

namespace ActualGaussianWeberChosenResidualDescriptor318

open IsLocalRing Polynomial WeierstrassCurve WeierstrassCurve.Affine
open ActualGaussianWeberHenselianPointMap318 ActualGaussianWeberPlaceEquivariance318
open ActualGaussianWeberStockCoordinateHom318 ActualGaussianWeberReductionCoordinates318
open ActualGaussianWeberPrimitiveRational318 ActualGaussianWeberQuadraticGenericChart318
open ActualGaussianWeberGaussLocalization318 ActualGaussianWeberGaussValuation318
open ActualGaussianWeberNoArcFiniteGenericScalar318 ActualGaussianWeberStockReductionAdd318
open ActualGaussianWeberGaussianScalarSpecialization318 ActualGaussianWeberQuarterTurn318
open ActualGaussianWeberOddNormGeneric318 ActualGaussianWeberTranslationFunctionField318
open ActualGaussianWeberNormalizedAbscissaDegree318
open ActualGaussianWeberSelectedGaussianPrime318 ActualGaussianWeberOriginalAbscissaHeight318

variable {k : Type*} [Field k]

private def polynomialImage : k[X] →+* FunctionField k :=
  (fractionMap k).comp (AdjoinRoot.of (relation k))

private theorem polynomialImage_injective :
    Function.Injective (polynomialImage (k:=k)) := by
  have hM : (relation k).Monic := monic_X_pow_sub_C _ (by decide)
  have hD : 0 < (relation k).degree := by
    rw [show (relation k).degree=2 from degree_X_pow_sub_C (by decide : 0<2) _]
    decide
  intro A B h
  have hF : fractionMap k (AdjoinRoot.of (relation k) A)=
      fractionMap k (AdjoinRoot.of (relation k) B) := h
  exact AdjoinRoot.of.injective_of_monic_of_degree_pos hM hD (fractionMap_injective k hF)

private theorem polynomialImage_ne {A : k[X]} (hA : A≠0) :
    polynomialImage A≠0 := by
  intro h
  exact hA (polynomialImage_injective (h.trans (map_zero (polynomialImage (k:=k))).symm))

/-- Normalization over the residue field itself, after specialization.
The single cross multiplication uses the same polynomial embedding in
both denominators; no lift from an uncompiled characteristic-zero
reflection owner is needed. -/
private theorem canonical_ratio_image (A B : k[X]) (hB : B≠0) :
    let r := RatFunc.mk A B
    polynomialImage A/polynomialImage B=polynomialImage r.num/polynomialImage r.denom := by
  let r := RatFunc.mk A B
  have hr : r.num * B = A * r.denom :=
    (RatFunc.num_mul_eq_mul_denom_iff hB).mpr (RatFunc.mk_eq_div A B)
  change polynomialImage A/polynomialImage B=polynomialImage r.num/polynomialImage r.denom
  apply (div_eq_div_iff (polynomialImage_ne hB) (polynomialImage_ne (RatFunc.denom_ne_zero r))).2
  simpa only [map_mul] using congrArg (polynomialImage (k:=k)) hr.symm

private theorem abscissa_eq {F : Type*} [Field F] {x y z w : F}
    {h : (curve F).toAffine.Nonsingular x y} {h' : (curve F).toAffine.Nonsingular z w}
    (e : Point.some x y h=Point.some z w h') : x=z :=
  congrArg (fun P : WP F => match P with | .zero => 0 | .some u _ _ => u) e

variable {K : Type*} [Field K] (V : ValuationSubring K)
variable [DecidableEq (FunctionField K)] [DecidableEq (FunctionField (ResidueField V))]
variable [DecidableEq (ResidueField (gauss V))]

/-- The same actual residual Gaussian point has the canonical residual
coprime ratio of its own abscissa. The input r has the canonical
characteristic-zero pair for the stated finite scalar. First produce the
actual primitive Gauss representative at this place, then normalize
its reduction, rather than reducing an already simplified expression
with a possibly vanishing denominator. -/
theorem same_point_capped_residual_abscissa
    (hK : (2:K)≠0) (h2 : (2:ResidueField V)≠0)
    (i : V) (hi : i^2 = -1) (a b p : ℤ) (hNorm : a^2+b^2=p) (hOdd : Odd p)
    (r : RatFunc K) (cap : ℕ) (hCap : max r.num.natDegree r.denom.natDegree ≤ cap)
    (x y : FunctionField K)
    (hxy : (curve (FunctionField K)).toAffine.Nonsingular x y)
    (hInput : gaussian (function_two_ne K hK) (constGeneric K (V.subtype i))
      (by simpa only [map_pow,map_neg,map_one] using
        congrArg (constGeneric K) (chosen_square_generic V i hi))
      a b (genericPoint K hK)=Point.some x y hxy)
    (hRat : x=fractionMap K (AdjoinRoot.of (relation K) r.num) /
      fractionMap K (AdjoinRoot.of (relation K) r.denom)) :
    let k := ResidueField V
    let j := residue V i
    let hj := chosen_square_residue V i hi
    ∃ u v : FunctionField k, ∃ h : (curve (FunctionField k)).toAffine.Nonsingular u v,
      gaussian (function_two_ne k h2) (constGeneric k j)
        (by simpa only [map_pow,map_neg,map_one] using congrArg (constGeneric k) hj)
        a b (genericPoint k h2)=Point.some u v h ∧
      ∃ D : PrimitivePair V r.num r.denom,
        D.den.map (residue V) ≠ 0 ∧
        let R := RatFunc.mk (D.num.map (residue V)) (D.den.map (residue V))
        IsCoprime R.num R.denom ∧ R.denom≠0 ∧
        R.num.natDegree ≤ r.num.natDegree ∧ R.denom.natDegree ≤ r.denom.natDegree ∧
        max R.num.natDegree R.denom.natDegree ≤ cap ∧
        u=fractionMap k (AdjoinRoot.of (relation k) R.num) /
          fractionMap k (AdjoinRoot.of (relation k) R.denom) := by
  classical
  let k := ResidueField V
  let W := gauss V
  let J := integral_i V i
  let hJ := integral_i_sq V i hi
  let hF := function_two_ne K hK
  let hR := gauss_two_ne V h2
  let hS := function_two_ne k h2
  let F := gaussResidue V
  let C := coordinateHom F.toRingHom hS
  let P := gaussian hF (W.subtype J) (chosen_square_generic W J hJ) a b (genericPoint K hK)
  obtain ⟨xg,yg,hg,hP,hxg,z,hz⟩ :=
    scalar_generic_reduces_finite V hK h2 i hi a b p hNorm hOdd
  have hPg : P=Point.some xg yg hg := hP
  have hCoefficient (u v : FunctionField K) (hu : u^2= -1) (hv : v^2= -1)
      (e : u=v) :
      gaussian hF u hu a b (genericPoint K hK)=
        gaussian hF v hv a b (genericPoint K hK) := by
    subst v
    rfl
  have hPi : P=Point.some x y hxy :=
    (hCoefficient _ _ _ _ (integral_i_generic V i)).trans hInput
  have hSame : xg=x := abscissa_eq (hPg.symm.trans hPi)
  have hLocalRatio : intoGeneric V z=
      algebraMap (Chart K) (FunctionField K) (AdjoinRoot.of (relation K) r.num) /
      algebraMap (Chart K) (FunctionField K) (AdjoinRoot.of (relation K) r.denom) :=
    hz.trans (hSame.trans hRat)
  obtain ⟨D,hDen,hAcap,hBcap,hRes⟩ := specialize_local_rational_coordinate V r.num r.denom
    (RatFunc.denom_ne_zero r) cap ((le_max_left _ _).trans hCap) ((le_max_right _ _).trans hCap)
    z hLocalRatio

  let x₀ : W := ⟨xg,hxg⟩
  let y₀ : W := ⟨yg,integral_y W ((literal_equation xg yg).mp hg.1) hxg⟩
  obtain ⟨hxy₀,hr⟩ := reduction_through_coordinates W hR hg x₀ y₀ rfl rfl
  let u := F (residue W x₀)
  let v := F (residue W y₀)
  let huv := mapped_nonsingular F.toRingHom hS hxy₀
  have hReduced : C (specialize W hR P)=Point.some u v huv := by
    rw [hPg,hr]
    exact point_some F.toRingHom hS hxy₀

  let i₀ := constGeneric k (residue V i)
  have hi₀ : i₀^2= -1 := by
    simpa only [i₀,map_pow,map_neg,map_one] using
      congrArg (constGeneric k) (chosen_square_residue V i hi)
  let G := gaussian hS i₀ hi₀ a b
  have hspec : specializeHom W hF hR P =
      gaussian hR (residue W J) (chosen_square_residue W J hJ) a b
        (specializeHom W hF hR (genericPoint K hK)) := by
    letI : DecidableEq (ResidueField (gauss (gauss V))) := Classical.decEq _
    exact specialize_scalar_core W hF hR J hJ a b (genericPoint K hK)
  have hspec' : specialize W hR P=
      gaussian hR (residue W J) (chosen_square_residue W J hJ) a b
        (specialize W hR (genericPoint K hK)) := hspec
  have hScalar : C (specialize W hR P)=G (genericPoint k h2) := by
    rw [hspec']
    calc
      _ = G (C (specialize W hR (genericPoint K hK))) :=
        coordinate_gaussian F.toRingHom hR hS _ _ _ hi₀ (integral_i_residue V i) a b _
      _ = _ := congrArg G (generic_point_specializes V hK h2)
  have hGen : G (genericPoint k h2)=Point.some u v huv :=
    hScalar.symm.trans hReduced

  have hZ : localEquiv V z=x₀ := by
    apply W.subtype_injective
    change intoGeneric V z=xg
    exact hz
  let A := D.num.map (residue V)
  let B := D.den.map (residue V)
  have hVal : u=polynomialImage A/polynomialImage B := by
    change F (residue W x₀)=_
    rw [←hZ,gauss_residue_of_local]
    exact hRes
  let R := RatFunc.mk A B
  obtain ⟨hNA,hNB⟩ := normalize_both_degrees A B hDen
  have hAB : A.natDegree ≤ r.num.natDegree := natDegree_map_le.trans D.num_degree
  have hBB : B.natDegree ≤ r.denom.natDegree := natDegree_map_le.trans D.den_degree
  exact ⟨u,v,huv,hGen,D,hDen,RatFunc.isCoprime_num_denom R,RatFunc.denom_ne_zero R,
    hNA.trans hAB,hNB.trans hBB,max_le_iff.mpr ⟨hNA.trans hAcap,hNB.trans hBcap⟩,
    hVal.trans (canonical_ratio_image A B hDen)⟩

section Selected
attribute [local instance] Classical.decEq

theorem residue_two_ne_at_odd_selected_prime {p : ℕ} [Fact p.Prime]
    (hOdd : Odd (p : ℤ)) (j : ZMod p) (hj : j ^ 2 = -1) :
    (2 : ResidueField (BasePlace j hj)) ≠ 0 := by
  intro h
  have h₂ : (2 : ZMod p) = 0 := by
    simpa only [map_ofNat,map_zero] using congrArg (residueEquiv j hj) h
  have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h₂
  have hEq : p = 2 :=
    le_antisymm (Nat.le_of_dvd (by decide) hd) (Fact.out : p.Prime).two_le
  obtain ⟨n, hn⟩ := hOdd
  rw [hEq] at hn
  norm_num at hn <;> omega

private theorem scalar_congr_at_root {K : Type*} [Field K] [DecidableEq K]
    (hK : (2 : K) ≠ 0) {i j : K} (hi : i ^ 2 = -1) (hj : j ^ 2 = -1)
    (e : i = j) (a b : ℤ) :
    gaussian hK i hi a b = gaussian hK j hj a b := by
  subst j
  rfl

/-- The original norm-p scalar on the formalized Gaussian base and on
its actual signed residue field. The checked Height theorem supplies
one original point and normalized quotient. The same quotient gives
both reduced degree bounds: callers supply neither a second original
witness, a residual cap, nor an origin-pole or derivative fact. -/
theorem actual_selected_descriptor {p : ℕ} [Fact p.Prime]
    (hOdd : Odd (p : ℤ)) (a b : ℤ) (hN : a ^ 2 + b ^ 2 = (p : ℤ)) :
    let j := rootOf (p := p) a b
    let hj := rootOf_sq (p := p) a b hN
    let V := BasePlace j hj
    let k := ResidueField V
    let i := integralI j hj
    let i₀ := residue V i
    let hK := base_two_ne
    let hR := residue_two_ne_at_odd_selected_prime hOdd j hj
    ∃ (x y : FunctionField Base), ∃ hxy : (curve (FunctionField Base)).toAffine.Nonsingular x y,
      gaussian (function_two_ne Base hK) (constGeneric Base originalI)
        (by simpa only [map_pow,map_neg,map_one] using congrArg (constGeneric Base) originalI_sq)
        a b (genericPoint Base hK) = Point.some x y hxy ∧
      ∃ r : RatFunc Base,
        x = fractionMap Base (AdjoinRoot.of (relation Base) r.num) /
          fractionMap Base (AdjoinRoot.of (relation Base) r.denom) ∧
        max r.num.natDegree r.denom.natDegree ≤ p ∧
        ∃ (u v : FunctionField k), ∃ huv : (curve (FunctionField k)).toAffine.Nonsingular u v,
          gaussian (function_two_ne k hR) (constGeneric k i₀)
            (by
              simpa only [map_pow,map_neg,map_one] using congrArg (constGeneric k)
                (chosen_square_residue V i (integralI_sq j hj)))
            a b (genericPoint k hR) = Point.some u v huv ∧
          ∃ D : PrimitivePair V r.num r.denom,
            D.den.map (residue V) ≠ 0 ∧
            let R := RatFunc.mk (D.num.map (residue V)) (D.den.map (residue V))
            IsCoprime R.num R.denom ∧ R.denom ≠ 0 ∧
            R.num.natDegree ≤ r.num.natDegree ∧ R.denom.natDegree ≤ r.denom.natDegree ∧
            max R.num.natDegree R.denom.natDegree ≤ p ∧
            u = fractionMap k (AdjoinRoot.of (relation k) R.num) /
              fractionMap k (AdjoinRoot.of (relation k) R.denom) := by
  let j := rootOf (p := p) a b
  let hj := rootOf_sq (p := p) a b hN
  let V := BasePlace j hj
  let i := integralI j hj
  let hi := integralI_sq j hj
  let hF := function_two_ne Base base_two_ne
  let hR := residue_two_ne_at_odd_selected_prime hOdd j hj
  have hSame : V.subtype i = originalI :=
    complexEmbedding.injective ((complexEmbedding_integralI j hj).trans complexEmbedding_i.symm)
  obtain ⟨x,y,hxy,hGen,r,_,_,hRat,hCap⟩ :=
    original_abscissa_height_at_most_prime p (Fact.out : p.Prime) hOdd a b hN
  have hRat' : x = fractionMap Base (AdjoinRoot.of (relation Base) r.num) /
      fractionMap Base (AdjoinRoot.of (relation Base) r.denom) := hRat
  let c₁ := constGeneric Base (V.subtype i)
  let c₂ := constGeneric Base originalI
  have h₁ : c₁ ^ 2 = -1 := by
    simpa only [map_pow,map_neg,map_one] using
      congrArg (constGeneric Base) (chosen_square_generic V i hi)
  have h₂ : c₂ ^ 2 = -1 := by
    simpa only [map_pow,map_neg,map_one] using congrArg (constGeneric Base) originalI_sq
  have hE : gaussian hF c₁ h₁ a b = gaussian hF c₂ h₂ a b :=
    scalar_congr_at_root hF h₁ h₂ (congrArg (constGeneric Base) hSame) a b
  have hInput : gaussian hF c₁ h₁ a b (genericPoint Base base_two_ne) = Point.some x y hxy :=
    (congrArg (fun f : WP (FunctionField Base) →+ WP (FunctionField Base) =>
      f (genericPoint Base base_two_ne)) hE).trans hGen
  exact ⟨x,y,hxy,hGen,r,hRat',hCap,
    same_point_capped_residual_abscissa V base_two_ne hR i hi a b (p : ℤ) hN hOdd
      r p hCap x y hxy hInput hRat'⟩

end Selected

end ActualGaussianWeberChosenResidualDescriptor318
