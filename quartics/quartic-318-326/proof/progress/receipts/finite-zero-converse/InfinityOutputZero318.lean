module
public import FiniteInfinitySymmetry318
public import ChartNegation318
public import AffineEquationFunctor318
public section
noncomputable section
namespace InfinityOutputZero318
open InfinityAdditionAlgebra318
set_option maxHeartbeats 700000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The homogeneous numerator being a unit removes the apparent nilpotent
ambiguity in the equations U*d=0 and d^3=0. No reducedness is used. -/
theorem denominator_zero (x₁ x₂ y₁ d e U V : S)
    (hU : U=e^2-(x₁+x₂)*d^2)
    (hV : V=e*(x₁*d^2-U)-y₁*d^3)
    (hunit : IsUnit V) (hUd : U*d=0) (hd3 : d^3=0) :
    d=0 ∧ IsUnit e := by
  have hVd : V*d=0 := by
    rw [hV]
    linear_combination -e*hUd+(e*x₁-y₁*d)*hd3
  have hd : d=0 := hunit.mul_left_cancel (by simpa only [mul_zero] using hVd)
  have hVe : V= -(e^3) := by rw [hV,hU,hd]; ring
  rw [hVe] at hunit
  exact ⟨hd,(isUnit_pow_iff (by decide : (3:ℕ)≠0)).mp (by simpa only [neg_neg] using hunit.neg)⟩

/-- On either actual infinity-output chart, zero output forces the two finite
inputs to be exact negatives, even over rings with nilpotents. -/
theorem coordinates (A B:R) (t:Bool) (φ:OutputRing A B t →ₐ[R] S)
    (hx : φ (outX A B t)=0) (hz : φ (outZ A B t)=0) :
    φ (pairMap A B t (X2 A B))=φ (pairMap A B t (X1 A B)) ∧
    φ (pairMap A B t (Y2 A B))= -φ (pairMap A B t (Y1 A B)) := by
  let F : RelativeChordAlgebra318.PairRing A B →ₐ[R] S := φ.comp (pairMap A B t)
  have fone : F 1=1 := F.toRingHom.map_one
  have fpow (r:RelativeChordAlgebra318.PairRing A B) (n:ℕ) : F (r^n)=F r^n := by
    induction n with
    | zero => simpa only [pow_zero] using fone
    | succ n ih => simp only [pow_succ,map_mul,ih]
  have hu : F (numeratorX A B t)*F (denominator A B t)=0 := by
    have h:=FiniteInfinitySymmetry318.mapped_outX A B t φ
    rw [hx,zero_mul] at h
    exact h.symm
  have hd3 : F (denominator A B t)^3=0 := by
    have h:=FiniteInfinitySymmetry318.mapped_outZ A B t φ
    rw [hz,zero_mul] at h
    exact h.symm
  have hU : F (numeratorX A B t)=F (slopeNumerator A B t)^2-
      (F (X1 A B)+F (X2 A B))*F (denominator A B t)^2 := by
    simp only [numeratorX,map_sub,fpow,map_mul,map_add]
  have hV : F (numeratorY A B t)=F (slopeNumerator A B t)*
      (F (X1 A B)*F (denominator A B t)^2-F (numeratorX A B t))-
      F (Y1 A B)*F (denominator A B t)^3 := by
    simp only [numeratorY,map_sub,fpow,map_mul]
  obtain ⟨hd,he⟩:=denominator_zero (F (X1 A B)) (F (X2 A B)) (F (Y1 A B))
    (F (denominator A B t)) (F (slopeNumerator A B t))
    (F (numeratorX A B t)) (F (numeratorY A B t)) hU hV
    ((numeratorY_unit A B t).map φ) hu hd3
  have h1:=congrArg F (first_equation A B)
  have h2:=congrArg F (second_equation A B)
  simp only [map_sub,fpow,map_mul,map_zero] at h1 h2
  have hs : (F (Y2 A B)-F (Y1 A B))*(F (Y1 A B)+F (Y2 A B))=
      (F (X2 A B)-F (X1 A B))*(F (X1 A B)^2+F (X1 A B)*F (X2 A B)+
        F (X2 A B)^2+F (coeffMap A B A)) := by
    linear_combination h2-h1
  change F (X2 A B)=F (X1 A B) ∧ F (Y2 A B)= -F (Y1 A B)
  cases t
  · simp only [denominator,Bool.false_eq_true,ite_false,map_sub] at hd
    simp only [slopeNumerator,Bool.false_eq_true,ite_false,map_sub] at he
    have hxx:=sub_eq_zero.mp hd
    rw [hd,zero_mul] at hs
    have hsum : F (Y1 A B)+F (Y2 A B)=0 :=
      he.mul_left_cancel (by simpa only [mul_zero] using hs)
    exact ⟨hxx,eq_neg_of_add_eq_zero_right hsum⟩
  · simp only [denominator,ite_true,map_add] at hd
    simp only [slopeNumerator,ite_true,map_add,fpow,map_mul] at he
    rw [hd,mul_zero] at hs
    have hdiff : F (X2 A B)-F (X1 A B)=0 :=
      he.mul_right_cancel (by simpa only [zero_mul] using hs.symm)
    exact ⟨sub_eq_zero.mp hdiff,eq_neg_of_add_eq_zero_right hd⟩

/-- Exact algebra-map conclusion, not merely a statement about field points. -/
theorem input_maps (A B:R) (t:Bool) (φ:OutputRing A B t →ₐ[R] S)
    (hx : φ (outX A B t)=0) (hz : φ (outZ A B t)=0) :
    φ.comp (InfinityAdditionScheme318.rightInput A B t)=
      (φ.comp (InfinityAdditionScheme318.leftInput A B t)).comp
        (ChartNegation318.affineNeg A B) := by
  obtain ⟨hX,hY⟩:=coordinates A B t φ hx hz
  apply AffineEquationFunctor318.hom_ext
  · simpa only [AlgHom.comp_apply,InfinityAdditionScheme318.rightInput,
      InfinityAdditionScheme318.leftInput,ChartNegation318.affineNeg_x,X1,X2] using hX
  · simpa only [AlgHom.comp_apply,InfinityAdditionScheme318.rightInput,
      InfinityAdditionScheme318.leftInput,ChartNegation318.affineNeg_y,map_neg,Y1,Y2] using hY
end InfinityOutputZero318
