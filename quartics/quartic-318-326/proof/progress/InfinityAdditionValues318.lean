module
public import InfinityAdditionAlgebra318
public section
noncomputable section
namespace InfinityAdditionValues318
open InfinityAdditionAlgebra318
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

/-- Vanishing chord denominator in the actual infinity-output open forces inverse inputs. -/
theorem chord_zero_inverse {K:Type*} [Field K] (a b x₁ y₁ x₂ y₂:K)
    (h₁:y₁^2-x₁^3-a*x₁-b=0) (h₂:y₂^2-x₂^3-a*x₂-b=0)
    (hd:x₂-x₁=0)
    (hv:(y₂-y₁)*(x₁*(x₂-x₁)^2-((y₂-y₁)^2-(x₁+x₂)*(x₂-x₁)^2))-
      y₁*(x₂-x₁)^3≠0) : x₁=x₂ ∧ y₁= -y₂ := by
  have hx : x₁=x₂ := (sub_eq_zero.mp hd).symm
  have hy : y₂^2=y₁^2 := by rw [←hx] at h₂; linear_combination h₂-h₁
  refine ⟨hx,?_⟩
  rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hy) with he | he
  · exfalso
    apply hv
    rw [hd,he]
    ring
  · linear_combination he

/-- Vanishing complementary denominator also forces inverse inputs, including 2-torsion. -/
theorem tangent_zero_inverse {K:Type*} [Field K] (a b x₁ y₁ x₂ y₂:K)
    (h₁:y₁^2-x₁^3-a*x₁-b=0) (h₂:y₂^2-x₂^3-a*x₂-b=0)
    (hd:y₁+y₂=0)
    (hv:(x₁^2+x₁*x₂+x₂^2+a)*(x₁*(y₁+y₂)^2-
      ((x₁^2+x₁*x₂+x₂^2+a)^2-(x₁+x₂)*(y₁+y₂)^2))-
      y₁*(y₁+y₂)^3≠0) : x₁=x₂ ∧ y₁= -y₂ := by
  have hs : x₁^2+x₁*x₂+x₂^2+a≠0 := by
    intro he
    apply hv
    rw [hd,he]
    ring
  have hp : (x₂-x₁)*(x₁^2+x₁*x₂+x₂^2+a)=0 := by
    linear_combination h₁-h₂+(y₂-y₁)*hd
  exact ⟨(sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right hs)).symm,eq_neg_of_add_eq_zero_left hd⟩

variable {R K:Type u} [CommRing R] [Field K] [Algebra R K]

/-- In the actual localized tensor algebra, zero denominator is exactly an inverse-pair case. -/
theorem inverse_coordinates (A B:R) (t:Bool) (φ:OutputRing A B t →ₐ[R] K)
    (hd:φ (pairMap A B t (denominator A B t))=0) :
    φ (pairMap A B t (X1 A B))=φ (pairMap A B t (X2 A B)) ∧
    φ (pairMap A B t (Y1 A B))= -φ (pairMap A B t (Y2 A B)) := by
  let f : RelativeChordAlgebra318.PairRing A B →ₐ[R] K := φ.comp (pairMap A B t)
  have hm (a:RelativeChordAlgebra318.PairRing A B) (n:ℕ) : f (a^n)=(f a)^n := by
    induction n with
    | zero =>
        simp only [pow_zero]
        exact f.toRingHom.map_one
    | succ n ih => simp only [pow_succ,map_mul,ih]
  have h1:=congrArg f (first_equation A B)
  have h2:=congrArg f (second_equation A B)
  have hn : f (numeratorY A B t)≠0 := isUnit_iff_ne_zero.mp ((numeratorY_unit A B t).map φ)
  simp only [map_sub,hm,map_mul,map_zero,coeffMap,Algebra.ofId_apply,AlgHom.commutes] at h1 h2
  change f (denominator A B t)=0 at hd
  change f (X1 A B)=f (X2 A B) ∧ f (Y1 A B)= -f (Y2 A B)
  cases t
  · simp only [denominator,Bool.false_eq_true,ite_false,map_sub] at hd
    simp only [numeratorY,numeratorX,slopeNumerator,denominator,Bool.false_eq_true,ite_false,
      map_sub,map_mul,hm,map_add] at hn
    exact chord_zero_inverse _ _ _ _ _ _ h1 h2 hd hn
  · simp only [denominator,ite_true,map_add] at hd
    simp only [numeratorY,numeratorX,slopeNumerator,denominator,ite_true,
      map_sub,map_mul,hm,map_add,coeffMap,Algebra.ofId_apply,AlgHom.commutes] at hn
    exact tangent_zero_inverse _ _ _ _ _ _ h1 h2 hd hn

end InfinityAdditionValues318
