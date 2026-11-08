module
public import SquareReflection318
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.Algebra.Squarefree.Basic
public section
noncomputable section
namespace QuadraticContactSquareclass318
set_option maxHeartbeats 600000
open Polynomial
variable {F ι:Type*} [Field F] [CharZero F] [DecidableEq ι]
@[expose] def factor (a:F) : F[X] := X^2-C a

theorem coprime {a b:F} (h:a≠b) : IsCoprime (factor a) (factor b) := by
  refine ⟨C (b-a)⁻¹,-C (b-a)⁻¹,?_⟩
  calc
    C (b-a)⁻¹*factor a+(-C (b-a)⁻¹)*factor b=C ((b-a)⁻¹*(b-a)) := by
      simp only [factor,map_mul,map_sub]
      ring
    _=1 := by rw [inv_mul_cancel₀ (sub_ne_zero.mpr h.symm),map_one]

theorem squarefree {a:F} (ha:a≠0) : Squarefree (factor a) :=
  (Polynomial.separable_X_pow_sub_C a (by norm_num : (2:F)≠0) ha).squarefree

theorem factor_nonunit (a:F) : ¬IsUnit (factor a) := by
  apply Polynomial.not_isUnit_of_natDegree_pos
  simp [factor]

/-- Distinct nonzero squared roots yield independent squareclasses even
when some individual quadratics split over the constant field. -/
theorem twisted_product_nonsquare (a:ι→F) (ha:Function.Injective a) (ha0:∀i,a i≠0)
    (s:Finset ι) (hs:s.Nonempty) (d:F) (hd:d≠0) :
    ¬IsSquare (algebraMap F[X] (RatFunc F) (C d*∏i∈s,factor (a i))) := by
  have hu:IsUnit (C d:F[X]):=isUnit_C.mpr (IsUnit.mk0 d hd)
  have hp:Squarefree (∏i∈s,factor (a i)) := by
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro i hi j hj hij
      exact (coprime (ha.ne hij)).isRelPrime
    · intro i hi
      exact squarefree (ha0 i)
  have hsf:Squarefree (C d*∏i∈s,factor (a i)):=
    squarefree_mul_iff.mpr ⟨hu.isRelPrime_left,hu.squarefree,hp⟩
  intro h
  obtain ⟨q,hq⟩:=(SquareReflection318.fraction_square_iff _).mp h
  have hqu:IsUnit q:=hsf q (by rw [hq])
  have hunit:IsUnit (C d*∏i∈s,factor (a i)):=hq.symm ▸ hqu.mul hqu
  obtain ⟨i,hi⟩:=hs
  apply factor_nonunit (a i)
  apply isUnit_of_dvd_unit _ hunit
  exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hi) _
end QuadraticContactSquareclass318
