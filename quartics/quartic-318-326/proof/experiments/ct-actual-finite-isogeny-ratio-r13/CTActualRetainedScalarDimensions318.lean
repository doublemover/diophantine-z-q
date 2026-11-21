module
public import CTActualDiagonalIsotropic318
public import CTActualRetainedLocalOrthogonality318
public import OriginalCasselsActualLocalSystem318
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import all CTActualFiniteIsogenyLinear318
import all OriginalSelectedCasselsParity318
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
public section
noncomputable section

namespace CTActualRetainedScalarDimensions318

open ActualNaturalAllPlacesFinite318 CTActualFiniteIsogenyLinear318
open CTActualRetainedScalarPair318 CTActualSignedGeneratorsQR318
open CTNativeRealSquareclassEquiv318 CTNativePadicSquareclassEquiv318
open ActualTwoDescentSquareClassQuotient318 OriginalSelectedCasselsParity318
open OriginalCasselsActualLocalSystem318 OriginalCasselsDyadicXClass318
open OriginalCasselsTargetClassChord318 OriginalCasselsNaturalPrimeValuation318
open Module
open scoped BigOperators

private def additiveCoordinateEquiv {K : Type} [Field K] {U : Type*}
    [AddCommGroup U] [Module F₂ U] (e : SquareClass K ≃* Multiplicative U) :
    ScalarBits K ≃ₗ[F₂] U := by
  let f : ScalarBits K →+ U :=
    { toFun := fun u => (e u.toMul).toAdd
      map_zero' := congrArg Multiplicative.toAdd (map_one e)
      map_add' := fun u v => congrArg Multiplicative.toAdd (map_mul e u.toMul v.toMul) }
  exact LinearEquiv.ofBijective (f.toZModLinearMap 2) ⟨by
    intro a b h
    exact Additive.toMul.injective (e.injective (Multiplicative.toAdd.injective h)),by
    intro x
    let r := e.symm (Multiplicative.ofAdd x)
    exact ⟨Additive.ofMul r,congrArg Multiplicative.toAdd (e.apply_symm_apply (Multiplicative.ofAdd x))⟩⟩

def realLinearEquiv : ScalarBits ℝ ≃ₗ[F₂] F₂ :=
  additiveCoordinateEquiv realScalarEquiv

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def dyadicLinearEquiv : ScalarBits ℚ_[2] ≃ₗ[F₂] (F₂ × F₂ × F₂) :=
  additiveCoordinateEquiv dyadicScalarEquiv

def oddLinearEquiv (p : ℕ) [Fact p.Prime] (hp2 : p≠2) :
    ScalarBits ℚ_[p] ≃ₗ[F₂] (F₂ × F₂) :=
  additiveCoordinateEquiv (oddScalarEquiv p hp2)

instance finiteRealScalarBits : Finite (ScalarBits ℝ) :=
  Finite.of_equiv F₂ realLinearEquiv.symm.toEquiv

instance finitePadicScalarBits (p : ℕ) [Fact p.Prime] : Finite (ScalarBits ℚ_[p]) := by
  by_cases h : p=2
  · subst p
    exact Finite.of_equiv (F₂ × F₂ × F₂) dyadicLinearEquiv.symm.toEquiv
  · exact Finite.of_equiv (F₂ × F₂) (oddLinearEquiv p h).symm.toEquiv

theorem real_scalar_dimension : finrank F₂ (ScalarBits ℝ)=1 :=
  realLinearEquiv.finrank_eq.trans (CommSemiring.finrank_self F₂)

theorem padic_scalar_dimension (p : ℕ) [Fact p.Prime] :
    finrank F₂ (ScalarBits ℚ_[p])=if p=2 then 3 else 2 := by
  by_cases hp : p=2
  · subst p
    rw [if_pos rfl,dyadicLinearEquiv.finrank_eq]
    simp only [Module.finrank_prod,CommSemiring.finrank_self]
  · rw [if_neg hp,(oddLinearEquiv p hp).finrank_eq]
    simp only [Module.finrank_prod,CommSemiring.finrank_self]

local instance {n : ℕ} (i : Support n) : Fact i.val.Prime :=
  ⟨Nat.prime_of_mem_primeFactors i.property⟩
local instance : DecidableEq ℝ := Classical.decEq _
local instance (p : ℕ) [Fact p.Prime] : DecidableEq (ℚ_[p]) := Classical.decEq _

instance retainedFinite (n : ℕ) : Finite (RetainedSpace n) := by
  change Finite (ScalarBits ℝ × ((i : Support n) → ScalarBits ℚ_[i.val]))
  infer_instance

theorem diagonal_dimension (n : ℕ) : finrank F₂ (globalDiagonal n)=1+Fintype.card (Support n) := by
  change finrank F₂ (LinearMap.range (diagonal n))=_
  rw [LinearMap.finrank_range_of_inj (diagonal_injective n)]
  change finrank F₂ (F₂ × (Support n → F₂))=_
  rw [Module.finrank_prod,CommSemiring.finrank_self,Module.finrank_pi]

theorem retained_dimension (n : ℕ) (hn : 0<n) :
    finrank F₂ (RetainedSpace n)=2*(1+Fintype.card (Support n)) := by
  change finrank F₂ (ScalarBits ℝ × ((i : Support n) → ScalarBits ℚ_[i.val]))=_
  rw [Module.finrank_prod,real_scalar_dimension,Module.finrank_pi_fintype]
  have hD (i : Support n) : finrank F₂ (ScalarBits ℚ_[i.val])=
      2+(if i=twoIndex n hn then 1 else 0) := by
    rw [padic_scalar_dimension]
    by_cases he : i=twoIndex n hn
    · rw [if_pos he,if_pos (congrArg Subtype.val he : i.val=2)]
    · have h : i.val≠2 := fun u => he (Subtype.ext u)
      rw [if_neg he,if_neg h]
  simp only [hD,Finset.sum_add_distrib]
  have h1 : (∑ i : Support n, if i=twoIndex n hn then (1:ℕ) else 0)=1 := by simp
  rw [h1]
  simp [Finset.sum_const,nsmul_eq_mul] <;> omega

/-- Actual finite vector space cardinality, not a numerically
similar supplied local index. -/
theorem card_eq_two_pow_dim (V : Type*) [AddCommGroup V] [Module F₂ V]
    [FiniteDimensional F₂ V] : Nat.card V=2^(finrank F₂ V) := by
  let b := Module.finBasis F₂ V
  calc
    Nat.card V=Nat.card (Fin (finrank F₂ V) → F₂) := Nat.card_congr b.equivFun.toEquiv
    _=_ := by simp [Nat.card_eq_fintype_card,Fintype.card_fun]

private theorem dimension_from_card (V : Type*) [AddCommGroup V] [Module F₂ V]
    [FiniteDimensional F₂ V] (j : ℕ) (h : Nat.card V=2^j) : finrank F₂ V=j :=
  (pow_right_strictMono' (by decide : (1:ℕ)<2)).injective
    ((card_eq_two_pow_dim V).symm.trans h)

section OneField
variable {K : Type} [Field K] [CharZero K] [DecidableEq K]

theorem forward_plane_card (n : K) (hn : n≠0) (L : LocalIsogeny n hn) :
    Nat.card (localPlane K .forward n hn)=L.cokernelCard := by
  change Nat.card ((xClassHom (actual_target_class_product n hn)).range)=
    Nat.card (TargetPoint n ⧸ L.hom.range)
  exact Nat.card_congr (actual_cokernel_equiv_xClass L (actual_target_class_product n hn)).symm.toEquiv

end OneField

def primeForwardDim (p : ℕ) : ℕ :=
  if p=2 then 1 else if p=3 then 0 else if p%3=1 then 1 else 0

theorem retained_not23_is_divisor (n : ℕ) (hn : 0<n)
    (p : ℕ) (hp : p.Prime) (hm : p∈(6*n).primeFactors) (h2 : p≠2) (h3 : p≠3) :
    p∈n.primeFactors := by
  have hp5 := five_le_prime_of_ne_two_three hp h2 h3
  have hD := (Nat.mem_primeFactors.mp hm).2.1
  refine (Nat.mem_primeFactors_of_ne_zero hn.ne').mpr ⟨hp,?_⟩
  rcases hp.dvd_mul.mp hD with h|h
  · have he : p∣2*3 := h
    rcases hp.dvd_mul.mp he with h|h
    · have hle := Nat.le_of_dvd (by decide : 0<2) h
      omega
    · have hle := Nat.le_of_dvd (by decide : 0<3) h
      omega
  · exact h

theorem real_forward_dimension (n : ℕ) (hn : 0<n) (hs : Squarefree n)
    (h12 : (n:ZMod 12)=11) : finrank F₂ (realPlane .forward n hn)=0 := by
  let S := actualLocalSystem n hn h12
  have hc := (actualExactLocalCokernels n hn hs h12).real_size
  have h := forward_plane_card (n:ℝ) (Nat.cast_ne_zero.mpr hn.ne') S.real
  apply dimension_from_card _ 0
  exact h.trans hc

theorem retained_forward_prime_dimension (n : ℕ) (hn : 0<n) (hs : Squarefree n)
    (hr : (n:ZMod 12)=11) (p : ℕ) (hp : p.Prime) (hm : p∈(6*n).primeFactors) :
    letI : Fact p.Prime := ⟨hp⟩
    finrank F₂ (localPlane ℚ_[p] .forward (n:ℚ_[p]) (Nat.cast_ne_zero.mpr hn.ne'))=primeForwardDim p := by
  letI : Fact p.Prime := ⟨hp⟩
  let S := actualLocalSystem n hn hr
  have hc := actualExactLocalCokernels n hn hs hr
  have he : Nat.card (localPlane ℚ_[p] .forward (n:ℚ_[p]) (Nat.cast_ne_zero.mpr hn.ne'))=
      S.finiteCokernelCard p hp :=
    forward_plane_card (n:ℚ_[p]) (Nat.cast_ne_zero.mpr hn.ne') (S.padic p hp)
  apply dimension_from_card _ (primeForwardDim p)
  rw [he]
  by_cases h2 : p=2
  · subst p
    simpa only [primeForwardDim,if_pos rfl,pow_one] using hc.two_size
  by_cases h3 : p=3
  · subst p
    simpa only [primeForwardDim,if_neg (by decide : (3:ℕ)≠2),if_pos rfl,pow_zero] using hc.three_size
  have hnM := retained_not23_is_divisor n hn p hp hm h2 h3
  have he' := hc.ramified_size p hnM hp
  have hmod : (p:ZMod 3)=1 ↔ p%3=1 := ZMod.natCast_eq_natCast_iff' p 1 3
  by_cases h : p%3=1
  · simpa only [primeForwardDim,if_neg h2,if_neg h3,if_pos h,if_pos (hmod.mpr h),pow_one] using he'
  · simpa only [primeForwardDim,if_neg h2,if_neg h3,if_neg h,if_neg (mt hmod.mp h),pow_zero] using he'

private def localProductCoordinateEquiv (e : CTActualGloballyFiniteIsogenySelmer318.Side)
    (n : ℕ) (hn : 0<n) :
    ↥(localProduct e n hn) ≃ₗ[F₂] (realPlane e n hn × ((i : Support n) → padicPlane e n hn i)) where
  toFun x := (⟨x.val.1,x.property.1⟩,fun i => ⟨x.val.2 i,x.property.2 i⟩)
  invFun x := ⟨(x.1.val,fun i => (x.2 i).val),x.1.property,fun i => (x.2 i).property⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · funext i
      apply Subtype.ext
      rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem forward_product_dimension (n : ℕ) (hn : 0<n) (hs : Squarefree n)
    (hr : (n:ZMod 12)=11) :
    finrank F₂ (localProduct .forward n hn)=∑ i : Support n, primeForwardDim i.val := by
  rw [(localProductCoordinateEquiv .forward n hn).finrank_eq,Module.finrank_prod,
    real_forward_dimension n hn hs hr,zero_add,Module.finrank_pi_fintype]
  apply Finset.sum_congr rfl
  intro i _
  exact retained_forward_prime_dimension n hn hs hr i.val (Fact.out : i.val.Prime) i.property

end CTActualRetainedScalarDimensions318

#print axioms CTActualRetainedScalarDimensions318.retained_dimension
#print axioms CTActualRetainedScalarDimensions318.forward_product_dimension
