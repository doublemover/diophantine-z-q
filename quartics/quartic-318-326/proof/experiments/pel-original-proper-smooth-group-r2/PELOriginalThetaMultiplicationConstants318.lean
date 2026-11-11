module
public import PELOriginalGradedSectionRing318
public section
noncomputable section
namespace PELOriginalThetaMultiplicationConstants318
open PELOriginalSectionMultiplication318 PELOriginalWholeHZeroDimension318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalPolarizationTransitions318
variable (τ:ℂ)(hτ:0<τ.im)(m n:ℕ)[NeZero m][NeZero n]
local instance sum_ne_zero:NeZero (m+n):=⟨Nat.ne_of_gt (Nat.add_pos_left (Nat.pos_of_ne_zero (NeZero.ne m)) n)⟩

/-- Exact multiplication in the FULL original H0 coefficient spaces,
transporting the already constructed actual section product, not
postulating a multiplication table on abstract theta labels. -/
@[expose] def coordinateProduct:(Label m→ℂ)→ₗ[ℂ](Label n→ℂ)→ₗ[ℂ](Label (m+n)→ℂ) where
  toFun c:=(coefficientEquivalence τ hτ (m+n)).symm.toLinearMap.comp
    ((multiply τ hτ m n (coefficientEquivalence τ hτ m c)).comp
      (coefficientEquivalence τ hτ n).toLinearMap)
  map_add' c d:=by
    ext a
    simp only [LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,map_add,LinearMap.add_apply]
  map_smul' a c:=by
    ext d
    simp only [LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,map_smul,LinearMap.smul_apply]
lemma product_value(c:Label m→ℂ)(d:Label n→ℂ)(q:Base τ):
    (coefficientEquivalence τ hτ (m+n) (coordinateProduct τ hτ m n c d)).val q=
      (coefficientEquivalence τ hτ m c).val q*(coefficientEquivalence τ hτ n d).val q:=by
  change (coefficientEquivalence τ hτ (m+n)
    ((coefficientEquivalence τ hτ (m+n)).symm
      (multiply τ hτ m n (coefficientEquivalence τ hτ m c)
        (coefficientEquivalence τ hτ n d)))).val q=_
  rw [LinearEquiv.apply_symm_apply]
  rfl

@[expose] def structureConstant(r:Label m)(s:Label n)(t:Label (m+n)):ℂ:=
  coordinateProduct τ hτ m n (Pi.single r 1) (Pi.single s 1) t
lemma coefficient_basis(k:ℕ)[NeZero k](r:Label k):
    coefficientEquivalence τ hτ k (Pi.single r 1)=thetaVector τ hτ k r:=by
  change (∑s:Label k,(Pi.single r (1:ℂ)) s • thetaVector τ hτ k s)=_
  simp

/-- Actual products of the SAME original theta sections have these
unique exact coefficients in the full degree-(m+n) original section basis. -/
theorem basis_product(r:Label m)(s:Label n)(q:Base τ):
    (levelSection τ hτ m r q).2*(levelSection τ hτ n s q).2=
      ∑t:Label (m+n),structureConstant τ hτ m n r s t*
        (levelSection τ hτ (m+n) t q).2:=by
  have he:=product_value τ hτ m n (Pi.single r 1) (Pi.single s 1) q
  rw [coefficient_basis,coefficient_basis] at he
  change (expansionMap τ hτ (m+n) (coordinateProduct τ hτ m n (Pi.single r 1) (Pi.single s 1))).val q=_ at he
  rw [expansionMap_value] at he
  exact he.symm

/-- The multiplication of arbitrary original sections is the actual
finite bilinear contraction of the derived structure constants. -/
theorem coefficient_convolution(c:Label m→ℂ)(d:Label n→ℂ)(t:Label (m+n)):
    coordinateProduct τ hτ m n c d t=
      ∑r:Label m,∑s:Label n,c r*d s*structureConstant τ hτ m n r s t:=by
  have hc:c=∑r:Label m,c r • Pi.single r (1:ℂ):=by ext r;simp
  have hd:d=∑s:Label n,d s • Pi.single s (1:ℂ):=by ext s;simp
  conv_lhs=>rw [hc,hd]
  simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,
    Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,structureConstant]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  ring
end PELOriginalThetaMultiplicationConstants318
