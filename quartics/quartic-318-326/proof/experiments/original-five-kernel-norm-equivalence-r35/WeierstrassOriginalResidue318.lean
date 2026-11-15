module
public import WeierstrassLaurentFiltration318

public section
noncomputable section
namespace WeierstrassOriginalResidue318
open WeierstrassLaurentModel318 WeierstrassLaurentFiltration318
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (A B : ℚ)

/-- Every element of the entire original finite chart obeys the finite exponent bound. -/
theorem finite_image (a : ShortAffineJacobian318.Ring A B) :
    finiteMap A B a ∈ finiteSpace A B := by
  obtain ⟨P,rfl⟩ := Ideal.Quotient.mk_surjective a
  induction P using MvPolynomial.induction_on with
  | C q =>
    change finiteMap A B (algebraMap ℚ (ShortAffineJacobian318.Ring A B) q) ∈ _
    rw [AlgHom.commutes]
    exact finite_scalar A B q
  | add P Q hP hQ =>
    simpa only [map_add] using (finiteSpace A B).add_mem hP hQ
  | mul_X P i hP =>
    rw [map_mul,map_mul]
    fin_cases i
    · change finiteMap A B _ * finiteMap A B (ShortAffineJacobian318.x A B) ∈ _
      rw [finiteMap_x]
      exact finite_mul_x A B hP
    · change finiteMap A B _ * finiteMap A B (ShortAffineJacobian318.y A B) ∈ _
      rw [finiteMap_y]
      exact finite_mul_y A B hP

/-- Every element of the entire original infinity chart has only nonnegative z powers. -/
theorem infinity_image (a : InfinityChart318.Ring A B) :
    infinityMap A B a ∈ infinitySpace A B := by
  obtain ⟨P,rfl⟩ := Ideal.Quotient.mk_surjective a
  induction P using MvPolynomial.induction_on with
  | C q =>
    change infinityMap A B (algebraMap ℚ (InfinityChart318.Ring A B) q) ∈ _
    rw [AlgHom.commutes]
    exact infinity_scalar A B q
  | add P Q hP hQ =>
    simpa only [map_add] using (infinitySpace A B).add_mem hP hQ
  | mul_X P i hP =>
    rw [map_mul,map_mul]
    fin_cases i
    · change infinityMap A B _ * infinityMap A B (InfinityChart318.x A B) ∈ _
      rw [infinityMap_x]
      exact infinity_mul_x A B hP
    · change infinityMap A B _ * infinityMap A B (InfinityChart318.z A B) ∈ _
      rw [infinityMap_z]
      exact infinity_mul_z A B hP

/-- A genuine additive functional on the original overlap ring. -/
@[expose] def originalResidue : WeierstrassOverlap318.InfinityOverlap A B →+ ℚ :=
  (residue A B).toAddMonoidHom.comp (overlapMap A B).toAddMonoidHom

theorem residue_finite (a : ShortAffineJacobian318.Ring A B) :
    originalResidue A B (WeierstrassOverlap318.toInfinityBase A B a) = 0 :=
  finite_residue A B (finite_image A B a)

theorem residue_infinity (a : InfinityChart318.Ring A B) :
    originalResidue A B (algebraMap (InfinityChart318.Ring A B) _ a) = 0 := by
  change residue A B (overlapMap A B _) = 0
  rw [overlapMap_base]
  exact infinity_residue A B (infinity_image A B a)

/-- The old specified target overlap representative maps to the distinguished monomial. -/
theorem representative_image :
    overlapMap A B (WeierstrassBoundaryClass318.representative A B) = monomial A B (-1) 2 := by
  change overlapMap A B (WeierstrassOverlap318.toInfinity A B
    (WeierstrassOverlap318.ax A B ^ 2 * WeierstrassOverlap318.ai A B)) = _
  simp only [map_mul,map_pow,WeierstrassOverlap318.toInfinity_ax,
    WeierstrassOverlap318.toInfinity_ai,overlapMap_ix,overlapMap_ii,overlapMap_iz]
  have h : zpow A B (-1) * zpow A B 1 = 1 := by
    rw [zpow_mul]; norm_num [zpow_zero]
  change (x A B * zpow A B (-1))^2 * zpow A B 1 = _
  calc
    _ = (zpow A B (-1) * x A B^2) * (zpow A B (-1) * zpow A B 1) := by ring
    _ = _ := by rw [h,mul_one]; rfl

/-- Exact nonzero residue of the original representative, uniformly in A and B. -/
theorem residue_representative :
    originalResidue A B (WeierstrassBoundaryClass318.representative A B) = 1 := by
  change residue A B (overlapMap A B _) = 1
  rw [representative_image,residue_monomial]
  norm_num

end WeierstrassOriginalResidue318
