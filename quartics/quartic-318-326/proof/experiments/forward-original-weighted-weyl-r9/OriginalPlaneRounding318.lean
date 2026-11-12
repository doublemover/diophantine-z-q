module
public import OriginalNormalHeightGenerator318
public import Mathlib.Tactic.Module
public section
noncomputable section
namespace OriginalPlaneRounding318
open scoped RealInnerProductSpace
open TernaryQuadraticLineCover318 LiteralTernaryReduction318 LiteralIntegerDuality318
open OriginalEuclideanLattice318 OriginalNormalHeightGenerator318
set_option maxHeartbeats 3500000

@[expose] def nearest (a : ℝ) : ℤ := ⌊a+(1/2:ℝ)⌋

lemma nearest_error (a : ℝ) : |a-(nearest a:ℝ)|≤(1/2:ℝ) := by
  have hlo := Int.floor_le (a+(1/2:ℝ))
  have hhi := Int.lt_floor_add_one (a+(1/2:ℝ))
  change |a-(⌊a+(1/2:ℝ)⌋:ℝ)|≤(1/2:ℝ)
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma plane_combination_sq (u v : E) (a b : ℝ) :
    ‖a • u+b • v‖^2=a^2*‖u‖^2+2*a*b*⟪u,v⟫+b^2*‖v‖^2 := by
  rw [←real_inner_self_eq_norm_sq]
  simp only [inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,
    real_inner_self_eq_norm_sq,real_inner_comm v u]
  ring

/-- Exact dimension-two rounding bound used by the intended 3D
transference argument. The reduction inequality is explicit; no covering
radius is presumed from determinant or rank. -/
theorem reduced_plane_bound (u v : E) (huv : ‖u‖≤‖v‖)
    (hip : |⟪u,v⟫|≤‖u‖^2/2) (a b : ℝ)
    (ha : |a|≤(1/2:ℝ)) (hb : |b|≤(1/2:ℝ)) :
    ‖a • u+b • v‖^2≤(3/4:ℝ)*‖v‖^2 := by
  have ha2 : a^2≤(1/4:ℝ) := by
    have hh := mul_self_le_mul_self (abs_nonneg a) ha
    nlinarith [sq_abs a]
  have hb2 : b^2≤(1/4:ℝ) := by
    have hh := mul_self_le_mul_self (abs_nonneg b) hb
    nlinarith [sq_abs b]
  have hab : |a*b|≤(1/4:ℝ) := by
    rw [abs_mul]
    nlinarith [mul_le_mul ha hb (abs_nonneg b) (by norm_num : (0:ℝ)≤1/2)]
  have habc : |a*b*⟪u,v⟫|≤‖u‖^2/8 := by
    rw [abs_mul]
    have hh := mul_le_mul hab hip (abs_nonneg ⟪u,v⟫) (by norm_num : (0:ℝ)≤1/4)
    nlinarith
  have hcross : 2*a*b*⟪u,v⟫≤‖u‖^2/4 := by
    have hh := le_abs_self (a*b*⟪u,v⟫)
    nlinarith
  have hA := mul_le_mul_of_nonneg_right ha2 (sq_nonneg ‖u‖)
  have hB := mul_le_mul_of_nonneg_right hb2 (sq_nonneg ‖v‖)
  have hUV := pow_le_pow_left₀ (norm_nonneg u) huv 2
  rw [plane_combination_sq]
  nlinarith

@[expose] def reduced (u v z : Vector ℤ) (a b : ℝ) : Vector ℤ :=
  z-nearest a • u-nearest b • v

lemma embed_reduced (u v z : Vector ℤ) (a b : ℝ) :
    embed (reduced u v z a b)=embed z-(nearest a:ℝ) • embed u-(nearest b:ℝ) • embed v := by
  ext i
  fin_cases i <;> simp [embed,reduced,zsmul_eq_mul]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma reduced_mem (p : ι → ℕ) (κ : ℤ) (t : ∀ i, Option (ZMod (p i)))
    (u v z : Vector ℤ) (hu : u∈literalLattice p κ t) (hv : v∈literalLattice p κ t)
    (hz : z∈literalLattice p κ t) (a b : ℝ) : reduced u v z a b∈literalLattice p κ t :=
  (literalLattice p κ t).sub_mem
    ((literalLattice p κ t).sub_mem hz ((literalLattice p κ t).zsmul_mem hu _))
    ((literalLattice p κ t).zsmul_mem hv _)

lemma reduced_normal_value (n u v z : Vector ℤ) (hnu : dot n u=0) (hnv : dot n v=0)
    (a b : ℝ) : dot n (reduced u v z a b)=dot n z := by
  change (dotHom n) (z-nearest a • u-nearest b • v)=(dotHom n) z
  rw [map_sub,map_sub,map_zsmul,map_zsmul]
  change dot n z-nearest a • dot n u-nearest b • dot n v=dot n z
  rw [hnu,hnv,smul_zero,smul_zero,sub_zero,sub_zero]

/-- Round an ACTUAL original lattice point using integer multiples of
ACTUAL plane vectors. Its normal value is preserved, and the standard
Euclidean squared norm gets the explicit 3/4 plane error. The normal
component and its orthogonality remain visible inputs for the subsequent
projection producer, not an asserted transference theorem. -/
theorem actual_rounding_bound (u v z : Vector ℤ) (N : E) (a b : ℝ)
    (hdecomp : embed z=a • embed u+b • embed v+N)
    (hNu : ⟪embed u,N⟫=0) (hNv : ⟪embed v,N⟫=0)
    (huv : ‖embed u‖≤‖embed v‖) (hip : |⟪embed u,embed v⟫|≤‖embed u‖^2/2) :
    ‖embed (reduced u v z a b)‖^2≤‖N‖^2+(3/4:ℝ)*‖embed v‖^2 := by
  have he : embed (reduced u v z a b)=
      ((a-(nearest a:ℝ)) • embed u+(b-(nearest b:ℝ)) • embed v)+N := by
    rw [embed_reduced,hdecomp]
    module
  have horth : ⟪(a-(nearest a:ℝ)) • embed u+(b-(nearest b:ℝ)) • embed v,N⟫=0 := by
    simp only [inner_add_left,real_inner_smul_left,hNu,hNv,mul_zero,add_zero]
  rw [he,norm_add_sq_real,horth]
  have hbnd := reduced_plane_bound (embed u) (embed v) huv hip
    (a-(nearest a:ℝ)) (b-(nearest b:ℝ)) (nearest_error a) (nearest_error b)
  linarith

end OriginalPlaneRounding318
