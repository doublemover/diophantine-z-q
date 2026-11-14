module
public import OriginalReducedBasisData318
public section
noncomputable section
namespace OriginalSaturatedPlane318
open scoped RealInnerProductSpace
open TernaryQuadraticLineCover318 LiteralTernaryReduction318 LiteralIntegerDuality318
open OriginalEuclideanLattice318 OriginalPlaneRounding318 OriginalIntegerNormalProjection318
open OriginalNormalHeightGenerator318
set_option maxHeartbeats 3000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def line (u : Vector ℤ) : Submodule ℝ E :=
  Submodule.span ℝ (Set.range (fun _ : Fin 1 => embed u))

lemma line_coefficient (u : Vector ℤ) (z : E) (hz : z∈line u) :
    ∃ a : ℝ, a • embed u=z := by
  have hsingle : z∈Submodule.span ℝ ({embed u}:Set E) := by
    simpa only [line,Set.range_const] using hz
  exact Submodule.mem_span_singleton.mp hsingle

lemma embed_zsmul (a : ℤ) (u : Vector ℤ) : embed (a • u)=(a:ℝ) • embed u := by
  ext i
  fin_cases i <;> simp [embed,zsmul_eq_mul]

/-- A genuine shortest original vector generates the WHOLE intersection
of the lattice with its real line. This is proved by nearest-integer
rounding, not assumed from primitiveness or a determinant calculation. -/
theorem whole_line (p : ι → ℕ) (κ : ℤ) (t : ∀ i, Option (ZMod (p i)))
    (u : Vector ℤ) (hu : u∈literalLattice p κ t) (hu0 : embed u≠0)
    (hmin : ∀ z, z∈literalLattice p κ t → embed z≠0 → ‖embed u‖≤‖embed z‖)
    (z : Vector ℤ) (hz : z∈literalLattice p κ t) (hline : embed z∈line u) :
    ∃ a : ℤ, z=a • u := by
  obtain ⟨a,ha⟩ := line_coefficient u (embed z) hline
  let r := z-nearest a • u
  have hr : r∈literalLattice p κ t :=
    (literalLattice p κ t).sub_mem hz ((literalLattice p κ t).zsmul_mem hu _)
  have he : embed r=(a-(nearest a:ℝ)) • embed u := by
    rw [embedHom.map_sub,embed_zsmul,←ha]
    module
  have hnorm : ‖embed r‖≤(1/2:ℝ)*‖embed u‖ := by
    rw [he,norm_smul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (nearest_error a) (norm_nonneg _)
  have hr0 : embed r=0 := by
    by_contra hn
    have hh := hmin r hr hn
    have hp := norm_pos_iff.mpr hu0
    linarith
  have rz : r=0 := embed_injective (by simpa only [embed_zero] using hr0)
  exact ⟨nearest a,sub_eq_zero.mp rz⟩

/-- The first two actual sequential shortest vectors generate the WHOLE
integer lattice in their real plane. The rounding residual is shorter
than the second vector, hence lies in the first line, whose saturation
was proved above. No finite-index sublattice is substituted for it. -/
theorem whole_normal_kernel (p : ι → ℕ) (κ : ℤ) (t : ∀ i, Option (ZMod (p i)))
    (u v : Vector ℤ) (hu : u∈literalLattice p κ t) (hv : v∈literalLattice p κ t)
    (hu0 : embed u≠0) (huv : ‖embed u‖≤‖embed v‖)
    (hip : |⟪embed u,embed v⟫|≤‖embed u‖^2/2)
    (humin : ∀ z, z∈literalLattice p κ t → embed z≠0 → ‖embed u‖≤‖embed z‖)
    (hvmin : ∀ z, z∈literalLattice p κ t → embed z∉line u → ‖embed v‖≤‖embed z‖)
    (z : Vector ℤ) (hz : z∈literalLattice p κ t) (hzn : dot (normal u v) z=0) :
    ∃ a b : ℤ, z=a • u+b • v := by
  have hn := normal_ne_zero u v hu0 huv hip
  let a := coefficientA u v z
  let b := coefficientB u v z
  let r := reduced u v z a b
  have hr := reduced_mem p κ t u v z hu hv hz a b
  have horth := normal_orthogonal u v z
  have hround := actual_rounding_bound u v z (normalComponent u v z) a b
    (actual_decomposition u v z hn) horth.1 horth.2 huv hip
  have hN : normalComponent u v z=0 := by simp only [normalComponent,hzn,Int.cast_zero,zero_div,zero_smul]
  rw [hN,norm_zero,zero_pow (by decide : (2:ℕ)≠0),zero_add] at hround
  have hline : embed r∈line u := by
    by_contra hh
    have hmin := hvmin r hr hh
    have hs := pow_le_pow_left₀ (norm_nonneg _) hmin 2
    have huPos := norm_pos_iff.mpr hu0
    have hvPos : 0<‖embed v‖ := huPos.trans_le huv
    have hvSq := sq_pos_of_pos hvPos
    change ‖embed r‖^2≤(3/4:ℝ)*‖embed v‖^2 at hround
    nlinarith
  obtain ⟨c,hc⟩ := whole_line p κ t u hu hu0 humin r hr hline
  refine ⟨nearest a+c,nearest b,?_⟩
  change z-nearest a • u-nearest b • v=c • u at hc
  calc
    z = (z-nearest a • u-nearest b • v)+nearest a • u+nearest b • v := by abel
    _ = (nearest a+c) • u+nearest b • v := by rw [hc]; module

end OriginalSaturatedPlane318
