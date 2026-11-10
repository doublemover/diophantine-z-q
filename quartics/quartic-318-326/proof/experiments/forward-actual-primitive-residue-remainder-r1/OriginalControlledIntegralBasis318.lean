module
public import OriginalSaturatedPlane318
public section
noncomputable section
namespace OriginalControlledIntegralBasis318
open scoped RealInnerProductSpace
open TernaryQuadraticLineCover318 LiteralTernaryReduction318 LiteralIntegerDuality318
open OriginalEuclideanLattice318 OriginalAttainedMinima318 OriginalReducedBasisData318
open OriginalPlaneRounding318 OriginalIntegerNormalProjection318 OriginalNormalHeightGenerator318
open OriginalSaturatedPlane318
set_option maxHeartbeats 4000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Integer spanning, not merely three independent lattice vectors or a
full-rank finite-index sublattice. Together with real independence this
is the literal integral-basis property needed by the good-lattice sieve. -/
@[expose] def IntegralBasisTriple (p : ι → ℕ) (κ : ℤ) (t : ∀ i, Option (ZMod (p i)))
    (u v z : Vector ℤ) : Prop :=
  IndependentTriple p κ t ![u,v,z] ∧
    ∀ y : Vector ℤ, y∈literalLattice p κ t → ∃ a b c : ℤ, y=a • u+b • v+c • z

/-- Construct a full ORIGINAL integer basis with first two sequential
shortest vectors unchanged and third vector at most twice the third
sequential minimum. The actual positive image generator supplies the
third height; plane saturation supplies integer spanning of every point. -/
theorem actual_controlled_basis (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (κ : ℤ) (t : ∀ i, Option (ZMod (p i))) :
    ∃ u v w z : Vector ℤ,
      IndependentTriple p κ t ![u,v,w] ∧ IntegralBasisTriple p κ t u v z ∧
      ‖embed u‖≤‖embed v‖ ∧ ‖embed v‖≤‖embed w‖ ∧
      |⟪embed u,embed v⟫|≤‖embed u‖^2/2 ∧ ‖embed z‖≤2*‖embed w‖ ∧
      (∀ y, y∈literalLattice p κ t → embed y≠0 → ‖embed u‖≤‖embed y‖) ∧
      (∀ y, y∈literalLattice p κ t → embed y∉line u → ‖embed v‖≤‖embed y‖) ∧
      (∀ y, y∈literalLattice p κ t →
        embed y∉Submodule.span ℝ (Set.range ![embed u,embed v]) → ‖embed w‖≤‖embed y‖) := by
  classical
  obtain ⟨u,v,w,hind,huv,hvw,hip,hvout,hwout,humin,hvmin,hwmin⟩ :=
    actual_full_sequential_data p hp κ t
  have hu : u∈literalLattice p κ t := hind.1 0
  have hv : v∈literalLattice p κ t := hind.1 1
  have hw : w∈literalLattice p κ t := hind.1 2
  have hu0 : embed u≠0 := hind.2.ne_zero 0
  let n := normal u v
  have hn : n≠0 := normal_ne_zero u v hu0 huv hip
  obtain ⟨G,hG,z,hz,hzn,hdiv⟩ := actual_positive_generator p hp κ t n hn
  let a := coefficientA u v z
  let b := coefficientB u v z
  let z' := reduced u v z a b
  have hz' : z'∈literalLattice p κ t := reduced_mem p κ t u v z hu hv hz a b
  have hnz' : dot n z'=G := by
    rw [reduced_normal_value n u v z (normal_dot_left u v) (normal_dot_right u v) a b,hzn]
  have hspan (y : Vector ℤ) (hy : y∈literalLattice p κ t) :
      ∃ a b c : ℤ, y=a • u+b • v+c • z' := by
    obtain ⟨c,hc⟩ := hdiv y hy
    let r := y-c • z'
    have hr : r∈literalLattice p κ t :=
      (literalLattice p κ t).sub_mem hy ((literalLattice p κ t).zsmul_mem hz' c)
    have hrn : dot n r=0 := by
      change (dotHom n) (y-c • z')=0
      rw [map_sub,map_zsmul]
      change dot n y-c • dot n z'=0
      rw [hnz',hc,zsmul_eq_mul]
      ring
    obtain ⟨d,e,hde⟩ := whole_normal_kernel p κ t u v hu hv hu0 huv hip humin hvmin r hr hrn
    refine ⟨d,e,c,?_⟩
    change y-c • z'=d • u+e • v at hde
    exact sub_eq_iff_eq_add.mp hde
  have hpair : LinearIndependent ℝ ![embed u,embed v] := by
    apply (LinearIndependent.pair_iff' hu0).mpr
    intro c hc
    apply hvout
    rw [←hc]
    exact (line u).smul_mem c (Submodule.subset_span ⟨0,rfl⟩)
  let K : Submodule ℝ E := (innerSL ℝ (embed n)).toLinearMap.ker
  have hplane : Submodule.span ℝ (Set.range ![embed u,embed v])≤K := by
    apply Submodule.span_le.mpr
    rintro y ⟨i,rfl⟩
    fin_cases i
    · change ⟪embed n,embed u⟫=0
      rw [inner_embed,normal_dot_left,Int.cast_zero]
    · change ⟪embed n,embed v⟫=0
      rw [inner_embed,normal_dot_right,Int.cast_zero]
  have hzout : embed z'∉Submodule.span ℝ (Set.range ![embed u,embed v]) := by
    intro hh
    have hk := hplane hh
    change ⟪embed n,embed z'⟫=0 at hk
    rw [inner_embed,hnz'] at hk
    have hGr : (0:ℝ)<G := by exact_mod_cast hG
    linarith
  have hindz : IndependentTriple p κ t ![u,v,z'] := by
    constructor
    · intro i; fin_cases i
      · exact hu
      · exact hv
      · exact hz'
    · have hh := hpair.finSnoc hzout
      convert hh using 1
      ext i
      fin_cases i <;> rfl
  have hnw : dot n w≠0 := by
    intro hh
    apply hwout
    have hdec := actual_decomposition u v w hn
    have hN : normalComponent u v w=0 := by simp only [normalComponent,hh,Int.cast_zero,zero_div,zero_smul]
    rw [hN,add_zero] at hdec
    rw [hdec]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0,rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1,rfl⟩))
  have hGle : G≤|dot n w| :=
    least_positive_value G hG _ (abs_pos.mpr hnw) ((dvd_abs).mpr (hdiv w hw))
  have hGr : (0:ℝ)<G := by exact_mod_cast hG
  let D : ℝ := (dot n n:ℝ)
  have hD : 0<D := by exact_mod_cast dot_self_positive n hn
  have hGN : (G:ℝ)≤|⟪embed n,embed w⟫| := by
    rw [inner_embed]
    exact_mod_cast hGle
  have hC := hGN.trans (abs_real_inner_le_norm (embed n) (embed w))
  have hCsq := pow_le_pow_left₀ hGr.le hC 2
  have hNN : ‖embed n‖^2=D := by rw [←real_inner_self_eq_norm_sq,inner_embed]
  rw [mul_pow,hNN] at hCsq
  have hheight : (G:ℝ)^2/D≤‖embed w‖^2 := by
    apply (div_le_iff₀ hD).mpr
    nlinarith
  have horth := normal_orthogonal u v z
  have hround := actual_rounding_bound u v z (normalComponent u v z) a b
    (actual_decomposition u v z hn) horth.1 horth.2 huv hip
  have hN : ‖normalComponent u v z‖^2=(G:ℝ)^2/D := by
    rw [normal_component_norm_sq u v z hn,hzn]
  rw [hN] at hround
  have hVW := pow_le_pow_left₀ (norm_nonneg _) hvw 2
  have hbound : ‖embed z'‖≤2*‖embed w‖ := by
    change ‖embed z'‖^2≤(G:ℝ)^2/D+(3/4:ℝ)*‖embed v‖^2 at hround
    nlinarith [norm_nonneg (embed z'),norm_nonneg (embed w)]
  exact ⟨u,v,w,z',hind,⟨hindz,hspan⟩,huv,hvw,hip,hbound,humin,hvmin,hwmin⟩

end OriginalControlledIntegralBasis318
