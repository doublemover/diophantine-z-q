module
public import OriginalIntegerNormalProjection318
public section
noncomputable section
namespace OriginalThreeDimensionalTransference318
open scoped RealInnerProductSpace
open TernaryQuadraticLineCover318 LiteralTernaryReduction318 LiteralIntegerDuality318
open OriginalEuclideanLattice318 OriginalAttainedMinima318 OriginalSequentialMinima318
open OriginalNormalHeightGenerator318 OriginalPlaneRounding318 OriginalIntegerNormalProjection318
set_option maxHeartbeats 4500000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Construct the dimension-three transference witnesses on the ACTUAL
original lattice. The positive image generator gives the normal height;
integer plane rounding and actual sequential shortestness give constant2.
No transference inequality, reduced basis or normal-height witness is an
input to this theorem. -/
theorem actual_transference_witness (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (κ : ℤ) (t : ∀ i, Option (ZMod (p i))) :
    ∃ f : Fin 3 → Vector ℤ, IndependentTriple p κ t f ∧
      ∃ R : ℝ, 0<R ∧ (∀ i, ‖embed (f i)‖≤R) ∧
        ∃ d : E, d∈Dual p κ t ∧ d≠0 ∧ R*‖d‖≤2 := by
  classical
  obtain ⟨u,v,w,hind,huv,hvw,hip,hwmin⟩ := actual_sequential_triple p hp κ t
  have hu : u∈literalLattice p κ t := hind.1 0
  have hv : v∈literalLattice p κ t := hind.1 1
  have hu0 : embed u≠0 := hind.2.ne_zero 0
  have hw0 : embed w≠0 := hind.2.ne_zero 2
  let n := normal u v
  have hn : n≠0 := normal_ne_zero u v hu0 huv hip
  obtain ⟨G,hG,z,hz,hzn,hGdiv⟩ := actual_positive_generator p hp κ t n hn
  have hGr : (0:ℝ)<G := by exact_mod_cast hG
  let D : ℝ := (dot n n:ℝ)
  have hD : 0<D := by exact_mod_cast dot_self_positive n hn
  let a := coefficientA u v z
  let b := coefficientB u v z
  let z' := reduced u v z a b
  have hz' : z'∈literalLattice p κ t := reduced_mem p κ t u v z hu hv hz a b
  have hnz' : dot n z'=G := by
    rw [reduced_normal_value n u v z (normal_dot_left u v) (normal_dot_right u v) a b,hzn]
  let K : Submodule ℝ E := (innerSL ℝ (embed n)).toLinearMap.ker
  have hplane : Submodule.span ℝ (Set.range ![embed u,embed v])≤K := by
    apply Submodule.span_le.mpr
    rintro x ⟨i,rfl⟩
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
    linarith
  have hshort := hwmin z' hz' hzout
  have hshort2 := pow_le_pow_left₀ (norm_nonneg _) hshort 2
  have horth := normal_orthogonal u v z
  have hround := actual_rounding_bound u v z (normalComponent u v z) a b
    (actual_decomposition u v z hn) horth.1 horth.2 huv hip
  have hheight : ‖normalComponent u v z‖^2=(G:ℝ)^2/D := by
    rw [normal_component_norm_sq u v z hn,hzn]
  rw [hheight] at hround
  have hVW := pow_le_pow_left₀ (norm_nonneg _) hvw 2
  have hquot : ‖embed w‖^2≤4*((G:ℝ)^2/D) := by
    change ‖embed z'‖^2≤(G:ℝ)^2/D+(3/4:ℝ)*‖embed v‖^2 at hround
    nlinarith
  have htimes := mul_le_mul_of_nonneg_right hquot hD.le
  have hcancel : (4*((G:ℝ)^2/D))*D=4*(G:ℝ)^2 := by field_simp [hD.ne']
  rw [hcancel] at htimes
  obtain ⟨hdmem,hdne,hdnorm⟩ := normal_generator_dual p κ t n hn G hG hGdiv
  let d : E := (G:ℝ)⁻¹ • embed n
  have hnNorm : ‖embed n‖^2=D := by rw [←real_inner_self_eq_norm_sq,inner_embed]
  have hdNorm : ‖d‖^2=D/(G:ℝ)^2 := by
    rw [hdnorm,div_pow,hnNorm]
  have hprod2 : (‖embed w‖*‖d‖)^2≤4 := by
    rw [mul_pow,hdNorm,←mul_div_assoc]
    exact (div_le_iff₀ (sq_pos_of_pos hGr)).mpr (by nlinarith [htimes])
  have hprod : ‖embed w‖*‖d‖≤2 := by
    nlinarith [mul_nonneg (norm_nonneg (embed w)) (norm_nonneg d)]
  refine ⟨![u,v,w],hind,‖embed w‖,norm_pos_iff.mpr hw0,?_,d,hdmem,hdne,hprod⟩
  intro i
  fin_cases i
  · exact huv.trans hvw
  · exact hvw
  · exact le_rfl

/-- The original large-third-minimum condition, phrased without a chosen
minimum: every actual independent triple has a vector longer than T. -/
@[expose] def LargeThird (p : ι → ℕ) (κ : ℤ) (t : ∀ i, Option (ZMod (p i))) (T : ℝ) : Prop :=
  ∀ f : Fin 3 → Vector ℤ, IndependentTriple p κ t f → ∃ i, T<‖embed (f i)‖

/-- Genuine produced short-dual vector from the actual large-third-
minimum condition. This discharges, rather than postulates, the missing
transference implication for the original lattice family. -/
theorem large_third_has_short_dual (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (κ : ℤ) (t : ∀ i, Option (ZMod (p i))) (T : ℝ) (hT : 0<T)
    (hlarge : LargeThird p κ t T) :
    ∃ d : E, d∈Dual p κ t ∧ d≠0 ∧ ‖d‖<2/T := by
  obtain ⟨f,hf,R,hR,hbounds,d,hd,hdne,hprod⟩ := actual_transference_witness p hp κ t
  obtain ⟨i,hi⟩ := hlarge f hf
  have hTR : T<R := hi.trans_le (hbounds i)
  have hdn : 0<‖d‖ := norm_pos_iff.mpr hdne
  refine ⟨d,hd,hdne,?_⟩
  apply (lt_div_iff₀ hT).mpr
  have hh := mul_lt_mul_of_pos_right hTR hdn
  nlinarith

end OriginalThreeDimensionalTransference318
