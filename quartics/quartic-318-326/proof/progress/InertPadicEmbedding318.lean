module
public import InertCompletion318
public section
namespace InertPadicEmbedding318
open ConcreteG8Domain DiscreteCompletion318 InertCompletion318
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
variable (p:ℕ) [Fact p.Prime] (nonsquare:¬∃x:ZMod p,x^2=2)

@[expose] abbrev RationalField := WithAbs (absolute (p:ℝ) (prime_gt_one p) (ConcretePadic318.rationalPlace p))
@[expose] def rationalToPadic : RationalField p →+* ℚ_[p] :=
  (Rat.castHom ℚ_[p]).comp (WithAbs.equiv _).toRingHom
@[expose] def rationalToCompletion : RationalField p →+* Field p nonsquare :=
  (Rat.castHom (Field p nonsquare)).comp (WithAbs.equiv _).toRingHom

 theorem rational_magnitude (q:ℚ) :
    magnitude (p:ℝ) (ConcretePadic318.rationalPlace p q)=‖(q:ℚ_[p])‖ := by
  by_cases hq:q=0
  · simp [hq]
  · rw [ConcretePadic318.rational_value p q hq,magnitude_coe]
    rw [Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast hq),Padic.valuation_ratCast]


 theorem toPadic_isometry : Isometry (rationalToPadic p) := by
  apply (AddMonoidHomClass.isometry_iff_norm _).mpr
  intro x
  rw [WithAbs.norm_eq_apply_ofAbs]
  change ‖(x.ofAbs:ℚ_[p])‖=magnitude (p:ℝ) (ConcretePadic318.rationalPlace p x.ofAbs)
  exact (rational_magnitude p x.ofAbs).symm

 theorem toCompletion_isometry : Isometry (rationalToCompletion p nonsquare) := by
  apply (AddMonoidHomClass.isometry_iff_norm _).mpr
  intro x
  rw [WithAbs.norm_eq_apply_ofAbs]
  change ‖(x.ofAbs:Field p nonsquare)‖=magnitude (p:ℝ) (ConcretePadic318.rationalPlace p x.ofAbs)
  rw [norm_ratCast]
  exact (rational_magnitude p x.ofAbs).symm

 theorem toPadic_dense : DenseRange (rationalToPadic p) := by
  have hr:Set.range (rationalToPadic p)=Set.range ((↑):ℚ→ℚ_[p]) := by
    ext y
    constructor
    · rintro ⟨x,hx⟩
      exact ⟨x.ofAbs,hx⟩
    · rintro ⟨q,hq⟩
      exact ⟨WithAbs.toAbs _ q,hq⟩
  intro x
  rw [hr]
  exact Padic.denseRange_ratCast p x

/-- The genuine isometric Qp embedding into the completion at the actual
inert place, obtained by extending the rational inclusion. -/
@[expose] def padicEmbedding : ℚ_[p] →+* Field p nonsquare :=
  IsDenseInducing.extendRingHom (toPadic_isometry p).isUniformInducing
    (toPadic_dense p) (toCompletion_isometry p nonsquare).uniformContinuous

 theorem padicEmbedding_uniformContinuous : UniformContinuous (padicEmbedding p nonsquare) :=
  uniformContinuous_uniformly_extend (toPadic_isometry p).isUniformInducing
    (toPadic_dense p) (toCompletion_isometry p nonsquare).uniformContinuous

 theorem padicEmbedding_isometry : Isometry (padicEmbedding p nonsquare) := by
  apply (AddMonoidHomClass.isometry_iff_norm _).mpr
  intro x
  refine (toPadic_dense p).induction_on x ?_ ?_
  · exact isClosed_eq (continuous_norm.comp (padicEmbedding_uniformContinuous p nonsquare).continuous) continuous_norm
  intro q
  change ‖((toPadic_isometry p).isUniformInducing.isDenseInducing (toPadic_dense p)).extend
    (rationalToCompletion p nonsquare) (rationalToPadic p q)‖=‖rationalToPadic p q‖
  rw [IsDenseInducing.extend_eq _ (toCompletion_isometry p nonsquare).continuous]
  rw [(toCompletion_isometry p nonsquare).norm_map_of_map_zero (map_zero _) q,
    (toPadic_isometry p).norm_map_of_map_zero (map_zero _) q]

 theorem padicEmbedding_norm (x:ℚ_[p]) : ‖padicEmbedding p nonsquare x‖=‖x‖ :=
  (padicEmbedding_isometry p nonsquare).norm_map_of_map_zero (map_zero _) x

 theorem padicEmbedding_ratCast (q:ℚ) : padicEmbedding p nonsquare (q:ℚ_[p])=(q:Field p nonsquare) := map_ratCast _ q

 theorem padicEmbedding_injective : Function.Injective (padicEmbedding p nonsquare) :=
  (padicEmbedding p nonsquare).injective

end
end InertPadicEmbedding318
#print axioms InertPadicEmbedding318.padicEmbedding
#print axioms InertPadicEmbedding318.padicEmbedding_isometry
