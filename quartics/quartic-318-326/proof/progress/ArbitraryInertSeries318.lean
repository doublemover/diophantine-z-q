module
public import IntegralScaledSeries318
public import InertClosedDisc318
public import CompressedOrientation318
public section
namespace ArbitraryInertSeries318
open PowerSeries IntegralRingEvaluation318 InertIntegers318
variable (p : ℕ) [Fact p.Prime] (nonsquare : ¬∃x : ZMod p, x^2=2)
variable (hp : 19 ≤ p)

@[expose] noncomputable def H (D : Integers p nonsquare) : PowerSeries (Integers p nonsquare) :=
  IntegralScaledSeries318.H p hp (padicIntEmbedding p nonsquare) D
@[expose] noncomputable def B (D : Integers p nonsquare) : PowerSeries (Integers p nonsquare) :=
  IntegralScaledSeries318.B p hp (padicIntEmbedding p nonsquare) D
@[expose] noncomputable def parameter (D : Integers p nonsquare) : Integers p nonsquare :=
  IntegralScaledSeries318.parameter p D
@[expose] noncomputable def integral (D : Integers p nonsquare) : PowerSeries (Integers p nonsquare) :=
  IntegralScaledSeries318.integral p hp (padicIntEmbedding p nonsquare) D
@[expose] noncomputable def branch (D : Integers p nonsquare) : PowerSeries (Integers p nonsquare) :=
  IntegralScaledSeries318.branch p hp (padicIntEmbedding p nonsquare) D

theorem H_restricted (D : Integers p nonsquare) : IsRestricted 1 (H p nonsquare hp D) :=
  IntegralScaledSeries318.H_restricted p hp _ D (padicIntEmbedding_isometry p nonsquare)

theorem integral_restricted (D : Integers p nonsquare) : IsRestricted 1 (integral p nonsquare hp D) :=
  IntegralScaledSeries318.integral_restricted p hp _ D (padicIntEmbedding_isometry p nonsquare)

theorem branch_restricted (D : Integers p nonsquare) : IsRestricted 1 (branch p nonsquare hp D) :=
  IntegralScaledSeries318.branch_restricted p hp _ D (padicIntEmbedding_isometry p nonsquare)

theorem map_H (D : Integers p nonsquare) :
    (H p nonsquare hp D).map (embedding p nonsquare) =
      rescale (embedding p nonsquare (parameter p nonsquare D))
        (GenericFormalDifferential318.H (K := InertCompletion318.Field p nonsquare)) :=
  IntegralScaledSeries318.map_H p hp _ D (embedding p nonsquare)
    (InertPadicEmbedding318.padicEmbedding p nonsquare) (padicIntEmbedding_coe p nonsquare)

theorem map_integral (D : Integers p nonsquare) :
    (integral p nonsquare hp D).map (embedding p nonsquare) =
      GenericFormalDifferential318.integral (embedding p nonsquare (parameter p nonsquare D)) :=
  IntegralScaledSeries318.map_integral p hp _ D (embedding p nonsquare)
    (InertPadicEmbedding318.padicEmbedding p nonsquare) (padicIntEmbedding_coe p nonsquare)

theorem map_branch (D : Integers p nonsquare) :
    (branch p nonsquare hp D).map (embedding p nonsquare) =
      GenericFormalDifferential318.branch (embedding p nonsquare (parameter p nonsquare D)) :=
  IntegralScaledSeries318.map_branch p hp _ D (embedding p nonsquare)
    (InertPadicEmbedding318.padicEmbedding p nonsquare) (padicIntEmbedding_coe p nonsquare)

theorem formal_addition (D : Integers p nonsquare) :
    (integral p nonsquare hp D).subst
      (IntegralFormalAddition318.f (parameter p nonsquare D) (branch p nonsquare hp D)) =
    (integral p nonsquare hp D).subst (IntegralFormalAddition318.x (R := Integers p nonsquare)) +
      (integral p nonsquare hp D).subst (IntegralFormalAddition318.a (R := Integers p nonsquare)) :=
  IntegralScaledSeries318.formal_addition p hp _ D (embedding p nonsquare)
    (InertPadicEmbedding318.padicEmbedding p nonsquare) (padicIntEmbedding_coe p nonsquare)
    (embedding_injective p nonsquare)

/-- The literal source parameter 11−6√2 in the actual inert integral ring. -/
@[expose] noncomputable def sourceD : Integers p nonsquare :=
  ⟨InertCompletion318.embedding p nonsquare CompressedOrientation318.D, by
    change ‖InertCompletion318.embedding p nonsquare (ConcreteG8Domain.pair 11 (-6))‖ ≤ 1
    rw [InertCompletion318.norm_pair]
    simp only [Rat.cast_ofNat, Rat.cast_neg, norm_neg]
    exact max_le (JTail318.norm_nat_le_one p 11) (JTail318.norm_nat_le_one p 6)⟩

@[simp] theorem sourceD_embedding :
    embedding p nonsquare (sourceD p nonsquare) =
      InertCompletion318.embedding p nonsquare CompressedOrientation318.D := rfl

/-- No Qp descent assumption remains for the literal source integral. -/
theorem source_integral_hasSum (t : Integers p nonsquare) :
    HasSum (fun n : ℕ => coeff n (integral p nonsquare hp (sourceD p nonsquare))*t^n)
      (eval (Integers p nonsquare) (integral p nonsquare hp (sourceD p nonsquare)) t) :=
  eval_hasSum _ _ (integral_restricted p nonsquare hp _) t

end ArbitraryInertSeries318
#print axioms ArbitraryInertSeries318.map_integral
#print axioms ArbitraryInertSeries318.map_branch
#print axioms ArbitraryInertSeries318.formal_addition
#print axioms ArbitraryInertSeries318.sourceD_embedding
#print axioms ArbitraryInertSeries318.source_integral_hasSum
