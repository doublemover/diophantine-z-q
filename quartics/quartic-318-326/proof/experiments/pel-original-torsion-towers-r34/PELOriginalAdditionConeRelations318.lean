module
public import PELOriginalAdditionTensorMap318
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public section
noncomputable section
namespace PELOriginalAdditionConeRelations318
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCubicAdditionConstants318 PELOriginalAdditionTensorMap318

abbrev Variables (N : ℕ) := Label N × Label N
abbrev Polynomials (N : ℕ) := MvPolynomial (Variables N) ℂ
abbrev Parameters := ℂ × (ComplexVectors × ComplexVectors)
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- Arbitrary scalar multiples of ALL independent original Segre pairs.
The relation model does not select an original witness as part of a point. -/
@[expose] def vector (N : ℕ) [NeZero N] (p : Parameters) : Variables N → ℂ :=
  p.1 • segre (fun r => value τ hτ N r p.2.1) (fun s => value τ hτ N s p.2.2)
@[expose] def evaluation (N : ℕ) [NeZero N] (p : Parameters) :
    Polynomials N →ₐ[ℂ] ℂ := MvPolynomial.aeval (vector τ hτ N p)
@[expose] def relations (N : ℕ) [NeZero N] : Ideal (Polynomials N) :=
  ⨅ p : Parameters, RingHom.ker (evaluation τ hτ N p).toRingHom

lemma mem_relations (N : ℕ) [NeZero N] (f : Polynomials N) :
    f ∈ relations τ hτ N ↔ ∀ p, evaluation τ hτ N p f = 0 := by
  simp only [relations,Ideal.mem_iInf,RingHom.mem_ker,AlgHom.coe_toRingHom]

@[expose] def coordinatePolynomial (i : Variables 3) : Polynomials 6 :=
  ∑ u : Label 6, ∑ v : Label 6,
    MvPolynomial.C (additionConstant τ hτ i.1 i.2 u v) * MvPolynomial.X (u,v)
@[expose] def substitution : Polynomials 3 →ₐ[ℂ] Polynomials 6 :=
  MvPolynomial.aeval (coordinatePolynomial τ hτ)
@[expose] def sumDifference (p : Parameters) : Parameters :=
  (p.1,(p.2.1+p.2.2,p.2.1-p.2.2))

lemma sumDifference_surjective : Function.Surjective sumDifference := by
  intro p
  refine ⟨(p.1,((1/2 : ℂ) • (p.2.1+p.2.2),(1/2 : ℂ) • (p.2.1-p.2.2))), ?_⟩
  refine Prod.ext rfl (Prod.ext ?_ ?_) <;> ext k <;>
    simp only [sumDifference,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul] <;> ring

lemma coordinate_evaluation (p : Parameters) (i : Variables 3) :
    evaluation τ hτ 6 p (coordinatePolynomial τ hτ i) =
      vector τ hτ 3 (sumDifference p) i := by
  simp only [evaluation,coordinatePolynomial,map_sum,map_mul,MvPolynomial.aeval_C,MvPolynomial.aeval_X]
  change (∑ u : Label 6, ∑ v : Label 6,
    additionConstant τ hτ i.1 i.2 u v *
      (p.1 * (value τ hτ 6 u p.2.1 * value τ hτ 6 v p.2.2))) =
    p.1 * (value τ hτ 3 i.1 (p.2.1+p.2.2) * value τ hτ 3 i.2 (p.2.1-p.2.2))
  rw [actual_addition_formula]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  ring

/-- Equality on the WHOLE polynomial algebra, not just chosen generators. -/
lemma evaluation_square (p : Parameters) :
    (evaluation τ hτ 6 p).comp (substitution τ hτ) =
      evaluation τ hτ 3 (sumDifference p) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply,substitution,MvPolynomial.aeval_X,evaluation]
  exact coordinate_evaluation τ hτ p i

/-- Exact inverse-image equality of the independently defined relation ideals.
The reverse direction uses the actual inverse linear change of variables. -/
theorem relations_comap :
    (relations τ hτ 6).comap (substitution τ hτ).toRingHom = relations τ hτ 3 := by
  ext f
  change substitution τ hτ f ∈ relations τ hτ 6 ↔ f ∈ relations τ hτ 3
  rw [mem_relations,mem_relations]
  have hs (p : Parameters) :
      evaluation τ hτ 6 p (substitution τ hτ f) =
        evaluation τ hτ 3 (sumDifference p) f :=
    DFunLike.congr_fun (evaluation_square τ hτ p) f
  simp only [hs]
  constructor
  · intro h p
    obtain ⟨q,rfl⟩ := sumDifference_surjective p
    exact h q
  · intro h p
    exact h (sumDifference p)

abbrev ConeRing (N : ℕ) [NeZero N] := Polynomials N ⧸ relations τ hτ N

/-- A genuine complex algebra map between the independent relation quotients.
The source of its contravariant scheme morphism is the full level-six Segre
relation model; identifying that with the original cubic candidate product
is a separate obligation. -/
@[expose] def coneMap : ConeRing τ hτ 3 →ₐ[ℂ] ConeRing τ hτ 6 :=
  Ideal.quotientMapₐ (relations τ hτ 6) (substitution τ hτ)
    (relations_comap τ hτ).ge

lemma coneMap_mk (f : Polynomials 3) :
    coneMap τ hτ (Ideal.Quotient.mk (relations τ hτ 3) f) =
      Ideal.Quotient.mk (relations τ hτ 6) (substitution τ hτ f) := rfl

theorem coneMap_injective : Function.Injective (coneMap τ hτ) := by
  exact Ideal.quotientMap_injective' (relations_comap τ hτ).le
end PELOriginalAdditionConeRelations318
