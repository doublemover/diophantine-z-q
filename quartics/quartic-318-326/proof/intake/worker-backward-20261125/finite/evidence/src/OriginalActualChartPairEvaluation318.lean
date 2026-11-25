module

public import OriginalRetainedProjectiveAffinePoints318
public import Mathlib.RingTheory.TensorProduct.Maps

@[expose] public section
noncomputable section

namespace OriginalActualChartPairEvaluation318

open AlgebraicGeometry CategoryTheory Limits
open OriginalRetainedProjectiveAffinePoints318
open scoped TensorProduct

variable {ι κ : Type} (I : Ideal (R ι)) (J : Ideal (R κ))
local notation "A" => Q I
local notation "B" => Q J
local notation "SA" => Spec (CommRingCat.of A)
local notation "SB" => Spec (CommRingCat.of B)
local notation "SC" => Spec (CommRingCat.of ℂ)
local notation "ST" => Spec (CommRingCat.of (A ⊗[ℂ] B))
local notation "pp" => pullbackSpecIso ℂ A B

/-- Every element of the actual quotient chart, not just its indexed
coordinate generators, gives a continuous scalar evaluation. -/
theorem quotient_eval_continuous (x : A) : Continuous (fun r : Rows I => evalRow I r x) := by
  obtain ⟨f,rfl⟩ := Ideal.Quotient.mk_surjective x
  have h : (fun r : Rows I => evalRow I r (Ideal.Quotient.mk I f)) =
      (fun r : Rows I => MvPolynomial.aeval r.val f) := by
    funext r
    exact DFunLike.congr_fun (evalRow_comp I r) f
  rw [h]
  exact (eval_continuous f).comp continuous_subtype_val

/-- Evaluation of the actual tensor chart of two original points. -/
def pairRead (r : Rows I) (s : Rows J) : A ⊗[ℂ] B →ₐ[ℂ] ℂ :=
  Algebra.TensorProduct.lift (evalRow I r) (evalRow J s) (fun _ _ => Commute.all _ _)

theorem tensor_values_continuous (c : A ⊗[ℂ] B) :
    Continuous (fun rs : Rows I × Rows J => pairRead I J rs.1 rs.2 c) := by
  induction c using TensorProduct.induction_on with
  | zero =>
      simpa only [map_zero] using
        (continuous_const : Continuous (fun _ : Rows I × Rows J => (0:ℂ)))
  | tmul a b =>
      simp only [pairRead,Algebra.TensorProduct.lift_tmul]
      exact continuous_mul.comp₂
        ((quotient_eval_continuous I a).comp continuous_fst)
        ((quotient_eval_continuous J b).comp continuous_snd)
  | add a b ha hb =>
      simpa only [map_add] using ha.fun_add hb

def firstPoint (r : Rows I) : SC ⟶ SA := Spec.map (CommRingCat.ofHom (evalRow I r).toRingHom)
def secondPoint (s : Rows J) : SC ⟶ SB := Spec.map (CommRingCat.ofHom (evalRow J s).toRingHom)
def tensorPoint (r : Rows I) (s : Rows J) : SC ⟶ ST :=
  Spec.map (CommRingCat.ofHom (pairRead I J r s).toRingHom)

/-- Exact first leg of the genuine scheme fibre product. The
underlying expressions agree as whole Spec(C) arrows. -/
theorem projection_fst (r : Rows I) (s : Rows J) :
    tensorPoint I J r s≫pp.inv≫pullback.fst _ _ = firstPoint I r := by
  rw [pullbackSpecIso_inv_fst]
  unfold tensorPoint firstPoint
  rw [←Spec.map_comp,←CommRingCat.ofHom_comp]
  have pin : (pairRead I J r s).toRingHom.comp
      (Algebra.TensorProduct.includeLeftRingHom : A→+*(A⊗[ℂ]B)) = (evalRow I r).toRingHom := by
    apply RingHom.ext
    intro x
    change pairRead I J r s (x ⊗ₜ[ℂ] (1:B))=evalRow I r x
    simp only [pairRead,Algebra.TensorProduct.lift_tmul,map_one,mul_one]
  rw [pin]

theorem projection_snd (r : Rows I) (s : Rows J) :
    tensorPoint I J r s≫pp.inv≫pullback.snd _ _ = secondPoint J s := by
  rw [pullbackSpecIso_inv_snd]
  unfold tensorPoint secondPoint
  rw [←Spec.map_comp,←CommRingCat.ofHom_comp]
  have pin : (pairRead I J r s).toRingHom.comp
      ((Algebra.TensorProduct.includeRight : B→ₐ[ℂ] A⊗[ℂ]B).toRingHom) = (evalRow J s).toRingHom := by
    apply RingHom.ext
    intro x
    change pairRead I J r s ((1:A) ⊗ₜ[ℂ] x)=evalRow J s x
    simp only [pairRead,Algebra.TensorProduct.lift_tmul,map_one,one_mul]
  rw [pin]

/-- The tensor-field evaluation is exactly the based geometric pair
selected by its two original whole projections, no extra point. -/
theorem pair_exact (r : Rows I) (s : Rows J)
    (base : firstPoint I r≫Spec.map (CommRingCat.ofHom (algebraMap ℂ A)) =
      secondPoint J s≫Spec.map (CommRingCat.ofHom (algebraMap ℂ B))) :
    tensorPoint I J r s≫pp.inv =
      pullback.lift (firstPoint I r) (secondPoint J s) base := by
  apply pullback.hom_ext
  · rw [pullback.lift_fst,Category.assoc,projection_fst]
  · rw [pullback.lift_snd,Category.assoc,projection_snd]

end OriginalActualChartPairEvaluation318
