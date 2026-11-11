module
public import PELOriginalScaledThetaHolomorphy318
public import PELOriginalThetaQuasiperiods318
public import Mathlib.Data.ZMod.Basic
public section
noncomputable section
namespace PELOriginalLevelTheta318
open QuaternionicRealPeriod318 PELOriginalThetaConvergence318
open PELOriginalThetaQuasiperiods318 PELOriginalSiegelMatrix318
open PELOriginalSiegelNormalization318 PELOriginalSymplecticCoordinates318
variable (τ:ℂ) (hτ:0<τ.im)
abbrev Label (N:ℕ):=ZMod N×ZMod N
@[expose] def residue (N:ℕ) (k:Index):Label N:=((k.1:ZMod N),(k.2:ZMod N))
@[expose] def shift (N:ℕ) (b:Index):Index:=((N:ℤ)*b.1,(N:ℤ)*b.2)
lemma residue_shift (N:ℕ) (k b:Index):residue N (k+shift N b)=residue N k:=by
  apply Prod.ext <;> simp [residue,shift,Int.cast_add,Int.cast_mul]
variable (N:ℕ) [NeZero N]
lemma inverse_level_positive:0<(1/(N:ℝ)):=by
  have hn:0<(N:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  positivity
lemma label_card:Fintype.card (Label N)=N^2:=by
  simp [Label,Fintype.card_prod,pow_two]
@[expose] def accepts (r:Label N) (k:Index):Prop:=residue N k=r
instance (r:Label N):DecidablePred (accepts N r):=fun _=>inferInstance
@[expose] def levelTerm (r:Label N) (k:Index) (z:ComplexVectors):ℂ:=
  PELOriginalScaledThetaHolomorphy318.selectedTerm τ (1/(N:ℝ)) (accepts N r) k z
@[expose] def levelTheta (r:Label N) (z:ComplexVectors):ℂ:=
  PELOriginalScaledThetaHolomorphy318.selectedTheta τ (1/(N:ℝ)) (accepts N r) z
lemma summable (r:Label N) (z:ComplexVectors):Summable (fun k=>levelTerm τ N r k z):=
  PELOriginalScaledThetaHolomorphy318.selected_summable τ hτ (1/(N:ℝ))
    (inverse_level_positive N) (accepts N r) z
lemma holomorphic (r:Label N):Differentiable ℂ (levelTheta τ N r):=
  PELOriginalScaledThetaHolomorphy318.selected_holomorphic τ hτ (1/(N:ℝ))
    (inverse_level_positive N) (accepts N r)
lemma scaled_term_integer (k m:Index) (z:ComplexVectors):
    PELOriginalScaledThetaConvergence318.term τ (1/(N:ℝ)) k (z+integerVector m)=
      PELOriginalScaledThetaConvergence318.term τ (1/(N:ℝ)) k z:=by
  apply Complex.exp_eq_exp_iff_exp_sub_eq_one.mpr
  apply Complex.exp_eq_one_iff.mpr
  refine ⟨k.1*m.1+k.2*m.2,?_⟩
  simp only [PELOriginalScaledThetaConvergence318.term,linear,integerVector,
    Pi.add_apply,Matrix.cons_val_zero,Matrix.cons_val_one]
  push_cast
  ring
lemma scaled_term_period (k b:Index) (z:ComplexVectors):
    PELOriginalScaledThetaConvergence318.term τ (1/(N:ℝ)) k (z+periodVector τ b)=
      multiplier τ b z^N*
        PELOriginalScaledThetaConvergence318.term τ (1/(N:ℝ)) (k+shift N b) z:=by
  have hn:(N:ℂ)≠0:=by exact_mod_cast NeZero.ne N
  simp only [PELOriginalScaledThetaConvergence318.term,multiplier,
    ←Complex.exp_nat_mul,←Complex.exp_add]
  congr 1
  simp only [quadratic,linear,periodVector,shift,Prod.fst_add,Prod.snd_add,Pi.add_apply]
  push_cast
  have hs:omega τ 1 0=omega τ 0 1:=congrFun (congrFun (PELOriginalSiegelMatrix318.symmetric τ) 0) 1
  rw [hs]
  field_simp [hn]
  ring
lemma term_integer (r:Label N) (k m:Index) (z:ComplexVectors):
    levelTerm τ N r k (z+integerVector m)=levelTerm τ N r k z:=by
  unfold levelTerm PELOriginalScaledThetaHolomorphy318.selectedTerm
  split_ifs <;> simp only [scaled_term_integer]
lemma term_period (r:Label N) (k b:Index) (z:ComplexVectors):
    levelTerm τ N r k (z+periodVector τ b)=
      multiplier τ b z^N*levelTerm τ N r (k+shift N b) z:=by
  simp only [levelTerm,PELOriginalScaledThetaHolomorphy318.selectedTerm,accepts,residue_shift]
  split_ifs
  · exact scaled_term_period τ N k b z
  · simp
lemma theta_integer (r:Label N) (m:Index) (z:ComplexVectors):
    levelTheta τ N r (z+integerVector m)=levelTheta τ N r z:=
  tsum_congr (fun k=>term_integer τ N r k m z)
lemma theta_period (r:Label N) (b:Index) (z:ComplexVectors):
    levelTheta τ N r (z+periodVector τ b)=multiplier τ b z^N*levelTheta τ N r z:=by
  change (∑'k:Index,levelTerm τ N r k (z+periodVector τ b))=_
  simp_rw [term_period]
  rw [tsum_mul_left]
  congr 1
  exact (Equiv.addRight (shift N b)).tsum_eq (fun k:Index=>levelTerm τ N r k z)

/-- All N² actual characteristic functions transform by the SAME level-N
multiplier on the FULL original normalized lattice. -/
theorem original_period (r:Label N) (p:Pair) (z:ComplexVectors):
    levelTheta τ N r (z+standardPeriod τ p)=
      multiplier τ (p.2 0,p.2 1) z^N*levelTheta τ N r z:=by
  rw [original_standard_decomposition]
  have he:z+(integerVector (p.1 0,p.1 1)+periodVector τ (p.2 0,p.2 1))=
      (z+periodVector τ (p.2 0,p.2 1))+integerVector (p.1 0,p.1 1):=by abel
  rw [he,theta_integer,theta_period]
end PELOriginalLevelTheta318
