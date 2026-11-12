module
public import ActualSieveEulerProduct318
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
public section
noncomputable section
namespace ActualGaussianDirichlet318
open scoped Topology
set_option maxHeartbeats 1000000

/-- The original Gaussian splitting character, constructed from the actual
modulo-four character, not an unspecified quadratic L-function. -/
@[expose] def character : DirichletCharacter ℂ 4 :=
  ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

lemma character_apply (n : ℕ) : character n=(ZMod.χ₄ (n : ZMod 4):ℂ) := rfl

lemma character_neg_one : character (-1 : ZMod 4)= -1 := by
  change ((ZMod.χ₄ (-1 : ZMod 4):ℤ):ℂ)= -1
  rw [show ZMod.χ₄ (-1 : ZMod 4)= -1 by decide]
  norm_num

lemma character_nontrivial : character≠1 := by
  intro he
  have hh := congrArg (fun χ : DirichletCharacter ℂ 4 => χ (-1 : ZMod 4)) he
  rw [character_neg_one,MulChar.one_apply (isUnit_neg.mpr isUnit_one)] at hh
  norm_num at hh

/-- The character in the original finite quadric density is precisely the
same modulo-four character entering this analytic L-function. -/
theorem original_character (p : ℕ) [Fact p.Prime] (hp2 : p≠2) :
    (quadraticChar (ZMod p) (-1 : ZMod p):ℂ)=character p := by
  rw [character_apply]
  have hF : ringChar (ZMod p)≠2 := by simpa only [ringChar_zmod_n] using hp2
  exact_mod_cast (show quadraticChar (ZMod p) (-1 : ZMod p)=ZMod.χ₄ (p : ZMod 4) from
    by simpa only [ZMod.card] using quadraticChar_neg_one hF)

/-- No nonvanishing hypothesis is delegated to a later caller. -/
theorem value_one_nonzero : DirichletCharacter.LFunction character 1≠0 :=
  DirichletCharacter.LFunction_apply_one_ne_zero (χ := character) character_nontrivial

theorem value_nonzero (s : ℂ) (hs : 1≤s.re) :
    DirichletCharacter.LFunction character s≠0 :=
  DirichletCharacter.LFunction_ne_zero_of_one_le_re character (Or.inl character_nontrivial) hs

theorem continuous_at_one : ContinuousAt (DirichletCharacter.LFunction character) 1 :=
  (DirichletCharacter.differentiable_LFunction character_nontrivial).continuous.continuousAt

end ActualGaussianDirichlet318
