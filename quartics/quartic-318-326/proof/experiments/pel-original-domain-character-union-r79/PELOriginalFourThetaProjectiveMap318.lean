module
public import PELOriginalFourThetaGeneration318
public import Mathlib.LinearAlgebra.Projectivization.Basic
public section
noncomputable section
namespace PELOriginalFourThetaProjectiveMap318
open QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalThetaConvergence318 PELOriginalLevelTheta318
open PELOriginalPolarizationTransitions318 PELOriginalPolarizationLineBundle318
open PELOriginalPolarizationPowerBundle318 PELOriginalThetaHermitianGauge318
open PELOriginalThetaGaugeMatrix318 PELOriginalSiegelNormalization318
open PELOriginalLevelPowerSections318 PELOriginalAutomorphyRepresentatives318
variable (τ:ℂ) (hτ:0<τ.im)
abbrev Coordinates:=Label 2→ℂ
@[expose] def coverVector (z:ComplexVectors):Coordinates:=fun r=>value τ hτ 2 r z
@[expose] def baseVector (q:Base τ):Coordinates:=fun r=>(levelSection τ hτ 2 r q).2
lemma baseVector_nonzero (q:Base τ):baseVector τ hτ q≠0:=by
  obtain ⟨r,hr⟩:=PELOriginalFourThetaGeneration318.four_sections_basepoint_free τ hτ q
  intro h
  exact hr (congrFun h r)
lemma coverVector_nonzero (z:ComplexVectors):coverVector τ hτ z≠0:=by
  obtain ⟨r,hr⟩:=PELOriginalFourThetaGeneration318.finite_coordinate_nonzero τ hτ
    (normalization τ hτ z)
  intro h
  have he:=congrFun h r
  have hn:gauge (bilinearMap τ) (normalization τ hτ z)^2*
      levelTheta τ 2 r (normalization τ hτ z)≠0:=
    mul_ne_zero (pow_ne_zero _ (gauge_nonzero _ _)) hr
  exact hn he
@[expose] def projectiveMap (q:Base τ):Projectivization ℂ Coordinates:=
  Projectivization.mk ℂ (baseVector τ hτ q) (baseVector_nonzero τ hτ q)
@[expose] def coveringMap (z:ComplexVectors):Projectivization ℂ Coordinates:=
  Projectivization.mk ℂ (coverVector τ hτ z) (coverVector_nonzero τ hτ z)

/-- The projective class is independent of the selected original gauge:
its lift is the FOUR literal entire functions, and the gauge change is
one common nonzero scalar from the actual original power-line action. -/
theorem original_covering_square (z:ComplexVectors):
    projectiveMap τ hτ (projection (P τ) z)=coveringMap τ hτ z:=by
  let q:Base τ:=projection (P τ) z
  let a:ComplexVectors:=(core τ hτ).indexAt q
  have ha:q∈baseSet τ hτ a:=(core τ hτ).mem_baseSet_at q
  let l:PELOriginalPolarizationAutomorphy318.L τ hτ:=shiftTo τ hτ a z
  have hs:z+l.val=chart τ hτ a q:=by
    rw [l,shiftTo_value τ hτ a z ha]
    abel
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨PELOriginalPolarizationAutomorphy318.factor τ hτ l z^2,?_⟩
  ext r
  change PELOriginalPolarizationAutomorphy318.factor τ hτ l z^2*value τ hτ 2 r z=
    value τ hτ 2 r (chart τ hτ a q)
  rw [←hs,PELOriginalLevelPowerSections318.original_automorphy]

lemma residue_neg_two (k:Index):residue 2 (-k)=residue 2 k:=by
  have h:∀x:ZMod 2,-x=x:=by
    intro x
    apply neg_eq_iff_add_eq_zero.mpr
    rw [←two_mul]
    norm_num
  apply Prod.ext <;> simp [residue,h]
lemma theta_even (r:Label 2) (z:ComplexVectors):
    levelTheta τ 2 r (-z)=levelTheta τ 2 r z:=by
  have he:∀k:Index,levelTerm τ 2 r k (-z)=levelTerm τ 2 r (-k) z:=by
    intro k
    simp only [levelTerm,PELOriginalScaledThetaHolomorphy318.selectedTerm,accepts,residue_neg_two]
    split_ifs
    · simp only [PELOriginalScaledThetaConvergence318.term]
      congr 1
      simp only [quadratic,linear,Pi.neg_apply,Prod.fst_neg,Prod.snd_neg,Int.cast_neg]
      ring
    · rfl
  change (∑'k:Index,levelTerm τ 2 r k (-z))=_
  simp_rw [he]
  exact (Equiv.neg Index).tsum_eq (fun k:Index=>levelTerm τ 2 r k z)
lemma value_even (r:Label 2) (z:ComplexVectors):value τ hτ 2 r (-z)=value τ hτ 2 r z:=by
  simp only [value,normalizedValue,map_neg,theta_even,gauge,LinearMap.neg_apply,neg_neg]

/-- The concrete four-coordinate map is invariant under inversion. It
is the level-two Kummer-type map, NOT a proved embedding of the original
surface. Point/tangent separation requires a distinct higher-power step. -/
theorem inversion (z:ComplexVectors):
    projectiveMap τ hτ (projection (P τ) (-z))=
      projectiveMap τ hτ (projection (P τ) z):=by
  rw [original_covering_square,original_covering_square]
  have he:coverVector τ hτ (-z)=coverVector τ hτ z:=funext (fun r=>value_even τ hτ r z)
  simp only [coveringMap,he]
end PELOriginalFourThetaProjectiveMap318
