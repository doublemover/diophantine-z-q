module
public import PELOriginalFiniteThetaGeneration318
public import Mathlib.LinearAlgebra.Projectivization.Basic
public section
noncomputable section
namespace PELOriginalAllLevelProjectiveMap318
open QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalThetaConvergence318 PELOriginalLevelTheta318
open PELOriginalPolarizationTransitions318 PELOriginalPolarizationLineBundle318
open PELOriginalPolarizationPowerBundle318 PELOriginalThetaHermitianGauge318
open PELOriginalThetaGaugeMatrix318 PELOriginalSiegelNormalization318
open PELOriginalLevelPowerSections318 PELOriginalAutomorphyRepresentatives318
variable (τ:ℂ) (hτ:0<τ.im) (n:ℕ)
abbrev Coordinates (n:ℕ):=Label (n+2)→ℂ
@[expose] def coverVector (z:ComplexVectors):Coordinates n:=fun r=>value τ hτ (n+2) r z
@[expose] def baseVector (q:Base τ):Coordinates n:=fun r=>(levelSection τ hτ (n+2) r q).2
lemma baseVector_nonzero (q:Base τ):baseVector τ hτ n q≠0:=by
  obtain ⟨r,hr⟩:=PELOriginalFiniteThetaGeneration318.finite_basepoint_free τ hτ n q
  intro h
  exact hr (congrFun h r)
lemma coverVector_nonzero (z:ComplexVectors):coverVector τ hτ n z≠0:=by
  let q:Base τ:=projection (P τ) z
  let a:ComplexVectors:=(core τ hτ).indexAt q
  have ha:q∈baseSet τ hτ a:=(core τ hτ).mem_baseSet_at q
  obtain ⟨r,hr⟩:=PELOriginalFiniteThetaGeneration318.finite_basepoint_free τ hτ n q
  let l:PELOriginalPolarizationAutomorphy318.L τ hτ:=shiftTo τ hτ a z
  have hs:z+l.val=chart τ hτ a q:=by
    rw [l,shiftTo_value τ hτ a z ha];abel
  intro h
  have hz:value τ hτ (n+2) r z=0:=congrFun h r
  have hf:=PELOriginalLevelPowerSections318.original_automorphy τ hτ (n+2) r l z
  rw [hs,hz,mul_zero] at hf
  exact hr hf
@[expose] def projectiveMap (q:Base τ):Projectivization ℂ (Coordinates n):=
  Projectivization.mk ℂ (baseVector τ hτ n q) (baseVector_nonzero τ hτ n q)
@[expose] def coveringMap (z:ComplexVectors):Projectivization ℂ (Coordinates n):=
  Projectivization.mk ℂ (coverVector τ hτ n z) (coverVector_nonzero τ hτ n z)

/-- The projective class is independent of the selected original gauge:
its lift is the N² literal entire functions, and the gauge change is
one common nonzero scalar from the actual original power-line action. -/
theorem original_covering_square (z:ComplexVectors):
    projectiveMap τ hτ n (projection (P τ) z)=coveringMap τ hτ n z:=by
  let q:Base τ:=projection (P τ) z
  let a:ComplexVectors:=(core τ hτ).indexAt q
  have ha:q∈baseSet τ hτ a:=(core τ hτ).mem_baseSet_at q
  let l:PELOriginalPolarizationAutomorphy318.L τ hτ:=shiftTo τ hτ a z
  have hs:z+l.val=chart τ hτ a q:=by
    rw [l,shiftTo_value τ hτ a z ha]
    abel
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨PELOriginalPolarizationAutomorphy318.factor τ hτ l z^(n+2),?_⟩
  ext r
  change PELOriginalPolarizationAutomorphy318.factor τ hτ l z^(n+2)*value τ hτ (n+2) r z=
    value τ hτ (n+2) r (chart τ hτ a q)
  rw [←hs,PELOriginalLevelPowerSections318.original_automorphy]


end PELOriginalAllLevelProjectiveMap318
