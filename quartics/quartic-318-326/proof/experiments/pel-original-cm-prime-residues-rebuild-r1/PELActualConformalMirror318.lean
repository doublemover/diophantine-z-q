module
public import PELActualInteriorConformal318
public import ReflectedConformalChart318
public section
noncomputable section
namespace PELActualConformalMirror318
open Set Metric
open scoped ComplexConjugate
open PELMaximalActualComplexDomain318 PELMaximalHalfOctagonCoordinates318
open PELMaximalHalfOctagonShape318 PELActualInteriorConformal318
set_option maxHeartbeats 2400000

lemma strict_reflection (z : ℂ) : -conj z∈strictPolygon ↔ z∈strictPolygon := by
  simp only [strictPolygon,Set.mem_setOf_eq,Complex.neg_re,Complex.conj_re,
    Complex.neg_im,Complex.conj_im,neg_neg]
  constructor <;> rintro ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩ <;>
    refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> linarith

/-- Reflection preserves the actual OPEN complex domain as well as its
closed half-cut. This is an identity in the original complex coordinate. -/
theorem openDomain_reflection (z : ℂ) : -conj z∈openDomain ↔ z∈openDomain := by
  have forward (w : ℂ) (hw : w∈openDomain) : -conj w∈openDomain := by
    refine ⟨by simpa using hw.1,?_⟩
    have hc := mirror_coordinates (⟨w,hw.1⟩ : QuaternionicJointPeriodTopology318.HalfPlane)
    change coordinates (-conj w)=(-(coordinates w).1,(coordinates w).2) at hc
    change centerHomeomorph (coordinates (-conj w))∈strictPolygon
    rw [hc,center_reflection]
    exact (strict_reflection _).mpr hw.2
  constructor
  · intro h
    simpa using forward (-conj z) h
  · exact forward z

/-- The genuine normalized Riemann map has the reflection required by
later boundary folding. Its analytic inverse, original source and positive
real derivative are all retained; no boundary extension is asserted. -/
theorem actual_symmetric_conformal_chart :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, e.source=openDomain ∧ e.target=ball 0 1 ∧ e center=0 ∧
      (∀ z∈openDomain,AnalyticAt ℂ e z) ∧ (∀ w∈ball (0:ℂ) 1,AnalyticAt ℂ e.symm w) ∧
      (deriv e center).im=0 ∧ 0<(deriv e center).re ∧
      (∀ z∈openDomain,e (-conj z)= -conj (e z)) := by
  obtain ⟨e,hs,ht,hzero,ha,hi,him,hre⟩ := actual_normalized_conformal_chart
  refine ⟨e,hs,ht,hzero,ha,hi,him,hre,?_⟩
  exact ReflectedConformalChart318.normalized_mirror openDomain_open openDomain_reflection
    e hs ht ha hi center_mem center_fixed hzero him hre
end PELActualConformalMirror318
