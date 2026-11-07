module
public import PoincareCurvature318
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
public import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
public import Mathlib.Analysis.Complex.RealDeriv
public section
noncomputable section
open Filter Set CompactMetricComparison318 ConformalCurvature318 FiniteLaplacian318
open InnerProductSpace
open scoped Topology
namespace HarmonicAxis318
set_option maxHeartbeats 0

@[expose] def coord (w:ℝ×ℝ) : ℂ := (w.1:ℂ)+w.2*Complex.I

theorem line_second (f:ℂ→ℝ) (hf:ContDiffAt ℝ 2 f 0) (v:ℂ) :
    deriv (deriv (fun t:ℝ=>f (t • v))) 0=iteratedFDeriv ℝ 2 f 0 (fun _=>v) := by
  have hc:ContDiffAt ℝ 2 (fun t:ℝ=>t • v) 0:=contDiffAt_id.smul contDiffAt_const
  have hfg:ContDiffAt ℝ 2 f ((0:ℝ) • v):=by simpa using hf
  have hd:deriv (fun t:ℝ=>t • v)=(fun _=>v) := by
    funext t
    simpa using ((hasDerivAt_id t).smul_const v).deriv
  have hh:=iteratedDeriv_vcomp_two hfg hc
  simp only [iteratedDeriv_succ,iteratedDeriv_zero,hd,deriv_const,zero_smul,map_zero,add_zero] at hh
  exact hh

theorem laplacian_eq (f:ℂ→ℝ) (hf:ContDiffAt ℝ 2 f 0) :
    laplacianAtOrigin (fun w=>f (coord w))=Laplacian.laplacian f 0 := by
  have hx:(fun t:ℝ=>f (coord (t,0)))=(fun t=>f (t • (1:ℂ))) := by
    funext t;simp [coord,Complex.real_smul]
  have hy:(fun t:ℝ=>f (coord (0,t)))=(fun t=>f (t • Complex.I)) := by
    funext t;simp [coord,Complex.real_smul]
  rw [laplacianAtOrigin,hx,hy,line_second f hf 1,line_second f hf Complex.I,
    laplacian_eq_iteratedFDeriv_complexPlane]
  congr 1 <;> congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem harmonic_laplacian (f:ℂ→ℝ) (hf:HarmonicAt f 0) :
    laplacianAtOrigin (fun w=>f (coord w))=0 := by
  rw [laplacian_eq f hf.1]
  exact hf.2.eq_of_nhds

theorem axisC2 (f:ℂ→ℝ) (hf:ContDiffAt ℝ 2 f 0) :
    AxisC2 (fun w=>f (coord w)) := by
  have hx:ContDiffAt ℝ 2 (fun t:ℝ=>(t:ℂ)) 0:=Complex.ofRealCLM.contDiff.contDiffAt
  constructor
  · have hh:=hf.comp (f:=fun t:ℝ=>(t:ℂ)) 0 hx
    simpa only [coord,Complex.ofReal_zero,zero_mul,add_zero,Function.comp_def] using hh
  · have hy:ContDiffAt ℝ 2 (fun t:ℝ=>(t:ℂ)*Complex.I) 0:=hx.mul contDiffAt_const
    have hf':ContDiffAt ℝ 2 f ((0:ℂ)*Complex.I):=by simpa using hf
    have hh:=hf'.comp (f:=fun t:ℝ=>(t:ℂ)*Complex.I) 0 hy
    simpa only [coord,Complex.ofReal_zero,zero_add,Function.comp_def] using hh

end HarmonicAxis318
#print axioms HarmonicAxis318.harmonic_laplacian
