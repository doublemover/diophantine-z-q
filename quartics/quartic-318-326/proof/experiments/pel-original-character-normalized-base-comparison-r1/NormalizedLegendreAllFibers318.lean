module
public import NormalizedLegendreWholeProjection318
public import Mathlib.Analysis.Complex.Polynomial.Basic
public section
noncomputable section
namespace NormalizedLegendreAllFibers318
open NormalizedLegendreProjectiveModel318 NormalizedLegendreFieldPoints318
open NormalizedLegendreFiniteProjection318 NormalizedLegendreWholeProjection318
open ProjectiveLineComplexSchemePoints318
open scoped OnePoint

/-- Algebraic root choice is used ONLY to enumerate individual fibers.
No continuity or analytic compatibility of this choice is asserted. -/
@[expose] def root (l t:ℂ) : ℂ:=
  (IsAlgClosed.exists_pow_nat_eq (t*(t-1)*(t-l)) (by decide : 0<2)).choose
lemma root_square (l t:ℂ) : root l t^2=t*(t-1)*(t-l):=
  (IsAlgClosed.exists_pow_nat_eq (t*(t-1)*(t-l)) (by decide : 0<2)).choose_spec
@[expose] def point (l t:ℂ) : FinitePoints l:=⟨(t,root l t),root_square l t⟩

/-- Every complete finite coordinate fiber consists of these actual two
signed points, with coincidence precisely at the finite branch roots. -/
theorem finite_fiber (l t:ℂ) (p:Option (FinitePoints l)) :
    coordinate l p=(t:OnePoint ℂ) ↔
      p=some (point l t) ∨ p=some (sign l (point l t)) := by
  have h:=NormalizedLegendreWholeProjection318.same_coordinate l (some (point l t)) p
  change (t:OnePoint ℂ)=coordinate l p ↔
    some (point l t)=p ∨ some (sign l (point l t))=p at h
  simpa only [eq_comm] using h

lemma infinity_fiber (l:ℂ) (p:Option (FinitePoints l)) : coordinate l p=∞ ↔ p=none := by
  cases p <;> simp [coordinate]

lemma finite_roots_coincide (l t:ℂ) : sign l (point l t)=point l t ↔ t=0 ∨ t=1 ∨ t=l := by
  rw [sign_fixed_iff,zero_iff_branch]
  rfl

/-- Full Scheme-point fiber identity for the SAME actual completed
projection. In particular no target point is excluded by a finite-chart
restriction, and infinity is not confused with a finite branch point. -/
theorem finite_scheme_fiber (l t:ℂ)
    (q:CompletedFieldPoints318.SchemePoints (K:=ℂ) (A l) (B l)) :
    project l q=chartPoint 1 t ↔
      q=schemeEquiv l (some (point l t)) ∨
      q=schemeEquiv l (some (sign l (point l t))) := by
  obtain ⟨p,rfl⟩:=(schemeEquiv l).surjective q
  change project l (schemeEquiv l p)=spherePoint (t:OnePoint ℂ) ↔ _
  rw [whole_projection]
  simp only [spherePoint_bijective.1.eq_iff,(schemeEquiv l).injective.eq_iff]
  exact finite_fiber l t p

theorem infinity_scheme_fiber (l:ℂ)
    (q:CompletedFieldPoints318.SchemePoints (K:=ℂ) (A l) (B l)) :
    project l q=chartPoint 0 0 ↔ q=CompletedFieldPoints318.infinityPoint (A l) (B l) := by
  obtain ⟨p,rfl⟩:=(schemeEquiv l).surjective q
  change project l (schemeEquiv l p)=spherePoint (∞:OnePoint ℂ) ↔
    schemeEquiv l p=schemeEquiv l none
  rw [whole_projection]
  simp only [spherePoint_bijective.1.eq_iff,(schemeEquiv l).injective.eq_iff]
  exact infinity_fiber l p

/-- Surjectivity is proved onto ALL actual base-preserving complex
Scheme-valued points by the original coordinate functors. -/
theorem scheme_projection_surjective (l:ℂ) : Function.Surjective (project l) := by
  intro q
  obtain ⟨z,rfl⟩:=spherePoint_bijective.2 q
  induction z using OnePoint.rec with
  | infty=>exact ⟨schemeEquiv l none,infinity_projection l⟩
  | coe t=>exact ⟨schemeEquiv l (some (point l t)),finite_projection l (point l t)⟩
end NormalizedLegendreAllFibers318
