module
public import PELActualHalfCutGeodesics318
public section
noncomputable section
namespace PELActualEdgeHalfNeighborhood318
open Set Filter
open scoped Topology
open PELMaximalActualComplexDomain318 PELMaximalHalfOctagonShape318
open PELMaximalHalfOctagonCoordinates318
set_option maxHeartbeats 2800000

/-- The SIX actual half-cut inequalities, including both left edges.
They are evaluated in the original complex point's exact Klein coordinates. -/
@[expose] def slack (i:Fin 6) (z:ℂ) : ℝ :=
  ![(coordinates z).2,1-(coordinates z).2,30-(coordinates z).1,
    30+(coordinates z).1,35-(coordinates z).1-7*(coordinates z).2,
    35+(coordinates z).1-7*(coordinates z).2] i

theorem slack_continuous (i:Fin 6) : Continuous (slack i) := by
  have hA := coordinates_continuous.fst
  have hB := coordinates_continuous.snd
  fin_cases i <;> norm_num [slack] <;> fun_prop

theorem original_domain_iff (z:ℂ) : z∈openDomain ↔ 0<z.im ∧ ∀i:Fin 6,0<slack i z := by
  simp only [openDomain,strictPolygon,Set.mem_setOf_eq,centerHomeomorph]
  simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero,
    Complex.add_im,Complex.mul_im,mul_one,zero_add]
  constructor
  · rintro ⟨hz,h₁,h₂,h₃,h₄,h₅,h₆⟩
    refine ⟨hz,?_⟩
    intro i
    fin_cases i <;> norm_num [slack] <;> linarith
  · rintro ⟨hz,h⟩
    have h₀:=h 0;have h₁:=h 1;have h₂:=h 2;have h₃:=h 3;have h₄:=h 4;have h₅:=h 5
    norm_num [slack] at h₀ h₁ h₂ h₃ h₄ h₅
    exact ⟨hz,by linarith,by linarith,by linarith,by linarith,by linarith,by linarith⟩

/-- A genuine nonvertex point of a specified original edge: exactly that
one original constraint is active, all the others are strict. -/
@[expose] def RegularEdge (i:Fin 6) (z:ℂ) : Prop :=
  0<z.im ∧ slack i z=0 ∧ ∀j:Fin 6,j≠i → 0<slack j z

/-- In a real neighborhood of an actual regular edge point, all other
constraints remain strict. Thus the original domain is EXACTLY the one
remaining half-space, not merely a subset of it. -/
theorem original_edge_local_halfspace {i:Fin 6} {z:ℂ} (hz:RegularEdge i z) :
    ∀ᶠw in 𝓝 z,(w∈openDomain ↔ 0<slack i w) := by
  have hi : ∀ᶠw in 𝓝 z,0<w.im :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz.1
  have ho : ∀ᶠw in 𝓝 z,∀j:Fin 6,j≠i → 0<slack j w := by
    apply Filter.eventually_all.mpr
    intro j
    by_cases hji:j=i
    · exact Eventually.of_forall (fun w h=>False.elim (h hji))
    · exact ((slack_continuous j).continuousAt.eventually
        (isOpen_Ioi.mem_nhds (hz.2.2 j hji))).mono (fun w hw _=>hw)
  filter_upwards [hi,ho] with w hw ho
  rw [original_domain_iff]
  constructor
  · exact fun h=>h.2 i
  · intro h
    refine ⟨hw,?_⟩
    intro j
    by_cases hji:j=i
    · simpa only [hji] using h
    · exact ho j hji
end PELActualEdgeHalfNeighborhood318
