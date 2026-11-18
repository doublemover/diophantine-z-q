module
public import LargeJActualOrbit318
public import ActualGammaHIndexUpper318
public import GammaHQuotient318
public section
noncomputable section
namespace ActualLargeJMarkedFiber318
open scoped MatrixGroups
open GammaHGroup318 GammaHQuotient318 LargeJActualOrbit318 ActualQJ318
abbrev Fiber (N : ℕ) (H : Subgroup (ZMod N)ˣ) (c : ℂ) := {q : Curve N H // jMap N H q=c}

private theorem project_smul (N : ℕ) (H : Subgroup (ZMod N)ˣ)
    (h : gammaH N H) (z : UpperHalfPlane) :
    projection N H (h.val•z)=projection N H z := by
  apply Quotient.sound
  apply MulAction.orbitRel_apply.mpr
  exact ⟨⟨positiveMatrix N H h,⟨h,rfl⟩⟩,rfl⟩

/-- Every large actual value has finite analytic marked fibre of cardinality
at most the *actual* subgroup index. Use an arbitrary representative for
each left coset and invert it; freeness at elliptic points is not required.
The threshold is uniform over all levels and marking subgroups. -/
theorem finite_fiber : ∃B:ℝ, ∀(N:ℕ) [NeZero N] (H:Subgroup (ZMod N)ˣ) (c:ℂ),
    B<‖c‖ → Finite (Fiber N H c) ∧ Nat.card (Fiber N H c)≤(gammaH N H).index := by
  classical
  obtain ⟨B,hB⟩ := one_orbit_above
  refine ⟨B,?_⟩
  intro N _ H c hc
  let Γ := gammaH N H
  letI : Γ.FiniteIndex := Subgroup.finiteIndex_of_le (gamma1_le_gammaH N H)
  letI : Fintype (SL(2,ℤ) ⧸ Γ) := Subgroup.fintypeQuotientOfFiniteIndex
  by_cases hn : Nonempty (Fiber N H c)
  · obtain ⟨q₀⟩ := hn
    obtain ⟨z,hz⟩ := (projection_openQuotient N H).surjective q₀.val
    have hc₀ : jInvariant z=c := by rw [←jMap_projection N H z,hz,q₀.property]
    let f (q : SL(2,ℤ) ⧸ Γ) : Fiber N H c :=
      ⟨projection N H (q.out⁻¹•z),by rw [jMap_projection,invariant,hc₀]⟩
    have hf : Function.Surjective f := by
      intro y
      obtain ⟨w,hw⟩ := (projection_openQuotient N H).surjective y.val
      have hc₁ : jInvariant w=c := by rw [←jMap_projection N H w,hw,y.property]
      obtain ⟨g,hg⟩ := hB z w (by rwa [hc₀]) (hc₀.trans hc₁.symm)
      let q : SL(2,ℤ) ⧸ Γ := ⟦g⁻¹⟧
      have hq : (⟦q.out⟧ : SL(2,ℤ) ⧸ Γ)=⟦g⁻¹⟧ := q.out_eq
      have hmem : q.out⁻¹*g⁻¹∈Γ := QuotientGroup.leftRel_apply.mp (Quotient.exact hq)
      have hi : g*q.out∈Γ := by simpa only [mul_inv_rev,inv_inv] using Γ.inv_mem hmem
      have hsm : (g*q.out)•(q.out⁻¹•z)=w := by rw [mul_smul,smul_inv_smul,hg]
      refine ⟨q,Subtype.ext ?_⟩
      change projection N H (q.out⁻¹•z)=y.val
      exact ((project_smul N H ⟨g*q.out,hi⟩ (q.out⁻¹•z)).symm.trans (congrArg (projection N H) hsm)).trans hw
    exact ⟨Finite.of_surjective f hf,Nat.card_le_card_of_surjective f hf⟩
  · letI : IsEmpty (Fiber N H c) := ⟨fun x => hn ⟨x⟩⟩
    exact ⟨inferInstance,by simp⟩

/-- Bounds the actual cardinality of each such fibre, without an assumed
cover-degree formula. The number of geometric points in a suitably
unramified algebraic fibre still has to be identified with this analytic
fibre to transfer this result to the chosen rational modular cover. -/
theorem euler_fiber : ∃B:ℝ, ∀(N:ℕ) [NeZero N] (H:Subgroup (ZMod N)ˣ) (c:ℂ),
    B<‖c‖ → (Nat.card (Fiber N H c):ℝ)≤(N:ℝ)*H.index*EulerIndex318.eulerProduct N := by
  obtain ⟨B,hB⟩ := finite_fiber
  refine ⟨B,?_⟩
  intro N _ H c hc
  exact (Nat.cast_le.mpr (hB N H c hc).2).trans (ActualGammaHIndexUpper318.gammaH_index N H)
end ActualLargeJMarkedFiber318
