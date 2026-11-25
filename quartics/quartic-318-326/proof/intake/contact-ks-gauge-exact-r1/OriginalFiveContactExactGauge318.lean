module
public import OriginalExactLocalKSUnit318
public import RefinedContactRealization318

public section
noncomputable section
namespace OriginalFiveContactExactGauge318

open NumberField SectionHeight318
open OriginalExactLocalKSUnit318 (localRing finite_norm_from_image)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {E : Type u} [Field E] [NumberField E]

/-- The entire finite lattice identity, expressed in the exact Q
coefficient field. The input a/b are the primitive coefficients
of the actual corresponding two lattices, not abstract norms. -/
structure FiniteImage (H C : FrameNorms E) (k : E) (w : FinitePlace E) where
  hodgePrimitive : E
  canonicalPrimitive : E
  hodge_ne : hodgePrimitive ≠ 0
  canonical_ne : canonicalPrimitive ≠ 0
  hodge_norm : H.finiteNorm w = (w hodgePrimitive)⁻¹
  canonical_norm : C.finiteNorm w = (w canonicalPrimitive)⁻¹
  exact_image :
    Submodule.span (localRing w) ({hodgePrimitive^2*k} : Set E) =
      Submodule.span (localRing w) ({(210:E)*canonicalPrimitive} : Set E)

theorem frame_ext {F G : FrameNorms E}
    (h₁ : ∀ v, F.arch v = G.arch v) (h₂ : ∀ v, F.finiteNorm v = G.finiteNorm v) :
    F = G := by
  obtain ⟨a,f,ha,hf,hs⟩ := F
  obtain ⟨b,g,hb,hg,ht⟩ := G
  have e : a = b := funext h₁
  have e' : f = g := funext h₂
  subst b
  subst g
  rfl

/-- The two mathematically independent checks give the actual
whole-frame equality expected by the existing five-contact consumer.
At infinity the map is Ψ, not Φ=Ψ/210. At finite places exact image
as a submodule, not its length, is used. -/
theorem compatible_ks (H C : FrameNorms E) (k : E) (hk : k ≠ 0)
    (finite : ∀ w : FinitePlace E, FiniteImage H C k w)
    (arch : ∀ w : InfinitePlace E, w k * C.arch w = H.arch w ^ 2) :
    InducedLattice318.induced (C.rescale k hk) (210:E) (by norm_num) =
      InducedLattice318.square H := by
  apply frame_ext
  · exact arch
  · intro w
    let F := finite w
    exact finite_norm_from_image w H C F.hodgePrimitive F.canonicalPrimitive k
      F.hodge_ne F.canonical_ne F.hodge_norm F.canonical_norm F.exact_image

/-- Changing from the true global Q to Q*=Ψ(ℓ²)=kQ does not alter
the norm of either original section. This holds for nonunit k. -/
theorem same_section_norm (v : AbsoluteValue E ℝ) (q k : E) (hk : k ≠ 0) (m : ℝ) :
    v (q/k) * (v k*m) = v q*m := by
  have nz : v k ≠ 0 := v.ne_zero_iff.mpr hk
  rw [map_div₀ v, ← mul_assoc, div_mul_cancel₀ _ nz]

variable (u v : ℤ) (hYuan : ℝ)
variable (a₀ a₁ : E) (C H : FrameNorms E) (k : E) (hk : k ≠ 0)
variable (h₀ : a₀ ≠ 0) (ratio : a₁ = ((32*((u:ℚ)/(v:ℚ)):ℚ):E)*a₀)
variable (degree : H.normalizedDegree = hYuan)
variable (paidFinite : ∀ (w : FinitePlace E) (i : Fin 2), w (![a₀,a₁] i)*C.finiteNorm w ≤ 1)
variable (paidArch : ∀ (w : InfinitePlace E) (i : Fin 2),
  w (![a₀,a₁] i)*C.arch w ≤ ContactMetricSections318.sectionBound)
variable (image : ∀ w : FinitePlace E, FiniteImage H C k w)
variable (arch : ∀ w : InfinitePlace E, w k*C.arch w = H.arch w^2)

private theorem coordinates_div (i : Fin 2) :
    ![a₀/k,a₁/k] i = (![a₀,a₁] i)/k := by
  fin_cases i <;> rfl

/-- The unchanged literal output type. This source constructor does
not produce either upper branch, the actual finite image, or equality
between E and K_ct. It consumes the actual same marked sections
and their paid bounds in Q, not an estimate reconstructed from T. -/
def actual_sections : RefinedContactRealization318.MetricSections E u v hYuan where
  a₀ := a₀/k
  a₁ := a₁/k
  a₀_ne := div_ne_zero h₀ hk
  ratio := by rw [ratio,mul_div_assoc]
  canonical := C.rescale k hk
  hodge := H
  hodge_degree := degree
  ks_image := compatible_ks H C k hk image arch
  arch_bound w i := by
    change w (![a₀/k,a₁/k] i) * (w k*C.arch w) ≤ ContactMetricSections318.sectionBound
    rw [coordinates_div]
    exact (same_section_norm w.val (![a₀,a₁] i) k hk (C.arch w)).trans_le (paidArch w i)
  finite_integral w i := by
    change w (![a₀/k,a₁/k] i) * (w k*C.finiteNorm w) ≤ 1
    rw [coordinates_div]
    exact (same_section_norm w.val (![a₀,a₁] i) k hk (C.finiteNorm w)).trans_le (paidFinite w i)

end OriginalFiveContactExactGauge318

#print axioms OriginalFiveContactExactGauge318.frame_ext
#print axioms OriginalFiveContactExactGauge318.compatible_ks
#print axioms OriginalFiveContactExactGauge318.same_section_norm
#print axioms OriginalFiveContactExactGauge318.actual_sections
