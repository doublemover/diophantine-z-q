module
public import HolomorphicRectanglePrimitive318
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.UniformSpace.UniformEmbedding
public section
noncomputable section
namespace BoundedRectanglePrimitiveClosure318
open Set Topology
open HolomorphicRectanglePrimitive318
set_option maxHeartbeats 2400000

/-- Uniformly continuous functions have genuine continuous extensions to
the closure of their ORIGINAL domain. Completeness is used only for the
complex target, not to invent boundary values. -/
theorem uniform_extension_closure (U : Set ℂ) (g : U → ℂ) (hg : UniformContinuous g) :
    ∃G : closure U → ℂ,UniformContinuous G ∧
      ∀z : U,G ⟨z.val,subset_closure z.property⟩=g z := by
  let j : U → closure U := Set.inclusion subset_closure
  have hj : IsUniformInducing j := (isUniformEmbedding_set_inclusion subset_closure).isUniformInducing
  have hD : DenseRange j := by
    have hh := (Topology.IsDenseEmbedding.id (α := ℂ)).subtype (fun z => z∈U)
    simpa only [Topology.IsDenseEmbedding.subtypeEmb,Set.image_id,Set.inclusion,id_eq] using hh.dense
  let G := (hj.isDenseInducing hD).extend g
  refine ⟨G,uniformContinuous_uniformly_extend hj hD hg,?_⟩
  intro z
  exact uniformly_extend_of_ind hj hD hg z

theorem rectangle_convex (a b c d : ℝ) : Convex ℝ (openRectangle a b c d) :=
  (convex_Ioo.preimage Complex.reLm).inter (convex_Ioo.preimage Complex.imLm)

/-- A bounded holomorphic function on a half-rectangle has an explicitly
constructed primitive whose derivative is that SAME function, and whose
values extend continuously to the whole closure. This is a precursor to
analytic seam extension without pre-assumed complex boundary values. -/
theorem bounded_holomorphic_primitive_closure (f : ℂ → ℂ) {a b c d : ℝ}
    (hf : DifferentiableOn ℂ f (openRectangle a b c d))
    (hne : (openRectangle a b c d).Nonempty) (C : ℝ≥0)
    (hC : ∀z∈openRectangle a b c d,‖f z‖₊≤C) :
    ∃g : ℂ → ℂ,∃G : closure (openRectangle a b c d) → ℂ,
      (∀z∈openRectangle a b c d,HasDerivAt g (f z) z) ∧
      LipschitzOnWith C g (openRectangle a b c d) ∧ UniformContinuous G ∧
      (∀z : openRectangle a b c d,G ⟨z.val,subset_closure z.property⟩=g z) := by
  obtain ⟨p,hp⟩ := hne
  let g : ℂ → ℂ := fun w => Complex.wedgeIntegral p w f
  have hg : ∀z∈openRectangle a b c d,HasDerivAt g (f z) z :=
    primitive_derivative f hf p hp
  have hLip : LipschitzOnWith C g (openRectangle a b c d) :=
    (rectangle_convex a b c d).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun z hz => (hg z hz).hasDerivWithinAt) hC
  obtain ⟨G,hGu,hGe⟩ := uniform_extension_closure (openRectangle a b c d)
    (fun z => g z) hLip.to_restrict.uniformContinuous
  exact ⟨g,G,hg,hLip,hGu,hGe⟩
end BoundedRectanglePrimitiveClosure318
