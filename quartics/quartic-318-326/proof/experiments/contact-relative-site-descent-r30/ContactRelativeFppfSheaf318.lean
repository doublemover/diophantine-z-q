module
public import ContactRelativeFppfFamily318
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public section
noncomputable section
namespace ContactRelativeFppfSheaf318
open AlgebraicGeometry CategoryTheory Opposite
open OriginalRelativeSite318 ContactUniversalRigidifiedClass318
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (t : ℚ)

/-- The unchanged original relative-class presheaf satisfies the actual
big fppf sheaf condition on schemes over the exact Contact field base.
The topology and objects are the existing relative site, not a new site
whose definition incorporates the desired conclusion. -/
theorem isSheaf : Presieve.IsSheaf (Scheme.fppfTopology.over (FieldBase t))
    (presheaf (q t)) := by
  intro Z R hR
  obtain ⟨Y,b,rfl⟩ := Z.mk_surjective
  have hR' : Sieve.overEquiv (object b) R ∈
      Scheme.grothendieckTopology (@Flat ⊓ @LocallyOfFinitePresentation) Y := hR
  obtain ⟨U,hU⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hR'
  have hmem := ContactRelativeFppfFamily318.mem_topology t b R U (fun i =>
    (Sieve.overEquiv_iff (object b) R (U.f i)).mp (hU _ (Presieve.ofArrows.mk i)))
  simpa only [Sieve.pullback_id] using hmem (object b) (𝟙 (object b))
end ContactRelativeFppfSheaf318
