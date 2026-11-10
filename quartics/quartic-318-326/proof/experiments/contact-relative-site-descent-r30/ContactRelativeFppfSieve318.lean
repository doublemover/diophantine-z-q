module
public import OriginalRelativePullback318
public section
noncomputable section
namespace ContactRelativeFppfSieve318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open OriginalRelativeSite318 ContactUniversalRigidifiedClass318
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (t : ℚ) {X Y : Scheme} (b : Y ⟶ FieldBase t) (b' : X ⟶ FieldBase t)
  (f : X ⟶ Y) (hf : f ≫ b = b') [Flat f] [Surjective f] [LocallyOfFinitePresentation f]
  (R : Sieve (object b)) (hR : R (arrow b b' f hf))

include hR in
/-- Every sieve containing an actual fppf covering arrow satisfies the
original relative-class sheaf condition; comparison with any sieve arrow
is detected on its genuine scheme-theoretic pullback cover. -/
lemma isSheafFor : Presieve.IsSheafFor (presheaf (q t)) R.arrows := by
  apply (ContactRelativeFppfSingleton318.isSheafFor t b b' f hf).of_singleton hR
  intro Z g hg
  obtain ⟨Z,c,rfl⟩ := Z.mk_surjective
  refine ⟨object (OriginalRelativePullback318.base c f g.left),
    OriginalRelativePullback318.second c f g.left,
    OriginalRelativePullback318.first b b' c f hf g.left g.w,
    OriginalRelativePullback318.square b b' c f hf g.left g.w,?_⟩
  exact (ContactRelativeFppfSingleton318.isSheafFor t c
    (OriginalRelativePullback318.base c f g.left) (pullback.snd f g.left) rfl).isSeparatedFor

include hR in
/-- The actual covering sieve is universal for the original sheaf
condition, hence belongs to the genuine finest sheaf topology. -/
lemma mem_topology : R ∈ ContactRelativeOpenSieve318.topology t (object b) := by
  intro Z g
  obtain ⟨Z,c,rfl⟩ := Z.mk_surjective
  apply isSheafFor t c (OriginalRelativePullback318.base c f g.left)
    (pullback.snd f g.left) rfl (R.pullback g)
  change R (OriginalRelativePullback318.second c f g.left ≫ g)
  rw [OriginalRelativePullback318.square b b' c f hf g.left g.w]
  exact R.downward_closed hR _
end ContactRelativeFppfSieve318
