module
public import ActualJSurjective318
public import ThreeArithmeticImage318
public section
noncomputable section
namespace ThreeArithmeticSurjective318
open OpenJModel318 ThreeArithmeticQuotient318
open CategoryTheory AlgebraicGeometry

/-- The actual map from the existing admissible analytic Gamma1(3)
quotient onto complex points of the specified arithmetic full fixed algebra
is surjective. Both the global j-image and each genuine torsion fiber are
proved, with no supplied modular classification or surjectivity premise. -/
theorem complexPoint_surjective (N : ℕ) [NeZero N] : Function.Surjective (complexPoint N) := by
  intro f
  apply (ThreeArithmeticImage318.in_image_iff_realized_j N f).mpr
  obtain ⟨tau,htau⟩ := ActualJSurjective318.surjective
    (f (algebraMap (Base N) (LiteralThreeXComparison318.Fixed N) (jCoord N)))
  exact ⟨tau,htau.symm⟩

/-- The same surjectivity reaches every actual Spec(C)-valued point of the
specified arithmetic affine scheme, by the full faithfulness of Spec. -/
theorem schemePoint_surjective (N : ℕ) [NeZero N] : Function.Surjective (schemePoint N) := by
  intro p
  let f : LiteralThreeXComparison318.Fixed N →+* ℂ := (Scheme.Spec.preimage p).unop.hom
  obtain ⟨q,hq⟩ := complexPoint_surjective N f
  refine ⟨q,?_⟩
  change Scheme.Spec.map (CommRingCat.ofHom (complexPoint N q)).op=p
  rw [hq]
  exact Scheme.Spec.map_preimage p

end ThreeArithmeticSurjective318
