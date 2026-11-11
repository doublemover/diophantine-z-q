module
public import ShortAffineJacobian318
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public section
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace ShortAffineScheme318
open ShortAffineJacobian318
variable {R : Type*} [CommRing R]

/-- The actual affine scheme cut out by the literal short Weierstrass equation. -/
@[expose] def scheme (A B : R) : Scheme := Spec (CommRingCat.of (Ring A B))

/-- Its actual structure morphism to the base scheme. -/
@[expose] def structureMap (A B : R) : scheme A B ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (Ring A B)))

/-- The affine Weierstrass structure morphism is genuinely smooth. -/
theorem structureMap_smooth (A B : R) (hD : IsUnit (-16*(4*A^3+27*B^2))) :
    Smooth (structureMap A B) := by
  apply HasRingHomProperty.Spec_iff.mpr
  exact RingHom.smooth_algebraMap.mpr (ShortAffineJacobian318.smooth A B hD)

/-- The literal affine plane containing the family. -/
@[expose] def plane : Scheme := Spec (CommRingCat.of (MvPolynomial (Fin 2) R))

/-- The actual closed embedding of the literal hypersurface in the affine plane. -/
@[expose] def embedding (A B : R) : scheme A B ⟶ plane (R := R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range (equations A B)))))

theorem embedding_closed (A B : R) : IsClosedImmersion (embedding A B) := by
  exact IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- The polynomial quotient embedding commutes with the actual base morphisms. -/
theorem embedding_over_base (A B : R) :
    embedding A B ≫ Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin 2) R)))=
      structureMap A B := by
  dsimp only [embedding,structureMap,scheme,plane]
  rw [← Spec.map_comp]
  rfl

end ShortAffineScheme318
