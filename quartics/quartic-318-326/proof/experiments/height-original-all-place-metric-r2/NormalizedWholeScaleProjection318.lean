module
public import NormalizedWholeScaleScheme318
public section
noncomputable section
namespace NormalizedWholeScaleProjection318
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open NormalizedWholeOverlap318 NormalizedWholeGluing318 NormalizedWholeProjection318
open NormalizedWholeScaleEquiv318 NormalizedWholeScaleScheme318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual algebra equivalence retains its complete scalar map. -/
theorem scalar_square {S A B : Type*} [CommRing S] [CommRing A] [CommRing B]
    [Algebra S A] [Algebra S B] (e : A ≃ₐ[S] B) :
    Spec.map e.toRingEquiv.toCommRingCatIso.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap S A))=
      Spec.map (CommRingCat.ofHom (algebraMap S B)) := by
  rw [←Spec.map_comp]
  exact congrArg (fun f : CommRingCat.of S ⟶ CommRingCat.of B => Spec.map f)
    (CommRingCat.hom_ext (RingHom.ext (fun r => e.commutes r)))

variable (R : Type*) [CommRing R] (c d a : Fin 4 → R)
  (s : Fin 4 → Rˣ) (h : ∀ i,c i=d i*(s i:R)^2)

/-- The global square-scaling comparison preserves the original t/w
projective projection, not just the underlying whole scheme. -/
theorem over_projective_line :
    forward R c d a s h ≫ projection R c a=projection R d a := by
  apply pushout.hom_ext
  · change finiteChart R d a ≫ (forward R c d a s h ≫ projection R c a)=
      finiteChart R d a ≫ projection R d a
    rw [←Category.assoc,finite_forward,Category.assoc,finite_restriction,finite_restriction]
    unfold finiteProjection
    rw [←Category.assoc]
    exact congrArg (fun f => f ≫ JLineAtlas318.chart R 1)
      (scalar_square (finiteEquiv R c d a s h))
  · change infinityChart R d a ≫ (forward R c d a s h ≫ projection R c a)=
      infinityChart R d a ≫ projection R d a
    rw [←Category.assoc,infinity_forward,Category.assoc,reciprocal_restriction,reciprocal_restriction]
    unfold reciprocalProjection
    rw [←Category.assoc]
    exact congrArg (fun f => f ≫ JLineAtlas318.chart R 0)
      (scalar_square (infinityEquiv R c d a s h))

theorem over_base : forward R c d a s h ≫ structureMap R c a=structureMap R d a := by
  rw [structureMap,←Category.assoc,over_projective_line]
end NormalizedWholeScaleProjection318
