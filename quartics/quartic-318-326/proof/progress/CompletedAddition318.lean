module
public import CompletedAdditionCompatibility318
public section
noncomputable section
namespace CompletedAddition318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open WeierstrassTwoChartCover318 CompletedAdditionCharts318
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type u} [CommRing R]
/-- Actual global addition on the completed relative Weierstrass Scheme,
glued from all four whole input-chart laws. -/
@[expose] def addition (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    pullback (WeierstrassGluing318.structureMap A B) (WeierstrassGluing318.structureMap A B) ⟶
      WeierstrassGluing318.scheme A B :=
  (productCover A B).glueMorphisms (fun ij=>localAddition A B hD ij.1 ij.2)
    (fun ij kl=>CompletedAdditionCompatibility318.local_compatibility A B hD ij.1 ij.2 kl.1 kl.2)
theorem restriction (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) (i j:Fin 2) :
    (productCover A B).f ⟨i,j⟩ ≫ addition A B hD=localAddition A B hD i j :=
  (productCover A B).ι_glueMorphisms _ _ ⟨i,j⟩
theorem addition_over_base (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    addition A B hD ≫ WeierstrassGluing318.structureMap A B=
      pullback.fst _ _ ≫ WeierstrassGluing318.structureMap A B := by
  apply (productCover A B).hom_ext
  rintro ⟨i,j⟩
  rw [←Category.assoc,restriction,localAddition_over_base]
@[expose] def literalAddition (N:ℕ) :=
  addition (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) (OpenJAffineScheme318.discriminant_unit N)
end CompletedAddition318
