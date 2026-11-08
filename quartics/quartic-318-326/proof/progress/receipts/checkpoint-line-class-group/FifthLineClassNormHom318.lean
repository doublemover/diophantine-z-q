module
public import LineSheafClassGroup318
public import FifthLineClassNormProduct318
public import FifthLineClassNormUnit318
public section
noncomputable section
namespace FifthLineClassNormHom318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open FifthCompletedGlobal318 FifthChartNorm318
/-- The exact previously constructed fifth norm, now bundled as a homomorphism
of actual line-sheaf isomorphism-class groups. No Picard scheme or Jacobian
map, base-change structure or monoidal coherence is inferred. -/
@[expose] def norm : Class Model →* Class Target where
  toFun := FifthLineClassNorm318.norm
  map_one' := FifthLineClassNormUnit318.norm_unit
  map_mul' := FifthLineClassNormProduct318.norm_product
lemma apply_eq (c : Class Model) : norm c = FifthLineClassNorm318.norm c := rfl
lemma on_representatives (L : Line Model) :
    norm (classOf L) = classOf (FifthLineClassNorm318.line L) := rfl
lemma maps_inverse (c : Class Model) : norm (c⁻¹) = (norm c)⁻¹ := map_inv norm c
lemma maps_power (c : Class Model) (n : ℕ) : norm (c ^ n) = norm c ^ n := map_pow norm c n
end FifthLineClassNormHom318
