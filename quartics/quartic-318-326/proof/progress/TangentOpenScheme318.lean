module
public import TangentOpenAlgebra318
public import Mathlib.AlgebraicGeometry.OpenImmersion
public section
noncomputable section
namespace TangentOpenScheme318
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ShortAffineJacobian318
open TangentOpenAlgebra318
open RelativeChordAlgebra318 (PairRing)
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type u} [CommRing R]

/-- Genuine affine self-fiber-product over the original base. -/
@[expose] def productScheme (A B:R) : Scheme :=
  pullback (ShortAffineScheme318.structureMap A B) (ShortAffineScheme318.structureMap A B)

/-- The actual nonvertical tangent/secant open, defined by localization at y1+y2. -/
@[expose] def tangentOpen (A B:R) : Scheme := Spec (CommRingCat.of (TangentRing A B))

@[expose] def intoProduct (A B:R) : tangentOpen A B ⟶ productScheme A B :=
  Spec.map (CommRingCat.ofHom (algebraMap (PairRing A B) (TangentRing A B))) ≫
    (pullbackSpecIso R (Ring A B) (Ring A B)).inv

instance intoProduct_open (A B:R) : IsOpenImmersion (intoProduct A B) := by
  letI:=IsOpenImmersion.of_isLocalization (S:=TangentRing A B) (ordinateSum A B)
  dsimp only [intoProduct,tangentOpen,productScheme,ShortAffineScheme318.scheme,ShortAffineScheme318.structureMap]
  infer_instance

/-- The genuine relative nonvertical tangent/secant addition morphism, constructed from the actual
localized quotient algebra, without a pointwise-to-scheme extension assumption. -/
@[expose] def addition (A B:R) : tangentOpen A B ⟶ ShortAffineScheme318.scheme A B :=
  Spec.map (CommRingCat.ofHom (tangentMap A B).toRingHom)

@[expose] def structureMap (A B:R) : tangentOpen A B ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (TangentRing A B)))

/-- Addition is a morphism over the original base. -/
theorem addition_over_base (A B:R) :
    addition A B ≫ ShortAffineScheme318.structureMap A B = structureMap A B := by
  dsimp only [addition,ShortAffineScheme318.structureMap,structureMap,tangentOpen,ShortAffineScheme318.scheme]
  rw [←Spec.map_comp]
  congr 1
  ext r
  exact (tangentMap A B).commutes r

/-- The genuine first projection reads the first tensor factor. -/
theorem intoProduct_fst (A B:R) : intoProduct A B ≫ pullback.fst _ _ =
    Spec.map (CommRingCat.ofHom (left A B).toRingHom) := by
  dsimp only [intoProduct,tangentOpen,productScheme,ShortAffineScheme318.scheme,ShortAffineScheme318.structureMap]
  rw [Category.assoc,pullbackSpecIso_inv_fst,←Spec.map_comp]
  rfl

/-- The genuine second projection reads the second tensor factor. -/
theorem intoProduct_snd (A B:R) : intoProduct A B ≫ pullback.snd _ _ =
    Spec.map (CommRingCat.ofHom (right A B).toRingHom) := by
  dsimp only [intoProduct,tangentOpen,productScheme,ShortAffineScheme318.scheme,ShortAffineScheme318.structureMap]
  rw [Category.assoc,pullbackSpecIso_inv_snd,←Spec.map_comp]
  rfl

/-- Evaluation of the actual Scheme morphism is composition with its actual coordinate map. -/
theorem addition_evaluation (A B:R) {K:Type u} [CommRing K] [Algebra R K]
    (φ:TangentRing A B →ₐ[R] K) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ addition A B =
      Spec.map (CommRingCat.ofHom (φ.comp (tangentMap A B)).toRingHom) := by
  dsimp only [addition,tangentOpen,ShortAffineScheme318.scheme]
  rw [←Spec.map_comp]
  rfl

/-- The nonvertical tangent/secant construction specializes unconditionally over the literal OpenJ base. -/
@[expose] def literalAddition (N:ℕ) :=
  addition (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)

end TangentOpenScheme318
