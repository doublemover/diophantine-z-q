module
public import BothFiniteMaps318
public section
noncomputable section
namespace BothFiniteInfinity318
open BothInfinityAlgebra318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 700000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The regular both-infinity output agrees with each finite-input infinity-output
chart over every common coefficient algebra, including tangent and inverse pairs. -/
theorem coordinates (A B:R) (tangent : Bool) (φ : OutputRing A B →ₐ[R] S)
    (ψ : InfinityAdditionAlgebra318.OutputRing A B tangent →ₐ[R] S)
    (hu : φ (u1 A B)*ψ (InfinityAdditionAlgebra318.pairMap A B tangent (InfinityAdditionAlgebra318.Y1 A B))=
      ψ (InfinityAdditionAlgebra318.pairMap A B tangent (InfinityAdditionAlgebra318.X1 A B)))
    (hv : φ (v1 A B)*ψ (InfinityAdditionAlgebra318.pairMap A B tangent (InfinityAdditionAlgebra318.Y1 A B))=1)
    (ht : φ (u2 A B)*ψ (InfinityAdditionAlgebra318.pairMap A B tangent (InfinityAdditionAlgebra318.Y2 A B))=
      ψ (InfinityAdditionAlgebra318.pairMap A B tangent (InfinityAdditionAlgebra318.X2 A B)))
    (hw : φ (v2 A B)*ψ (InfinityAdditionAlgebra318.pairMap A B tangent (InfinityAdditionAlgebra318.Y2 A B))=1) :
    φ (outU A B)=ψ (InfinityAdditionAlgebra318.outX A B tangent) ∧
      φ (outV A B)=ψ (InfinityAdditionAlgebra318.outZ A B tangent) := by
  let f := ψ.comp (InfinityAdditionAlgebra318.pairMap A B tangent)
  obtain ⟨hU,hV⟩ := BothFiniteMaps318.homogeneous_coordinates A B φ f tangent hu hv ht hw
  have hinv : f (InfinityAdditionAlgebra318.numeratorY A B tangent)*
      ψ (↑(InfinityAdditionAlgebra318.numeratorYUnit A B tangent)⁻¹)=1 := by
    have hh := congrArg ψ (Units.mul_inv (InfinityAdditionAlgebra318.numeratorYUnit A B tangent))
    simpa only [map_mul,map_one,InfinityAdditionAlgebra318.numeratorYUnit,IsUnit.unit_spec,
      f,AlgHom.comp_apply] using hh
  constructor
  · calc
      _=(φ (outU A B)*f (InfinityAdditionAlgebra318.numeratorY A B tangent))*
          ψ (↑(InfinityAdditionAlgebra318.numeratorYUnit A B tangent)⁻¹) := by
        rw [mul_assoc,hinv,mul_one]
      _=(f (InfinityAdditionAlgebra318.numeratorX A B tangent)*
          f (InfinityAdditionAlgebra318.denominator A B tangent))*
          ψ (↑(InfinityAdditionAlgebra318.numeratorYUnit A B tangent)⁻¹) := by rw [hU]
      _=_ := by simp only [InfinityAdditionAlgebra318.outX,map_mul,f,AlgHom.comp_apply]
  · calc
      _=(φ (outV A B)*f (InfinityAdditionAlgebra318.numeratorY A B tangent))*
          ψ (↑(InfinityAdditionAlgebra318.numeratorYUnit A B tangent)⁻¹) := by
        rw [mul_assoc,hinv,mul_one]
      _=f (InfinityAdditionAlgebra318.denominator A B tangent)^3*
          ψ (↑(InfinityAdditionAlgebra318.numeratorYUnit A B tangent)⁻¹) := by rw [hV]
      _=_ := by simp only [InfinityAdditionAlgebra318.outZ,map_mul,map_pow,f,AlgHom.comp_apply]

/-- Equality of the actual Scheme morphisms, not just field-point formulas. -/
theorem scheme_agreement (A B:R) (tangent : Bool) (φ : OutputRing A B →ₐ[R] S)
    (ψ : InfinityAdditionAlgebra318.OutputRing A B tangent →ₐ[R] S)
    (hu : φ (u1 A B)*ψ (InfinityAdditionAlgebra318.pairMap A B tangent (InfinityAdditionAlgebra318.Y1 A B))=
      ψ (InfinityAdditionAlgebra318.pairMap A B tangent (InfinityAdditionAlgebra318.X1 A B)))
    (hv : φ (v1 A B)*ψ (InfinityAdditionAlgebra318.pairMap A B tangent (InfinityAdditionAlgebra318.Y1 A B))=1)
    (ht : φ (u2 A B)*ψ (InfinityAdditionAlgebra318.pairMap A B tangent (InfinityAdditionAlgebra318.Y2 A B))=
      ψ (InfinityAdditionAlgebra318.pairMap A B tangent (InfinityAdditionAlgebra318.X2 A B)))
    (hw : φ (v2 A B)*ψ (InfinityAdditionAlgebra318.pairMap A B tangent (InfinityAdditionAlgebra318.Y2 A B))=1) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ BothInfinityScheme318.addition A B=
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ InfinityAdditionScheme318.addition A B tangent := by
  have hh := coordinates A B tangent φ ψ hu hv ht hw
  have he : φ.comp (outputMap A B)=ψ.comp (InfinityAdditionAlgebra318.outputMap A B tangent) := by
    apply InfinityChart318.hom_ext
    · simpa only [AlgHom.comp_apply,outputMap,InfinityChart318.lift_x,
        InfinityAdditionAlgebra318.outputMap_x] using hh.1
    · simpa only [AlgHom.comp_apply,outputMap,InfinityChart318.lift_z,
        InfinityAdditionAlgebra318.outputMap_z] using hh.2
  dsimp only [BothInfinityScheme318.addition,BothInfinityScheme318.chartAddition,
    InfinityAdditionScheme318.addition,InfinityAdditionScheme318.chartAddition]
  rw [←Category.assoc,←Category.assoc,←Spec.map_comp,←Spec.map_comp]
  congr 2
  exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom he)

end BothFiniteInfinity318
