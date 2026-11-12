module
public import TwoOpenNamedCoefficientComparison318
public section
noncomputable section
namespace ContactPicardCechSectionEqualizer318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
local notation "Q" => Spec (CommRingCat.of ℚ)
variable (c : Fin 4 → ℚˣ) (B : Over Q)
local notation "P" => (ContactDifferenceSheafEpimorphism318.target c).obj
variable (x y : P.obj (op B))
open ContactPicardActualFppfWitnessCover318
variable (i k : index c B x y)
local notation "d" => datum c B x y i
local notation "q" => (ContactPicardLocalWitnessSchemes318.projection c B x y d).left
local notation "U" => MonicFiniteAffineRefinements318.cover q
variable (a : d.T.left.affineCover.I₀) (j : (U.X a).affineCover.I₀)
local notation "f" => MonicFiniteAffineRefinements318.projection q a j
local notation "T" => ContactPicardCechFiniteEnvelopePullback318.base c B x y i k a
variable (b : T.affineCover.I₀)
local notation "g" => ContactPicardCechAffineFlatBase318.affineArrow c B x y i k a b
local notation "R" => Γ(d.T.left.affineCover.X a,⊤)
local notation "S" => Γ((U.X a).affineCover.X j,⊤)
local notation "A" => Γ(T.affineCover.X b,⊤)
variable (p r : PrimeSpectrum S)
variable (D : letI : Algebra R S := f.appTop.hom.toAlgebra; FiniteSubalgebraEnvelopeData318.Data R S p)
variable (E : letI : Algebra R S := f.appTop.hom.toAlgebra; FiniteSubalgebraEnvelopeData318.Data R S r)
/-- The original fppf Cech coefficient map supplies flatness for the
ACTUAL whole source-union section ring, not the chosen finite envelope.
The result is its complete tensor-chart equalizer with exact coefficients. -/
def comparison := by
  letI : Algebra R S := f.appTop.hom.toAlgebra
  letI : Algebra R A := g.appTop.hom.toAlgebra
  letI : Module.Flat R A := ContactPicardCechAffineFlatBase318.coefficient_flat c B x y i k a b
  let u := FiniteSubalgebraEnvelopeSchemes318.sourceInto R S p D
  let v := FiniteSubalgebraEnvelopeSchemes318.sourceInto R S r E
  let base : R →+* Γ(TwoOpenSourceUnion318.scheme u v,⊤) :=
    (WholeAffineTargetFunctions318.ringMap (CommRingCat.of R)
      ((TwoOpenSourceUnion318.opens u v).ι≫Spec.map (CommRingCat.ofHom (algebraMap R S)))).hom
  exact TwoOpenNamedCoefficientComparison318.comparison u v
    (FiniteEnvelopeFullIntersection318.left D E) (FiniteEnvelopeFullIntersection318.right D E)
    (FiniteEnvelopeCommonSourceCartesian318.original_cartesian D E) base A
end ContactPicardCechSectionEqualizer318
