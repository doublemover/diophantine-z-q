module
public import WeierstrassCoefficientMap318
public import GluedNegation318
import all WeierstrassGluing318
public section
noncomputable section
namespace CompletedNegationCoefficient318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open WeierstrassGluing318 WeierstrassCoefficientMap318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S:Type u} [CommRing R] [CommRing S] [Algebra R S]
local notation "a" => algebraMap R S
lemma finite_algebra (A B:R) :
    (AffineBaseChange318.coefficientMap (S:=S) A B).comp (ChartNegation318.affineNeg A B)=
      ((ChartNegation318.affineNeg (a A) (a B)).restrictScalars R).comp (AffineBaseChange318.coefficientMap (S:=S) A B) := by
  apply AffineEquationFunctor318.hom_ext <;> simp
lemma infinity_algebra (A B:R) :
    (InfinityBaseChange318.coefficientMap (S:=S) A B).comp (ChartNegation318.infinityNeg A B)=
      ((ChartNegation318.infinityNeg (a A) (a B)).restrictScalars R).comp (InfinityBaseChange318.coefficientMap (S:=S) A B) := by
  apply InfinityChart318.hom_ext <;> simp
lemma finite_square (A B:R) : finiteMap (S:=S) A B ≫ GluedNegation318.finiteNeg A B=
    GluedNegation318.finiteNeg (a A) (a B) ≫ finiteMap A B := by
  unfold finiteMap GluedNegation318.finiteNeg
  rw [←Spec.map_comp,←Spec.map_comp]
  exact congrArg (fun f=>Spec.map (CommRingCat.ofHom f)) (congrArg AlgHom.toRingHom (finite_algebra (S:=S) A B))
lemma infinity_square (A B:R) : infinityMap (S:=S) A B ≫ GluedNegation318.infinityNeg A B=
    GluedNegation318.infinityNeg (a A) (a B) ≫ infinityMap A B := by
  unfold infinityMap GluedNegation318.infinityNeg
  rw [←Spec.map_comp,←Spec.map_comp]
  exact congrArg (fun f=>Spec.map (CommRingCat.ofHom f)) (congrArg AlgHom.toRingHom (infinity_algebra (S:=S) A B))

/-- The actual global negation commutes with arbitrary coefficient change,
without a discriminant, reducedness, or nontriviality hypothesis. -/
theorem negation (A B:R) : coefficientMap (S:=S) A B ≫ GluedNegation318.negation A B=
    GluedNegation318.negation (a A) (a B) ≫ coefficientMap A B := by
  apply pushout.hom_ext
  · change finiteChart (a A) (a B) ≫ (coefficientMap A B ≫ _)=finiteChart (a A) (a B) ≫ (_ ≫ _)
    rw [←Category.assoc,finite_coefficientMap,Category.assoc,GluedNegation318.finiteChart_negation,
      ←Category.assoc,finite_square,Category.assoc,←finite_coefficientMap,
      ←Category.assoc,←GluedNegation318.finiteChart_negation,Category.assoc]
  · change infinityChart (a A) (a B) ≫ (coefficientMap A B ≫ _)=infinityChart (a A) (a B) ≫ (_ ≫ _)
    rw [←Category.assoc,infinity_coefficientMap,Category.assoc,GluedNegation318.infinityChart_negation,
      ←Category.assoc,infinity_square,Category.assoc,←infinity_coefficientMap,
      ←Category.assoc,←GluedNegation318.infinityChart_negation,Category.assoc]
end CompletedNegationCoefficient318
