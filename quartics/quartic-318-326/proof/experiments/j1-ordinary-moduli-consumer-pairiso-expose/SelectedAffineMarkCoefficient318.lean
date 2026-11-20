module
public import WeierstrassCoefficientMap318
public section
noncomputable section
open AlgebraicGeometry CategoryTheory WeierstrassGluing318
open ShortAffineJacobian318 AffineEquationFunctor318

namespace SelectedAffineMarkCoefficient318
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (A B : R) (p : Ring A B →ₐ[R] S)
local notation "a" => algebraMap R S

/-- True coefficient change of the mark into the same affine equation
with mapped coefficients. The actual two evaluations are retained. -/
@[expose] def extendEval : Ring (a A) (a B) →ₐ[S] S :=
  toHom (a A) (a B) ⟨(p (x A B),p (y A B)),by
    have h := congrArg p (relation A B)
    simpa only [map_sub,map_pow,map_mul,map_zero,AlgHom.commutes,
      Algebra.algebraMap_self,RingHom.id_apply] using h⟩

@[simp] theorem extend_x :
    extendEval A B p (x (a A) (a B)) = p (x A B) := toHom_x ..

@[simp] theorem extend_y :
    extendEval A B p (y (a A) (a B)) = p (y A B) := toHom_y ..

theorem extend_factor :
    ((extendEval A B p).restrictScalars R).comp (AffineBaseChange318.coefficientMap A B) = p := by
  apply hom_ext
  · simp only [AlgHom.comp_apply,AlgHom.restrictScalars_apply,AffineBaseChange318.coefficientMap_x,
      extend_x]
  · simp only [AlgHom.comp_apply,AlgHom.restrictScalars_apply,AffineBaseChange318.coefficientMap_y,
      extend_y]

@[expose] def point : Spec (CommRingCat.of S) ⟶ scheme A B :=
  Spec.map (CommRingCat.ofHom p.toRingHom) ≫ finiteChart A B

@[reassoc] theorem point_over :
    point A B p ≫ structureMap A B = Spec.algebraMap R S := by
  rw [point,Category.assoc,finiteChart_structure]
  change Spec.map (CommRingCat.ofHom p.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (Ring A B))) =
    Spec.map (CommRingCat.ofHom a)
  rw [←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a₀
  exact p.commutes a₀

@[reassoc] theorem point_coefficient :
    point (a A) (a B) (extendEval A B p) ≫ WeierstrassCoefficientMap318.coefficientMap A B =
      point A B p := by
  rw [point,Category.assoc,WeierstrassCoefficientMap318.finite_coefficientMap,←Category.assoc,point]
  unfold WeierstrassCoefficientMap318.finiteMap
  rw [←Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f) ≫ finiteChart A B)
    (congrArg AlgHom.toRingHom (extend_factor A B p))

end SelectedAffineMarkCoefficient318

#print axioms SelectedAffineMarkCoefficient318.point_coefficient
