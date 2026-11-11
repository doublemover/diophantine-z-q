module
public import VaryingWholeIdealFamilyCover318
public import AffineIdealEqualityIso318
public import SchemeMonoLocalLift318
public section
noncomputable section
namespace VaryingWholeIdealDescent318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open VaryingWholeIdealFamily318
open scoped TensorProduct
universe u
variable (R A S : Type u) [CommRing R] [CommRing A] [Algebra R A] [CommRing S] [Algebra R S]
variable (I J : Ideal (S ⊗[R] A)) (C : AffineCoefficientCover318.Data R S)
  (h : ∀ i,extended R A S I (C.ring i) (C.coefficient i)=extended R A S J (C.ring i) (C.coefficient i))
local notation "U" => VaryingWholeIdealFamilyCover318.cover R A S I C
@[expose] def localMap (i : C.Index) : U.X i ⟶ family R A S J :=
  (AffineIdealEqualityIso318.iso (C.ring i ⊗[R] A) _ _ (h i)).hom ≫ map R A S J (C.ring i) (C.coefficient i)
lemma local_factor (i : C.Index) : localMap R A S I J C h i ≫ into R A S J=U.f i ≫ into R A S I := by
  rw [localMap,Category.assoc,map_into,← Category.assoc,AffineIdealEqualityIso318.hom_into]
  exact (map_into R A S I (C.ring i) (C.coefficient i)).symm
/-- Full-ideal descent is proved by actual original-source quotient maps,
not by faithful-flatness assumed of one chart or equality of supports. -/
@[expose] def factor : family R A S I ⟶ family R A S J :=
  SchemeMonoLocalLift318.lift U (into R A S J) (into R A S I)
    (localMap R A S I J C h) (local_factor R A S I J C h)
@[reassoc] lemma factor_into : factor R A S I J C h ≫ into R A S J=into R A S I :=
  SchemeMonoLocalLift318.lift_factor U (into R A S J) (into R A S I)
    (localMap R A S I J C h) (local_factor R A S I J C h)
lemma ideal_eq : I=J := by
  apply le_antisymm
  · exact AffineQuotientFactorRigidity318.ideal_le (S ⊗[R] A) J I
      (factor R A S J I C (fun i => (h i).symm)) (factor_into R A S J I C (fun i => (h i).symm))
  · exact AffineQuotientFactorRigidity318.ideal_le (S ⊗[R] A) I J
      (factor R A S I J C h) (factor_into R A S I J C h)
end VaryingWholeIdealDescent318
