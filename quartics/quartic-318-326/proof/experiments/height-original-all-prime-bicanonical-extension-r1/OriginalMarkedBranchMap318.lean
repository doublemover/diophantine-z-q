module
public import ContactFiniteCoefficientIdentity318
public import IntegralRootPointMaps318
public section
noncomputable section
namespace OriginalMarkedBranchMap318
open Polynomial
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {A : Type*} [CommRing A] [Algebra ℚ A]
  (c : Fin 4 → ℚˣ) (T : A) (r : Fin 4 → A)
  (hr : ∀ i,(r i)^2=algebraMap ℚ A (c i : ℚ)*(T-algebraMap ℚ A (LinearContactSquareclass318.contacts i)))
  (hu : ∀ i,IsUnit (r i))
@[expose] def sourceScalar : ℚ[X] →+* A := Polynomial.eval₂RingHom (algebraMap ℚ A) T
@[expose] def sourceMap : ContactKummerOrder318.SourceOrder c →+* A := by
  letI : Algebra ℚ[X] A := (sourceScalar T).toAlgebra
  exact (IntegralRootPointMaps318.fourMap (ContactKummerOrder318.coefficient c) r (fun i => by
    change (r i)^2=Polynomial.eval₂ (algebraMap ℚ A) T (ContactKummerOrder318.coefficient c i)
    simpa only [ContactKummerOrder318.coefficient,eval₂_mul,eval₂_sub,eval₂_C,eval₂_X] using hr i)).toRingHom

theorem sourceMap_polynomial (p : ℚ[X]) : sourceMap c T r hr
    (algebraMap ℚ[X] (ContactKummerOrder318.SourceOrder c) p)=sourceScalar T p := by
  letI : Algebra ℚ[X] A := (sourceScalar T).toAlgebra
  exact (IntegralRootPointMaps318.fourMap (ContactKummerOrder318.coefficient c) r (fun i => by
    change (r i)^2=Polynomial.eval₂ (algebraMap ℚ A) T (ContactKummerOrder318.coefficient c i)
    simpa only [ContactKummerOrder318.coefficient,eval₂_mul,eval₂_sub,eval₂_C,eval₂_X] using hr i)).commutes p

theorem sourceMap_generator (i : Fin 4) : sourceMap c T r hr
    (FourRootOrderSigns318.generator (ContactKummerOrder318.coefficient c) i)=r i := by
  letI : Algebra ℚ[X] A := (sourceScalar T).toAlgebra
  exact IntegralRootPointMaps318.fourMap_generator _ _ _ i

theorem sourceMap_scalar (q : ℚ) : sourceMap c T r hr
    (algebraMap ℚ (ContactKummerOrder318.SourceOrder c) q)=algebraMap ℚ A q := by
  rw [IsScalarTower.algebraMap_apply ℚ ℚ[X] (ContactKummerOrder318.SourceOrder c)]
  change sourceMap c T r hr (algebraMap ℚ[X] _ (C q))=_
  rw [sourceMap_polynomial]
  exact Polynomial.eval₂_C _ _ _

theorem sourceDenominator_unit (i : Fin 4) : IsUnit
    (sourceMap c T r hr (SourceDenominatorCover318.denominator c i)) := by
  have hs (j : Fin 4) : sourceScalar T (ContactKummerOrder318.coefficient c j)=(r j)^2 := by
    change Polynomial.eval₂ (algebraMap ℚ A) T (ContactKummerOrder318.coefficient c j)=_
    simpa only [ContactKummerOrder318.coefficient,eval₂_mul,eval₂_sub,eval₂_C,eval₂_X] using (hr j).symm
  have he : sourceMap c T r hr (SourceDenominatorCover318.denominator c i)=
      ∏ j : Fin 3,(r (FourRootPivot318.indices i j.succ))^2 := by
    simp only [SourceDenominatorCover318.denominator,SourceDenominatorCover318.twisted,
      map_prod,sourceMap_polynomial,hs]
  rw [he]
  classical
  induction (Finset.univ : Finset (Fin 3)) using Finset.induction_on with
  | empty => simpa using (isUnit_one : IsUnit (1 : A))
  | @insert j s hj h => rw [Finset.prod_insert hj]; exact ((hu _).pow 2).mul h

@[expose] def branchRingMap (i : Fin 4) : ContactBicanonicalCoefficients318.BranchRing c i →+* A :=
  IsLocalization.Away.lift (SourceDenominatorCover318.denominator c i)
    (sourceDenominator_unit c T r hr hu i)
theorem branchRingMap_base (i : Fin 4) (z : ContactKummerOrder318.SourceOrder c) :
    branchRingMap c T r hr hu i (algebraMap (ContactKummerOrder318.SourceOrder c)
      (ContactBicanonicalCoefficients318.BranchRing c i) z)=sourceMap c T r hr z :=
  IsLocalization.Away.lift_eq _ _ _
@[expose] def branchMap (i : Fin 4) : ContactBicanonicalCoefficients318.BranchRing c i →ₐ[ℚ] A where
  __ := branchRingMap c T r hr hu i
  commutes' q := by
    rw [IsScalarTower.algebraMap_apply ℚ (ContactKummerOrder318.SourceOrder c)
      (ContactBicanonicalCoefficients318.BranchRing c i),branchRingMap_base,sourceMap_scalar]

theorem branchMap_T (i : Fin 4) : branchMap c T r hr hu i (ContactBicanonicalCoefficients318.branchT c i)=T := by
  change branchRingMap c T r hr hu i (algebraMap _ _ (algebraMap ℚ[X] _ X))=_
  rw [branchRingMap_base,sourceMap_polynomial]
  exact Polynomial.eval₂_X _ _

theorem branchMap_P (i : Fin 4) : branchMap c T r hr hu i
    (ContactFiniteCoefficientIdentity318.branchP c i)=
      ∏ j : Fin 4,(T-algebraMap ℚ A (LinearContactSquareclass318.contacts j)) := by
  change branchRingMap c T r hr hu i (algebraMap _ _ (SourceOpenFractionField318.d c))=_
  rw [branchRingMap_base,SourceOpenFractionField318.d,sourceMap_polynomial]
  simp only [sourceScalar,ContactKummerOrder318.denominator,coe_eval₂RingHom,
    eval₂_finsetProd,eval₂_sub,eval₂_X,eval₂_C]
end OriginalMarkedBranchMap318
