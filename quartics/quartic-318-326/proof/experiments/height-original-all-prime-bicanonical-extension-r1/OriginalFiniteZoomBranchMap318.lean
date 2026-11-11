module
public import ContactBicanonicalGenericPullback318
public import IntegralRootPointMaps318
public section
noncomputable section
namespace OriginalFiniteZoomBranchMap318
open Polynomial IntegralContactZoomCoefficients318
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K] [CharZero K]
  (c : Fin 4 → ℚˣ) (d : Fin 4 → K) (t : K) (y s : Fin 4 → K)
  (hs : ∀ i,s i≠0)
  (hc : ∀ i,algebraMap ℚ K (c i : ℚ)=d i*(s i)^2)
abbrev contacts : Fin 4 → K := fun i => algebraMap ℚ K (LinearContactSquareclass318.contacts i)
abbrev Target := Chart d (contacts (K:=K)) t .finite
variable (hy : ∀ i,(y i)^2=IntegralQuadraticPointZoom318.value
  (alpha d (contacts (K:=K)) .finite) d (gamma d (contacts (K:=K)) .finite) t i)
  (hn : ∀ i,y i≠0)
@[expose] def sourceScalar : ℚ[X] →+* Target d t :=
  Polynomial.eval₂RingHom (algebraMap ℚ (Target d t)) (oldCoordinate d (contacts (K:=K)) t .finite)
@[expose] def originalRoot (i : Fin 4) : Target d t :=
  algebraMap K (Target d t) (s i)*
    IntegralZoomNeighborhood318.oldRoot K (alpha d (contacts (K:=K)) .finite)
      d (gamma d (contacts (K:=K)) .finite) t y i

theorem originalRoot_equation (i : Fin 4) : (originalRoot d t y s i)^2=
    sourceScalar d t (ContactKummerOrder318.coefficient c i) := by
  have hr := IntegralContactZoomCoefficients318.original_root_square d (contacts (K:=K)) t .finite y hy i
  have hcoef : algebraMap ℚ (Target d t) (c i : ℚ)=
      algebraMap K (Target d t) (d i)*(algebraMap K (Target d t) (s i))^2 := by
    rw [IsScalarTower.algebraMap_apply ℚ K (Target d t),hc i,map_mul,map_pow]
  rw [originalRoot,mul_pow,hr]
  simp only [sourceScalar,ContactKummerOrder318.coefficient,coe_eval₂RingHom,
    eval₂_mul,eval₂_C,eval₂_sub,eval₂_X,contactFactor,mul_one]
  rw [hcoef]
  change _= _*(oldCoordinate d (contacts (K:=K)) t .finite-
    algebraMap ℚ (Target d t) (LinearContactSquareclass318.contacts i))
  rw [IsScalarTower.algebraMap_apply ℚ K (Target d t)]
  ring

@[expose] def sourceMap : ContactKummerOrder318.SourceOrder c →+* Target d t := by
  letI : Algebra ℚ[X] (Target d t) := (sourceScalar d t).toAlgebra
  exact (IntegralRootPointMaps318.fourMap (ContactKummerOrder318.coefficient c)
    (originalRoot d t y s) (originalRoot_equation c d t y s hc hy)).toRingHom

theorem sourceMap_polynomial (p : ℚ[X]) : sourceMap c d t y s hc hy
    (algebraMap ℚ[X] (ContactKummerOrder318.SourceOrder c) p)=sourceScalar d t p := by
  letI : Algebra ℚ[X] (Target d t) := (sourceScalar d t).toAlgebra
  exact (IntegralRootPointMaps318.fourMap (ContactKummerOrder318.coefficient c)
    (originalRoot d t y s) (originalRoot_equation c d t y s hc hy)).commutes p

theorem sourceMap_generator (i : Fin 4) : sourceMap c d t y s hc hy
    (FourRootOrderSigns318.generator (ContactKummerOrder318.coefficient c) i)=originalRoot d t y s i := by
  letI : Algebra ℚ[X] (Target d t) := (sourceScalar d t).toAlgebra
  exact IntegralRootPointMaps318.fourMap_generator _ _ _ i

theorem sourceMap_scalar (r : ℚ) : sourceMap c d t y s hc hy
    (algebraMap ℚ (ContactKummerOrder318.SourceOrder c) r)=algebraMap ℚ (Target d t) r := by
  rw [IsScalarTower.algebraMap_apply ℚ ℚ[X] (ContactKummerOrder318.SourceOrder c)]
  change sourceMap c d t y s hc hy (algebraMap ℚ[X] _ (C r))=_
  rw [sourceMap_polynomial]
  exact Polynomial.eval₂_C _ _ _

theorem originalRoot_unit (i : Fin 4) : IsUnit (originalRoot d t y s i) :=
  ((IsUnit.mk0 (s i) (hs i)).map (algebraMap K (Target d t))).mul
    (FieldContactZoomTensor318.original_root_unit d (contacts (K:=K)) t .finite y hn i)

theorem sourceDenominator_unit (i : Fin 4) : IsUnit
    (sourceMap c d t y s hc hy (SourceDenominatorCover318.denominator c i)) := by
  have he : sourceMap c d t y s hc hy (SourceDenominatorCover318.denominator c i)=
      ∏ j : Fin 3,(originalRoot d t y s (FourRootPivot318.indices i j.succ))^2 := by
    simp only [SourceDenominatorCover318.denominator,SourceDenominatorCover318.twisted,
      map_prod,sourceMap_polynomial,←originalRoot_equation c d t y s hc hy]
  rw [he]
  classical
  induction (Finset.univ : Finset (Fin 3)) using Finset.induction_on with
  | empty => simpa using (isUnit_one : IsUnit (1 : Target d t))
  | @insert j r hj h => rw [Finset.prod_insert hj]; exact ((originalRoot_unit d t y s hs hn _).pow 2).mul h

@[expose] def branchRingMap (i : Fin 4) : ContactBicanonicalCoefficients318.BranchRing c i →+* Target d t :=
  IsLocalization.Away.lift (SourceDenominatorCover318.denominator c i)
    (sourceDenominator_unit c d t y s hs hc hy hn i)

theorem branchRingMap_base (i : Fin 4) (r : ContactKummerOrder318.SourceOrder c) :
    branchRingMap c d t y s hs hc hy hn i
      (algebraMap (ContactKummerOrder318.SourceOrder c) (ContactBicanonicalCoefficients318.BranchRing c i) r)=
    sourceMap c d t y s hc hy r := IsLocalization.Away.lift_eq _ _ _

@[expose] def branchMap (i : Fin 4) : ContactBicanonicalCoefficients318.BranchRing c i →ₐ[ℚ] Target d t where
  __ := branchRingMap c d t y s hs hc hy hn i
  commutes' r := by
    rw [IsScalarTower.algebraMap_apply ℚ (ContactKummerOrder318.SourceOrder c)
      (ContactBicanonicalCoefficients318.BranchRing c i),branchRingMap_base,sourceMap_scalar]

theorem branchMap_T (i : Fin 4) : branchMap c d t y s hs hc hy hn i
    (ContactBicanonicalCoefficients318.branchT c i)=oldCoordinate d (contacts (K:=K)) t .finite := by
  change branchRingMap c d t y s hs hc hy hn i (algebraMap _ _ (algebraMap ℚ[X] _ X))=_
  rw [branchRingMap_base,sourceMap_polynomial]
  exact Polynomial.eval₂_X _ _

theorem branchMap_P (i : Fin 4) : branchMap c d t y s hs hc hy hn i
    (ContactFiniteCoefficientIdentity318.branchP c i)=contactProduct d (contacts (K:=K)) t .finite := by
  change branchRingMap c d t y s hs hc hy hn i (algebraMap _ _ (SourceOpenFractionField318.d c))=_
  rw [branchRingMap_base,SourceOpenFractionField318.d,sourceMap_polynomial]
  simp only [sourceScalar,ContactKummerOrder318.denominator,coe_eval₂RingHom,
    eval₂_finsetProd,eval₂_sub,eval₂_X,eval₂_C,contactProduct,contactFactor,contacts,
    ←IsScalarTower.algebraMap_apply]

/-- The actual original source map, not a comparison hypothesis, now
identifies both constructed integral coefficients on the generic chart
with the literal original global section formulas. -/
theorem original_q0 (i : Fin 4) : section0 d (contacts (K:=K)) t .finite=
    ContactBicanonicalGenericPullback318.branchImage c i (branchMap c d t y s hs hc hy hn i) :=
  ContactBicanonicalGenericPullback318.finite_original_q0 c i d (contacts (K:=K)) t y hy hn
    (branchMap c d t y s hs hc hy hn i) (branchMap_T c d t y s hs hc hy hn i)
    (branchMap_P c d t y s hs hc hy hn i)
end OriginalFiniteZoomBranchMap318
