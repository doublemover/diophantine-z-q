module
public import OriginalCotangentOverlapRefinement318
public import IntegralGenericCotangentSquare318
public import LinearEquivComparisonDiamond318
public section
noncomputable section
namespace OriginalCotangentPathCoherence318
open NumberField AlgebraicGeometry CategoryTheory
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318 OriginalAllPlaceNormalModel318
open OriginalCotangentOverlapRefinement318
open scoped TensorProduct
set_option maxHeartbeats 1400000
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t))
  (D : OriginalAllPlaceNormalizedData318.Data c t w) (M : Realization c t w D)
  (ht : w (t : K c t) ≤ 1)

/-- The two INDEPENDENTLY constructed source paths agree as complete
linear equivalences. All overlap squares below are produced from the
actual scheme refinement, not supplied as additional compatibility data. -/
theorem comparison :
    OriginalNormalOrderIntegralComparison318.genericComparison c t w D M ht ≪≫ₗ
      OriginalNormalOrderCotangentCoordinate318.genericComparison c t w D M ht =
    OriginalNormalCenterCommonChart318.genericComparison c t w D M := by
  let R := V c t w
  let L := K c t
  let AA := A c t w D M
  let CC := C c t w D M ht
  let BB := B c t w D
  let EE := E c t w D M ht
  let FF := F c t w D M
  let GG := G c t w D M ht
  let a := oldChart c t w D M
  let z := orderChart c t w D M ht
  let e := integralCommon c t w D M ht
  let f := sourceCommon c t w D M
  let q := refinement c t w D M ht
  letI : Algebra R AA := a.scalar.hom.toAlgebra
  letI : Algebra R CC := z.scalar.hom.toAlgebra
  letI : Algebra AA R := a.evaluation.hom.toAlgebra
  letI : Algebra CC R := z.evaluation.hom.toAlgebra
  letI : Algebra EE R := e.evaluation.hom.toAlgebra
  letI : Algebra AA EE := e.left.hom.toAlgebra
  letI : Algebra CC EE := e.right.hom.toAlgebra
  letI : Algebra AA FF := f.left.hom.toAlgebra
  letI : Algebra BB FF := f.right.hom.toAlgebra
  letI : Algebra CC BB := (orderToSource c t w D M ht).hom.toAlgebra
  letI : Algebra EE GG := q.left.hom.toAlgebra
  letI : Algebra FF GG := q.right.hom.toAlgebra
  letI : Algebra R EE := (e.left.hom.comp a.scalar.hom).toAlgebra
  letI : Algebra R FF := (f.left.hom.comp a.scalar.hom).toAlgebra
  letI : Algebra R GG := (q.left.hom.comp (e.left.hom.comp a.scalar.hom)).toAlgebra
  letI : Algebra AA L := ((algebraMap R L).comp a.evaluation.hom).toAlgebra
  letI : Algebra CC L := ((algebraMap R L).comp z.evaluation.hom).toAlgebra
  letI : Algebra BB L := M.fieldPoint.toAlgebra
  letI : Algebra EE L := ((algebraMap R L).comp e.evaluation.hom).toAlgebra
  letI : Algebra FF L := f.evaluation.hom.toAlgebra
  letI : Algebra GG L := q.evaluation.hom.toAlgebra
  letI : IsScalarTower R AA EE := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsScalarTower R CC EE := IsScalarTower.of_algebraMap_eq (fun r =>
    congrArg (fun h => h.hom r) (LocalSectionCommonChart318.scalar_square a z e))
  letI : IsScalarTower R AA FF := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsScalarTower R BB FF := IsScalarTower.of_algebraMap_eq (fun r =>
    congrArg (fun h => h.hom r) (OriginalNormalCenterCommonChart318.scalar_square c t w D M))
  letI : IsScalarTower R CC BB := IsScalarTower.of_algebraMap_eq (fun r => by
    change algebraMap R BB r=algebraMap (Polynomial R) BB (Polynomial.C r)
    exact (IsScalarTower.algebraMap_apply R (Polynomial R) BB r).symm)
  letI : IsScalarTower R EE GG := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsScalarTower R FF GG := IsScalarTower.of_algebraMap_eq (fun r =>
    congrArg (fun h => h.hom (a.scalar.hom r)) (old_square c t w D M ht))
  letI : IsScalarTower AA EE R := IsScalarTower.of_algebraMap_eq (fun x =>
    (congrArg (fun h => h.hom x) e.left_point).symm)
  letI : IsScalarTower CC EE R := IsScalarTower.of_algebraMap_eq (fun x =>
    (congrArg (fun h => h.hom x) e.right_point).symm)
  letI : IsScalarTower AA R L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsScalarTower CC R L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsScalarTower EE R L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsScalarTower AA EE L := IsScalarTower.of_algebraMap_eq (fun x =>
    congrArg (algebraMap R L) ((congrArg (fun h => h.hom x) e.left_point).symm))
  letI : IsScalarTower CC EE L := IsScalarTower.of_algebraMap_eq (fun x =>
    congrArg (algebraMap R L) ((congrArg (fun h => h.hom x) e.right_point).symm))
  letI : IsScalarTower AA FF L := IsScalarTower.of_algebraMap_eq (fun x =>
    (congrArg (fun h => h.hom x) f.left_point).symm)
  letI : IsScalarTower BB FF L := IsScalarTower.of_algebraMap_eq (fun x =>
    (congrArg (fun h => h.hom x) f.right_point).symm)
  letI : IsScalarTower CC BB L := IsScalarTower.of_algebraMap_eq (fun x =>
    RingHom.congr_fun (OriginalNormalOrderIntegralPoint318.field_square c t w D M ht) x)
  letI : IsScalarTower EE GG L := IsScalarTower.of_algebraMap_eq (fun x =>
    (congrArg (fun h => h.hom x) q.left_point).symm)
  letI : IsScalarTower FF GG L := IsScalarTower.of_algebraMap_eq (fun x =>
    (congrArg (fun h => h.hom x) q.right_point).symm)
  letI : Algebra.Etale AA EE := RingHom.etale_algebraMap.mp e.left_etale
  letI : Algebra.Etale CC EE := RingHom.etale_algebraMap.mp e.right_etale
  letI : Algebra.Etale AA FF := RingHom.etale_algebraMap.mp f.left_etale
  letI : Algebra.Etale BB FF := RingHom.etale_algebraMap.mp f.right_etale
  letI : Algebra.Etale CC BB := RingHom.etale_algebraMap.mp
    (OriginalNormalOrderCotangentCoordinate318.inclusion_etale c t w D M)
  letI : Algebra.Etale EE GG := RingHom.etale_algebraMap.mp q.left_etale
  letI : Algebra.Etale FF GG := RingHom.etale_algebraMap.mp q.right_etale
  let ae := IntegralEtaleCotangent318.transport R AA EE L
  let ce := IntegralEtaleCotangent318.transport R CC EE L
  let af := IntegralEtaleCotangent318.transport R AA FF L
  let bf := IntegralEtaleCotangent318.transport R BB FF L
  let cb := IntegralEtaleCotangent318.transport R CC BB L
  let eg := IntegralEtaleCotangent318.transport R EE GG L
  let fg := IntegralEtaleCotangent318.transport R FF GG L
  have ha : ae ≪≫ₗ eg = af ≪≫ₗ fg := by
    apply EvaluatedCotangentExt318.equiv_ext R AA L
    intro x
    simp only [ae,eg,af,fg,LinearEquiv.trans_apply,
      IntegralEtaleCotangent318.transport_differential]
    have hx := congrArg (fun h => h.hom x) (old_square c t w D M ht)
    change (1:L) ⊗ₜ[GG] KaehlerDifferential.D R GG (q.left.hom (e.left.hom x)) =
      (1:L) ⊗ₜ[GG] KaehlerDifferential.D R GG (q.right.hom (f.left.hom x))
    rw [hx]
  have hc : ce ≪≫ₗ eg = cb ≪≫ₗ bf ≪≫ₗ fg := by
    apply EvaluatedCotangentExt318.equiv_ext R CC L
    intro x
    simp only [ce,eg,cb,bf,fg,LinearEquiv.trans_apply,
      IntegralEtaleCotangent318.transport_differential]
    have hx := congrArg (fun h => h.hom x) (order_square c t w D M ht)
    change (1:L) ⊗ₜ[GG] KaehlerDifferential.D R GG (q.left.hom (e.right.hom x)) =
      (1:L) ⊗ₜ[GG] KaehlerDifferential.D R GG
        (q.right.hom (f.right.hom ((orderToSource c t w D M ht).hom x)))
    rw [hx]
  have hd := LinearEquivComparisonDiamond318.comparison ae ce af bf cb eg fg ha hc
  have hi := IntegralGenericCotangentSquare318.comparison_square R AA EE L CC
  apply LinearEquiv.ext
  intro x
  have hix := congrArg (fun h => h x) hi
  have hdx := congrArg (fun h => h
    (TensorProduct.AlgebraTensorModule.cancelBaseChange AA R L L
      (KaehlerDifferential R AA) x)) hd
  simp only [LinearEquiv.trans_apply,IntegralEtaleCotangent318.comparison] at hix hdx
  change cb (TensorProduct.AlgebraTensorModule.cancelBaseChange CC R L L
      (KaehlerDifferential R CC)
      (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl L L)
        (IntegralEtaleCotangent318.comparison R AA EE R CC) x)) =
    bf.symm (af (TensorProduct.AlgebraTensorModule.cancelBaseChange AA R L L
      (KaehlerDifferential R AA) x))
  rw [hix]
  exact hdx
end OriginalCotangentPathCoherence318
