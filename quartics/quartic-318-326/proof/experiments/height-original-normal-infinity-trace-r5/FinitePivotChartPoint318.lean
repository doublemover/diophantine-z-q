module
public import FinitePivotGenericCanonical318
public section
noncomputable section
namespace FinitePivotChartPoint318
open Polynomial FinitePivotCanonicalSource318
variable (V : Type*) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  (rho : V) (u : Vˣ) (d a : Fin 4 → V) (i : Fin 4) (hd : d i=(u:V)*rho)
  (Z : V) (r : Fin 3 → V)
  (hr : ∀ j,(r j)^2=Polynomial.eval Z (OddTwistDilatationCoordinates318.coefficient
    rho u (a i) (others V d i) (others V a i) j)) (hunit : ∀ j,IsUnit (r j))
local notation "C" => FinitePivotCanonicalSource318.Chart V rho u d a i
@[expose] def point : C →+* V := OddTwistDilatationEtale318.point V rho u (a i)
  (others V d i) (others V a i) Z r hr hunit
@[expose] def modelPoint : DVRNormalizedFiniteOrder318.Order V d a →+* V :=
  (point V rho u d a i Z r hr hunit).comp (sourceMap V rho u d a i hd)
lemma point_scalar (v : V) : point V rho u d a i Z r hr hunit (algebraMap V C v)=v :=
  OddTwistDilatationEtale318.point_scalar _ _ _ _ _ _ _ _ _ _ _
lemma point_scalarMap : (point V rho u d a i Z r hr hunit).comp (scalarMap V rho u d a i)=
    Polynomial.evalRingHom (Polynomial.eval Z (OddTwistDilatationCoordinates318.contact rho u (a i))) := by
  apply Polynomial.ringHom_ext
  · intro v
    simp only [RingHom.comp_apply,scalarMap,OddTwistDilatationSourceMap318.originalScalar,
      coe_eval₂RingHom,eval₂_C,point_scalar,Polynomial.evalRingHom_apply,eval_C]
  · simp only [RingHom.comp_apply,scalarMap,OddTwistDilatationSourceMap318.originalScalar,
      coe_eval₂RingHom,eval₂_X,Polynomial.evalRingHom_apply,eval_X]
    exact OddTwistDilatationEtale318.point_contact _ _ _ _ _ _ _ _ _ _
lemma modelPoint_polynomial (p : V[X]) : modelPoint V rho u d a i hd Z r hr hunit
    (algebraMap V[X] (DVRNormalizedFiniteOrder318.Order V d a) p)=Polynomial.eval
      (Polynomial.eval Z (OddTwistDilatationCoordinates318.contact rho u (a i))) p := by
  change point V rho u d a i Z r hr hunit (sourceMap _ _ _ _ _ _ _ _) = _
  rw [sourceMap_polynomial]
  exact RingHom.congr_fun (point_scalarMap V rho u d a i Z r hr hunit) p
lemma modelPoint_pivot : modelPoint V rho u d a i hd Z r hr hunit
    (FourRootOrderSigns318.generator (DVRNormalizedFiniteOrder318.coefficient V d a) i)=rho*Z := by
  change point V rho u d a i Z r hr hunit (sourceMap _ _ _ _ _ _ _ _) = _
  rw [sourceMap_root]
  have hi : originalRoot V rho u d a i i=originalRoot V rho u d a i (FourRootPivot318.indices i 0) :=
    congrArg (originalRoot V rho u d a i) (FourRootPivot318.indices_zero i).symm
  rw [hi,originalRoot_index]
  change OddTwistDilatationEtale318.point _ _ _ _ _ _ _ _ _ _
    (algebraMap V C rho*OddTwistDilatationEtale318.coordinate V rho u (a i)
      (others V d i) (others V a i))=_
  rw [map_mul,OddTwistDilatationEtale318.point_scalar,OddTwistDilatationEtale318.point_coordinate]
lemma modelPoint_other (j : Fin 3) : modelPoint V rho u d a i hd Z r hr hunit
    (FourRootOrderSigns318.generator (DVRNormalizedFiniteOrder318.coefficient V d a)
      (FourRootPivot318.indices i j.succ))=r j := by
  change point V rho u d a i Z r hr hunit (sourceMap _ _ _ _ _ _ _ _) = _
  rw [sourceMap_root,originalRoot_index]
  exact OddTwistDilatationEtale318.point_signed_root _ _ _ _ _ _ _ _ _ _ _
end FinitePivotChartPoint318
