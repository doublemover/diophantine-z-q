module
public import OriginalSparseQuadraticCharts318
public import JacobianLocalSmooth318
public import Mathlib.Algebra.Polynomial.Derivation

/-! The two-generator plane quotient used by the actual smoothness proof is
canonically the ordinary AdjoinRoot chart used in the proper model. -/
public section
noncomputable section
namespace OriginalSparseQuadraticPlane318

open OriginalSparseQuadraticCharts318
open MvPolynomial Algebra
variable {R : Type*} [CommRing R]
variable (f : Polynomial R)

@[expose] def equation : MvPolynomial (Fin 2) R :=
  X 1^2 - Polynomial.aeval (X 0) f
@[expose] def equations : Unit → MvPolynomial (Fin 2) R := fun _ => equation f
abbrev Plane := MvPolynomial (Fin 2) R ⧸ Ideal.span (Set.range (equations f))
local notation "Ieq" => Ideal.span (Set.range (equations f))
@[expose] def planex : Plane f := Ideal.Quotient.mk Ieq (X 0)
@[expose] def planey : Plane f := Ideal.Quotient.mk Ieq (X 1)

theorem mk_aeval (p : Polynomial R) :
    Ideal.Quotient.mk Ieq (Polynomial.aeval (X 0) p) =
      Polynomial.aeval (planex f) p := by
  have h : (Ideal.Quotient.mkₐ R Ieq).comp (Polynomial.aeval (X 0)) =
      Polynomial.aeval (planex f) := by
    apply Polynomial.algHom_ext
    simp [planex]
  exact AlgHom.congr_fun h p

theorem plane_relation : planey f^2=Polynomial.aeval (planex f) f := by
  have h : Ideal.Quotient.mk Ieq (equation f)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨(),rfl⟩)
  rw [equation,map_sub,map_pow,mk_aeval] at h
  exact sub_eq_zero.mp h

@[expose] def toQuadratic : Plane f →ₐ[R] Chart f :=
  Ideal.Quotient.liftₐ Ieq (MvPolynomial.aeval ![x f,y f]) (by
    intro a ha
    have hle : Ieq ≤ RingHom.ker (MvPolynomial.aeval ![x f,y f] :
        MvPolynomial (Fin 2) R →ₐ[R] Chart f).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨⟨⟩,rfl⟩
      change MvPolynomial.aeval ![x f,y f] (equation f)=0
      have h : (MvPolynomial.aeval ![x f,y f]).comp (Polynomial.aeval (X 0)) =
          Polynomial.aeval (R:=R) (x f) := by
        apply Polynomial.algHom_ext
        simp
      have hy : MvPolynomial.aeval (R:=R) ![x f,y f] (X 1)=y f := by simp
      unfold equation
      rw [map_sub,map_pow,hy]
      change y f^2 - ((MvPolynomial.aeval ![x f,y f]).comp (Polynomial.aeval (X 0))) f=0
      rw [h,relation_aeval,sub_self]
    exact hle ha)

@[expose] def fromQuadratic : Chart f →ₐ[R] Plane f :=
  lift f (planex f) (planey f) (plane_relation f)

@[simp] theorem toQuadratic_x : toQuadratic f (planex f) = x f := by
  change (toQuadratic f).comp (Ideal.Quotient.mkₐ R Ieq) (MvPolynomial.X 0)=_
  unfold toQuadratic
  rw [Ideal.Quotient.liftₐ_comp]
  simp
@[simp] theorem toQuadratic_y : toQuadratic f (planey f) = y f := by
  change (toQuadratic f).comp (Ideal.Quotient.mkₐ R Ieq) (MvPolynomial.X 1)=_
  unfold toQuadratic
  rw [Ideal.Quotient.liftₐ_comp]
  simp
@[simp] theorem fromQuadratic_x : fromQuadratic f (x f) = planex f := by
  simp [fromQuadratic]
@[simp] theorem fromQuadratic_y : fromQuadratic f (y f) = planey f := by
  simp [fromQuadratic]

theorem quadratic_inverse :
    (toQuadratic f).comp (fromQuadratic f)=AlgHom.id R (Chart f) := by
  apply hom_ext f <;> simp

theorem plane_inverse :
    (fromQuadratic f).comp (toQuadratic f)=AlgHom.id R (Plane f) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change fromQuadratic f (toQuadratic f (planex f))=planex f
    simp
  · change fromQuadratic f (toQuadratic f (planey f))=planey f
    simp

@[expose] def equivalence : Plane f ≃ₐ[R] Chart f :=
  AlgEquiv.ofAlgHom (toQuadratic f) (fromQuadratic f)
    (quadratic_inverse f) (plane_inverse f)

@[expose] def presentation (i : Fin 2) :
    PreSubmersivePresentation R (Plane f) (Fin 2) Unit :=
  PreSubmersivePresentation.naive (v := equations f) (fun _ => i)
    (fun _ _ _ => Subsingleton.elim _ _)

theorem jacobian_formula (i : Fin 2) :
    (presentation f i).jacobian = Ideal.Quotient.mk Ieq (pderiv i (equation f)) := by
  rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,Matrix.det_unique,
    PreSubmersivePresentation.jacobiMatrix_apply]
  rfl

theorem jacobian_x :
    (presentation f 0).jacobian = -Polynomial.aeval (planex f) (Polynomial.derivative f) := by
  rw [jacobian_formula,equation,map_sub,Derivation.comp_aeval_eq,
    pderiv_X_self,smul_eq_mul,mul_one,Derivation.leibniz_pow,pderiv_X_of_ne (by decide : (1:Fin 2) ≠ 0)]
  simp [mk_aeval]

theorem jacobian_y : (presentation f 1).jacobian = 2*planey f := by
  rw [jacobian_formula,equation,map_sub,Derivation.comp_aeval_eq,
    pderiv_X_of_ne (by decide : (0:Fin 2) ≠ 1),Derivation.leibniz_pow,pderiv_X_self]
  simp [planey,two_mul]

theorem jacobian_span (h2 : IsUnit (2:R)) (hc : IsCoprime f (Polynomial.derivative f)) :
    Ideal.span (Set.range (fun i : Fin 2 => (presentation f i).jacobian)) = ⊤ := by
  obtain ⟨u,v,huv⟩:=hc
  let ev := Polynomial.aeval (R:=R) (planex f)
  have h := congrArg ev huv
  simp only [map_add,map_mul,map_one] at h
  change ev u*ev f + ev v*ev (Polynomial.derivative f)=1 at h
  rw [show ev f=(planey f)^2 from (plane_relation f).symm] at h
  let I := Ideal.span (Set.range (fun i : Fin 2 => (presentation f i).jacobian))
  apply I.eq_top_of_isUnit_mem (x := 2)
  · have hh : (2:Plane f)=ev u*planey f*(presentation f 1).jacobian -
        2*ev v*(presentation f 0).jacobian := by
      rw [jacobian_x,jacobian_y]
      calc
        _ = 2*(ev u*planey f^2+ev v*ev (Polynomial.derivative f)) := by rw [h,mul_one]
        _ = _ := by dsimp [ev]; ring
    rw [hh]
    exact I.sub_mem (I.mul_mem_left _ (Ideal.subset_span ⟨1,rfl⟩))
      (I.mul_mem_left _ (Ideal.subset_span ⟨0,rfl⟩))
  · simpa only [map_ofNat] using h2.map (algebraMap R (Plane f))

/-- Relative hypersurface smoothness on both ACTUAL rank-two charts. -/
theorem smooth (h2 : IsUnit (2:R)) (hc : IsCoprime f (Polynomial.derivative f)) :
    Algebra.Smooth R (Chart f) := by
  have hplane : Algebra.Smooth R (Plane f) := by
    rw [←RingHom.smooth_algebraMap,RingHom.smooth_iff_locally_isStandardSmooth]
    refine ⟨Set.range (fun i : Fin 2 => (presentation f i).jacobian),jacobian_span f h2 hc,?_⟩
    rintro j ⟨i,rfl⟩
    rw [←IsScalarTower.algebraMap_eq,RingHom.isStandardSmooth_algebraMap]
    exact JacobianLocalSmooth318.localization_jacobian (presentation f i)
  exact Algebra.Smooth.of_equiv (equivalence f)

end OriginalSparseQuadraticPlane318

#print axioms OriginalSparseQuadraticPlane318.smooth
