module
public import OriginalUniformSparseReciprocalChart318
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Localization.Away.Basic

/-! The actual rank-two double cover on both polynomial affine charts.
All formulas are over a general commutative ring and retain nilpotents. -/
public section
noncomputable section
namespace OriginalSparseQuadraticCharts318

open Polynomial
open OriginalUniformSparseSmoothChart318 (eqVal)
open OriginalUniformSparseReciprocalChart318 (reverse_laurent overlap overlap_inverse)
local notation "sparseReverse" => OriginalUniformSparseReciprocalChart318.reverse

variable {R : Type*} [CommRing R]

@[expose] def quadratic (f : R[X]) : (R[X])[X] := X^2-C f
abbrev Chart (f : R[X]) := AdjoinRoot (quadratic f)
@[expose] def x (f : R[X]) : Chart f := AdjoinRoot.of (quadratic f) X
@[expose] def y (f : R[X]) : Chart f := AdjoinRoot.root (quadratic f)

theorem monic (f : R[X]) : (quadratic f).Monic :=
  monic_X_pow_sub_C f (by decide)
theorem degree (f : R[X]) [Nontrivial R] : (quadratic f).natDegree=2 :=
  natDegree_X_pow_sub_C

/-- Finiteness of the ACTUAL affine cover follows from its monic quadratic. -/
theorem finite (f : R[X]) : Module.Finite R[X] (Chart f) :=
  (monic f).finite_adjoinRoot

/-- The actual local rank-two power basis, not an assumed extension degree. -/
def powerBasis (f : R[X]) : PowerBasis R[X] (Chart f) :=
  AdjoinRoot.powerBasis' (monic f)

theorem relation (f : R[X]) : y f ^ 2 = AdjoinRoot.of (quadratic f) f := by
  have q := AdjoinRoot.eval₂_root (quadratic f)
  change (X^2-C f).eval₂ (AdjoinRoot.of (quadratic f)) (y f) = 0 at q
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at q
  exact sub_eq_zero.mp q

/-- The polynomial-coordinate hom is the literal structure map of the
rank-two algebra, not a shifted or Möbius-transformed coordinate. -/
theorem coordinate (f : R[X]) :
    (aeval (x f)).toRingHom = AdjoinRoot.of (quadratic f) := by
  apply Polynomial.ringHom_ext
  · intro a
    exact aeval_C _ _
  · exact aeval_X _

theorem relation_aeval (f : R[X]) : y f^2=aeval (x f) f := by
  exact (relation f).trans (RingHom.congr_fun (coordinate f).symm f)

/-- The two-element basis of each actual polynomial-chart preimage. -/
def basisTwo (f : R[X]) [Nontrivial R] : Module.Basis (Fin 2) R[X] (Chart f) :=
  (powerBasis f).basis.reindex (finCongr (degree f))

theorem coordinate_finite (f : R[X]) : (aeval (R:=R) (x f)).toRingHom.Finite := by
  rw [coordinate, ← AdjoinRoot.algebraMap_eq, RingHom.finite_algebraMap]
  exact finite f

section Maps
variable {S : Type*} [CommRing S] [Algebra R S]

/-- Map of the whole affine cover from specified coordinates satisfying
the literal double-cover relation. -/
@[expose] def lift (f : R[X]) (p q : S) (hq : q^2=aeval p f) : Chart f →ₐ[R] S :=
  AdjoinRoot.liftAlgHom (quadratic f) (aeval p) q (by
    simp only [quadratic,eval₂_sub,eval₂_pow,eval₂_X,eval₂_C,
      AlgHom.coe_toRingHom]
    exact sub_eq_zero.mpr hq)

@[simp] theorem lift_x (f : R[X]) (p q : S) (hq : q^2=aeval p f) :
    lift f p q hq (x f) = p := by simp [lift,x]
@[simp] theorem lift_y (f : R[X]) (p q : S) (hq : q^2=aeval p f) :
    lift f p q hq (y f) = q := by simp [lift,y]

theorem hom_ext (f : R[X]) {u v : Chart f →ₐ[R] S}
    (hx : u (x f)=v (x f)) (hy : u (y f)=v (y f)) : u=v := by
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    exact hx
  · exact hy

@[expose] def ordinary (s t : R) : R[X] := eqVal (C s) (C t) X
@[expose] def reciprocal (s t : R) : R[X] := sparseReverse (C s) (C t) X

@[simp] theorem aeval_ordinary (s t:R) (p:S) :
    aeval p (ordinary s t) = eqVal (algebraMap R S s) (algebraMap R S t) p := by
  simp [ordinary,eqVal, map_ofNat]
@[simp] theorem aeval_reciprocal (s t:R) (p:S) :
    aeval p (reciprocal s t) = sparseReverse (algebraMap R S s) (algebraMap R S t) p := by
  simp [reciprocal,OriginalUniformSparseReciprocalChart318.reverse,map_ofNat]
end Maps

abbrev Overlap (f : R[X]) := Localization.Away (x f)
@[expose] def xx (f : R[X]) : Overlap f := algebraMap (Chart f) _ (x f)
@[expose] def yy (f : R[X]) : Overlap f := algebraMap (Chart f) _ (y f)
@[expose] def xi (f : R[X]) : Overlap f := IsLocalization.Away.invSelf (x f)
@[simp] theorem xx_xi (f : R[X]) : xx f*xi f=1 := IsLocalization.Away.mul_invSelf _
@[simp] theorem xi_xx (f : R[X]) : xi f*xx f=1 := by rw [mul_comm,xx_xi]

theorem relation_overlap (f : R[X]) : yy f^2=aeval (xx f) f := by
  have h := congrArg (algebraMap (Chart f) (Overlap f)) (relation f)
  rw [map_pow] at h
  have he : (algebraMap (Chart f) (Overlap f)).comp (AdjoinRoot.of (quadratic f)) =
      (aeval (xx f)).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      change algebraMap (Chart f) (Overlap f) (algebraMap R (Chart f) a) =
        aeval (xx f) (C a)
      rw [aeval_C]
      exact (IsScalarTower.algebraMap_apply R (Chart f) (Overlap f) a).symm
    · simp [x,xx]
  exact h.trans (RingHom.congr_fun he f)

variable (s t : R)
abbrev F := ordinary s t
abbrev G := reciprocal s t
abbrev CF := Chart (F s t)
abbrev CG := Chart (G s t)
abbrev LF := Overlap (F s t)
abbrev LG := Overlap (G s t)

theorem forward_relation :
    yy (F s t)^2=eqVal (algebraMap R (LF s t) s) (algebraMap R (LF s t) t) (xx (F s t)) := by
  simpa using relation_overlap (F s t)
theorem reverse_relation :
    yy (G s t)^2=sparseReverse (algebraMap R (LG s t) s) (algebraMap R (LG s t) t) (xx (G s t)) := by
  simpa using relation_overlap (G s t)

/-- Infinity algebra in the finite Laurent chart: z=1/x and w=y/x³. -/
@[expose] def infToFinBase : CG s t →ₐ[R] LF s t :=
  lift (G s t) (xi (F s t)) (yy (F s t)*xi (F s t)^3) (by
    rw [aeval_reciprocal]
    exact overlap _ _ _ _ _ (xx_xi _) (forward_relation s t))

/-- Finite algebra in the infinity Laurent chart, inverse substitution. -/
@[expose] def finToInfBase : CF s t →ₐ[R] LG s t :=
  lift (F s t) (xi (G s t)) (yy (G s t)*xi (G s t)^3) (by
    rw [aeval_ordinary]
    have hr := reverse_laurent (algebraMap R (LG s t) s)
      (algebraMap R (LG s t) t) (xi (G s t)) (xx (G s t)) (xi_xx _)
    calc
      _ = yy (G s t)^2*xi (G s t)^6 := by ring
      _ = (eqVal (algebraMap R (LG s t) s) (algebraMap R (LG s t) t)
        (xi (G s t))*xx (G s t)^6)*xi (G s t)^6 := by
          rw [reverse_relation, hr]
      _ = _ := by
        rw [mul_assoc,←mul_pow,xx_xi,one_pow,mul_one])

@[simp] theorem infToFinBase_x : infToFinBase s t (x (G s t))=xi (F s t) := by
  simp [infToFinBase]
@[simp] theorem infToFinBase_y : infToFinBase s t (y (G s t))=yy (F s t)*xi (F s t)^3 := by
  simp [infToFinBase]
@[simp] theorem finToInfBase_x : finToInfBase s t (x (F s t))=xi (G s t) := by
  simp [finToInfBase]
@[simp] theorem finToInfBase_y : finToInfBase s t (y (F s t))=yy (G s t)*xi (G s t)^3 := by
  simp [finToInfBase]

@[expose] def infToFin : LG s t →ₐ[R] LF s t :=
  IsLocalization.Away.liftAlgHom (f:=infToFinBase s t) (x (G s t)) (by
    rw [infToFinBase_x]
    exact IsUnit.of_mul_eq_one_right _ (xx_xi _))
@[expose] def finToInf : LF s t →ₐ[R] LG s t :=
  IsLocalization.Away.liftAlgHom (f:=finToInfBase s t) (x (F s t)) (by
    rw [finToInfBase_x]
    exact IsUnit.of_mul_eq_one_right _ (xx_xi _))

@[simp] theorem infToFin_map (q : CG s t) :
    infToFin s t (algebraMap (CG s t) (LG s t) q)=infToFinBase s t q := by
  simp [infToFin,IsLocalization.Away.liftAlgHom_apply]
@[simp] theorem finToInf_map (q : CF s t) :
    finToInf s t (algebraMap (CF s t) (LF s t) q)=finToInfBase s t q := by
  simp [finToInf,IsLocalization.Away.liftAlgHom_apply]
@[simp] theorem infToFin_xx : infToFin s t (xx (G s t))=xi (F s t) := by simp [xx]
@[simp] theorem infToFin_yy :
    infToFin s t (yy (G s t))=yy (F s t)*xi (F s t)^3 := by simp [yy]
@[simp] theorem finToInf_xx : finToInf s t (xx (F s t))=xi (G s t) := by simp [xx]
@[simp] theorem finToInf_yy :
    finToInf s t (yy (F s t))=yy (G s t)*xi (G s t)^3 := by simp [yy]

@[simp] theorem infToFin_xi : infToFin s t (xi (G s t))=xx (F s t) := by
  have h := congrArg (infToFin s t) (xx_xi (G s t))
  simp only [map_mul,map_one,infToFin_xx] at h
  calc
    _ = xx (F s t)*(xi (F s t)*infToFin s t (xi (G s t))) := by
      rw [←mul_assoc,xx_xi,one_mul]
    _ = _ := by rw [h,mul_one]

@[simp] theorem finToInf_xi : finToInf s t (xi (F s t))=xx (G s t) := by
  have h := congrArg (finToInf s t) (xx_xi (F s t))
  simp only [map_mul,map_one,finToInf_xx] at h
  calc
    _ = xx (G s t)*(xi (G s t)*finToInf s t (xi (F s t))) := by
      rw [←mul_assoc,xx_xi,one_mul]
    _ = _ := by rw [h,mul_one]

theorem inverse_finite : (infToFin s t).comp (finToInf s t)=AlgHom.id R (LF s t) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (x (F s t)))
  apply hom_ext (F s t)
  · change infToFin s t (finToInf s t (xx (F s t)))=xx (F s t)
    simp
  · change infToFin s t (finToInf s t (yy (F s t)))=yy (F s t)
    simp only [finToInf_yy, map_mul, map_pow, infToFin_yy, infToFin_xi]
    exact overlap_inverse _ _ _ (xx_xi _)

theorem inverse_infinity : (finToInf s t).comp (infToFin s t)=AlgHom.id R (LG s t) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (x (G s t)))
  apply hom_ext (G s t)
  · change finToInf s t (infToFin s t (xx (G s t)))=xx (G s t)
    simp
  · change finToInf s t (infToFin s t (yy (G s t)))=yy (G s t)
    simp only [infToFin_yy, map_mul, map_pow, finToInf_yy, finToInf_xi]
    exact overlap_inverse _ _ _ (xx_xi _)

/-- The actual principal overlap underlying the Scheme gluing. -/
@[expose] def overlapEquiv : LG s t ≃ₐ[R] LF s t :=
  AlgEquiv.ofAlgHom (infToFin s t) (finToInf s t) (inverse_finite s t) (inverse_infinity s t)

end OriginalSparseQuadraticCharts318

#print axioms OriginalSparseQuadraticCharts318.overlapEquiv
