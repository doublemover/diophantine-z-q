module
public import OriginalSparseQuadraticCharts318
public import OriginalQuadraticDualizing318
public import Mathlib.Algebra.Polynomial.Laurent
public section
noncomputable section
namespace OriginalActualQuadraticLaurent318
open Polynomial
open OriginalSparseQuadraticCharts318
variable {E:Type*} [Field E] (f:E[X])
abbrev L (E:Type*) [Field E] := LaurentPolynomial E
abbrev D := OriginalQuadraticDualizing318.Cover (toLaurent f)
abbrev Y := OriginalQuadraticDualizing318.y (toLaurent f)
abbrev inc : L E →ₐ[E] D f := IsScalarTower.toAlgHom E _ _
abbrev Xl : L E := LaurentPolynomial.T 1
@[expose] def uL : (L E)ˣ := ⟨Xl,LaurentPolynomial.T (-1),by rw [←LaurentPolynomial.T_add]; rfl,
  by rw [←LaurentPolynomial.T_add]; rfl⟩
@[expose] def U : (D f)ˣ := Units.map (inc f).toMonoidHom uL
@[expose] def V : (Overlap f)ˣ := ⟨xx f,xi f,xx_xi f,xi_xx f⟩

theorem aeval_xl (p:E[X]) : aeval (Xl:L E) p=toLaurent p := by
  have h : aeval (Xl:L E)=toLaurentAlg := by apply Polynomial.algHom_ext; rw [aeval_X,toLaurentAlg_apply,toLaurent_X]
  rw [h,toLaurentAlg_apply]

@[expose] def toBase : Chart f →ₐ[E] D f :=
  lift f (↑(U f)) (Y f) (by
    change (Y f)^2=aeval ((inc f) Xl) f
    rw [aeval_algHom_apply,aeval_xl,OriginalQuadraticDualizing318.y_sq]
    rfl)
@[expose] def up : Overlap f →ₐ[E] D f :=
  IsLocalization.Away.liftAlgHom (f:=toBase f) (x f) (by
    change IsUnit (lift f _ _ _ (x f))
    rw [lift_x]; exact (U f).isUnit)
@[simp] theorem up_x : up f (xx f)=U f := by simp [xx,up,toBase]
@[simp] theorem up_y : up f (yy f)=Y f := by simp [yy,up,toBase]

@[expose] def leval : L E →ₐ[E] Overlap f where
  toRingHom:=LaurentPolynomial.eval₂ (algebraMap E (Overlap f)) (V f)
  commutes' a:= by
    change LaurentPolynomial.eval₂ _ _ (algebraMap E (L E) a)=_
    rw [LaurentPolynomial.algebraMap_apply,Algebra.algebraMap_self_apply,LaurentPolynomial.eval₂_C]
@[simp] theorem leval_T : leval f Xl=xx f := by
  change LaurentPolynomial.eval₂ _ (V f) (LaurentPolynomial.T 1)=_
  rw [LaurentPolynomial.eval₂_T,zpow_one]
  rfl
@[simp] theorem leval_p (p:E[X]) : leval f (toLaurent p)=aeval (xx f) p := by
  change LaurentPolynomial.eval₂ _ (V f) (toLaurent p)=_
  rw [LaurentPolynomial.eval₂_toLaurent]; rfl
@[expose] def down : D f→ₐ[E] Overlap f :=
  AdjoinRoot.liftAlgHom (OriginalQuadraticDualizing318.eqn (toLaurent f)) (leval f) (yy f) (by
    change eval₂ _ (yy f) (X^2-C (toLaurent f))=0
    rw [eval₂_sub,eval₂_pow,eval₂_X,eval₂_C,AlgHom.coe_toRingHom,leval_p,relation_overlap,sub_self])
@[simp] theorem down_base (p:L E) : down f (inc f p)=leval f p := AdjoinRoot.liftAlgHom_of .. 
@[simp] theorem down_y : down f (Y f)=yy f := AdjoinRoot.liftAlgHom_root ..
@[simp] theorem down_u : down f (U f)=xx f := by
  change down f (inc f Xl)=xx f
  rw [down_base,leval_T]

theorem down_up : (down f).comp (up f)=AlgHom.id E (Overlap f) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (x f))
  apply hom_ext f
  · change down f (up f (xx f))=xx f
    rw [up_x,down_u]
  · change down f (up f (yy f))=yy f
    rw [up_y,down_y]
theorem up_leval : (up f).comp (leval f)=inc f := by
  let inst : IsScalarTower E E[X] (L E) := IsScalarTower.of_algebraMap_eq (fun a => by
    rw [LaurentPolynomial.algebraMap_eq_toLaurent,algebraMap_eq,toLaurent_C,LaurentPolynomial.algebraMap_apply,Algebra.algebraMap_self_apply])
  apply IsLocalization.algHom_ext (Submonoid.powers (X:E[X]))
  apply Polynomial.algHom_ext
  change up f (leval f (toLaurent X))=inc f (toLaurent X)
  rw [toLaurent_X]
  exact (congrArg (up f) (leval_T f)).trans (up_x f)

theorem up_down : (up f).comp (down f)=AlgHom.id E (D f) := by
  apply AdjoinRoot.algHom_ext'
  · apply AlgHom.ext
    intro a
    change up f (down f (inc f a))=inc f a
    rw [down_base]
    exact AlgHom.congr_fun (up_leval f) a
  · change up f (down f (Y f))=Y f
    rw [down_y,up_y]

/-- Canonical equivalence of the glued scheme's actual principal overlap with
the monic quadratic Laurent algebra used for the finite dualizing counit. -/
@[expose] def equivalence : Overlap f ≃ₐ[E] D f :=
  AlgEquiv.ofAlgHom (up f) (down f) (up_down f) (down_up f)
end OriginalActualQuadraticLaurent318
#print axioms OriginalActualQuadraticLaurent318.equivalence
