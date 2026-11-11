module
public import ScalarWeightedFiniteSeparation318
public import WholeGeneratorEvaluationSeparation318
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public section
noncomputable section
namespace PrimitiveFinitePointSeparator318
open Set Polynomial
variable {F K A L T : Type*} [Field F] [Infinite F]
  [Field K] [Algebra F K] [CommRing A] [Algebra F A]
  [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [Algebra F L] [IsScalarTower F K L] [Algebra A L] [IsFractionRing A L]
  [IsScalarTower F A L]
  [Field T] [IsAlgClosed T] [Algebra K T] [Algebra F T] [IsScalarTower F K T]

@[expose] def element {n : ℕ} (a : Fin n → A) (c : F) : A :=
  ∑ i : Fin n, a i * (algebraMap F A c)^i.val

lemma field_value {n : ℕ} (a : Fin n → A) (c : F) (f : L →ₐ[K] T) :
    f (algebraMap A L (element a c)) =
      ScalarWeightedFiniteSeparation318.weighted (algebraMap F T c)
        (fun i => f (algebraMap A L (a i))) := by
  have hc : f (algebraMap A L (algebraMap F A c)) = algebraMap F T c := by
    rw [←IsScalarTower.algebraMap_apply F A L]
    exact (f.restrictScalars F).commutes c
  simp only [element,ScalarWeightedFiniteSeparation318.weighted,map_sum,map_mul,map_pow,hc]

lemma point_value {n : ℕ} (a : Fin n → A) (c : F) (v : A →ₐ[F] F) :
    algebraMap F T (v (element a c)) =
      ScalarWeightedFiniteSeparation318.weighted (algebraMap F T c)
        (fun i => algebraMap F T (v (a i))) := by
  simp only [element,ScalarWeightedFiniteSeparation318.weighted,map_sum,map_mul,map_pow,
    AlgHom.commutes,Algebra.algebraMap_self,RingHom.id_apply]

/-- A SINGLE literal constant-weighted combination of the original
whole-ring generators simultaneously generates the actual fraction-field
extension and separates ANY specified finite set of complex-style
points. Generic primitivity and point separation are proved separately
using one shared finite-root exclusion, not inferred from each other. -/
include T in
theorem exists_primitive_separator {n : ℕ} (a : Fin n → A)
    (hgen : Function.Surjective (MvPolynomial.aeval a : MvPolynomial (Fin n) F →ₐ[F] A))
    (V : Set (A →ₐ[F] F)) (hV : V.Finite) :
    ∃ c : F,
      Function.Surjective (Polynomial.aeval (algebraMap A L (element a c)) :
        Polynomial K →ₐ[K] L) ∧
      Set.InjOn (fun v : A →ₐ[F] F => v (element a c)) V := by
  classical
  let vf (f : L →ₐ[K] T) : Fin n → T := fun i => f (algebraMap A L (a i))
  let vp (v : A →ₐ[F] F) : Fin n → T := fun i => algebraMap F T (v (a i))
  let W : Set (Fin n → T) := Set.range vf ∪ vp '' V
  have hW : W.Finite := (Set.finite_range vf).union (hV.image vp)
  obtain ⟨c,hc⟩ := ScalarWeightedFiniteSeparation318.exists_weighted_injective
    (F := F) W hW
  have hfield : Function.Injective
      (fun f : L →ₐ[K] T => f (algebraMap A L (element a c))) := by
    intro f g he
    have hv : vf f = vf g := hc (Or.inl ⟨f,rfl⟩) (Or.inl ⟨g,rfl⟩)
      (by simpa only [vf,←field_value] using he)
    exact WholeGeneratorEvaluationSeparation318.fraction_hom_ext a hgen f g (congrFun hv)
  have hprimitive : IntermediateField.adjoin K {algebraMap A L (element a c)} = ⊤ :=
    (Field.primitive_element_iff_algHom_eq_of_eval' K T
      (fun z => IsAlgClosed.splits _) _).mpr hfield
  refine ⟨c,?_,?_⟩
  · apply (AlgHom.range_eq_top _).mp
    rw [←Algebra.adjoin_singleton_eq_range_aeval,
      ←IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
        (IsIntegral.of_finite K (algebraMap A L (element a c))).isAlgebraic,
      hprimitive]
    rfl
  · intro v hv w hw he
    have hcoords : vp v = vp w := hc (Or.inr ⟨v,hv,rfl⟩) (Or.inr ⟨w,hw,rfl⟩)
      (by simpa only [vp,←point_value] using congrArg (algebraMap F T) he)
    apply WholeGeneratorEvaluationSeparation318.algebra_hom_ext a hgen v w
    intro i
    exact (algebraMap F T).injective (congrFun hcoords i)
end PrimitiveFinitePointSeparator318
