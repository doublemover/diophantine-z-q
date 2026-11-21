module
public import SelectedPrimitiveFixedX318
public import Mathlib.RingTheory.Ideal.Maximal
import all LiteralSchemePointGroup318
public section
noncomputable section
open AlgebraicGeometry CategoryTheory
open SelectedLiteralTorsionKernel318 SelectedPrimitiveOpen318 LiteralSchemePointOperations318
open SelectedPrimitiveAffineSign318 SelectedPrimitiveFixedX318

namespace SelectedPrimitiveOrdinateUnit318

variable (n m : ℕ)
variable [IsFinite (kernelProjection n m)] [Etale (kernelProjection n m)]

private theorem under_chart_iso {S T A U : Scheme} (e : S ≅ T)
    (i : S ⟶ A) (j : T ⟶ A) (h : i = e.hom ≫ j) (p : U ⟶ T) :
    (p ≫ e.inv) ≫ i = p ≫ j := by
  rw [h,Category.assoc,e.inv_hom_id_assoc]

private theorem spec_quot_comp {B F : Type} [CommRing B] [CommRing F]
    (I : Ideal B) (f : (B ⧸ I) →+* F) :
    Spec.map (CommRingCat.ofHom (f.comp (Ideal.Quotient.mk I))) =
      Spec.map (CommRingCat.ofHom f) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) :=
  (congrArg (fun t : CommRingCat.of B ⟶ CommRingCat.of F => Spec.map t)
    (CommRingCat.ofHom_comp (Ideal.Quotient.mk I) f)).trans
      (Spec.map_comp (CommRingCat.ofHom (Ideal.Quotient.mk I)) (CommRingCat.ofHom f))

section Fields
variable {K : Type} [Field K] [Algebra (R n) K]

private def fieldPoint (I : Ideal (D n))
    (e : PrimitiveScheme n m ≅ Spec (CommRingCat.of (D n ⧸ I)))
    (f : (D n ⧸ I) →ₐ[R n] K) : Spec (CommRingCat.of K) ⟶ PrimitiveScheme n m :=
  Spec.map (CommRingCat.ofHom f.toRingHom) ≫ e.inv

private theorem affine_sign_fixes (I : Ideal (D n)) (f : (D n ⧸ I) →ₐ[R n] K)
    (hy : f (ybar n I) = 0) : (f.comp (q n I)).comp (sign n) = f.comp (q n I) := by
  apply AffineEquationFunctor318.hom_ext
  · simp only [AlgHom.comp_apply,ChartNegation318.affineNeg_x]
  · rw [AlgHom.comp_apply,ChartNegation318.affineNeg_y,map_neg]
    change -(f (ybar n I)) = f (ybar n I)
    rw [hy,neg_zero]

private theorem fixes_primitive (hm : 1 < m) (I : Ideal (D n))
    (e : PrimitiveScheme n m ≅ Spec (CommRingCat.of (D n ⧸ I)))
    (he : intoAffine n m hm = e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (f : (D n ⧸ I) →ₐ[R n] K) (hy : f (ybar n I) = 0) :
    fieldPoint n m I e f ≫ primitiveNeg n m = fieldPoint n m I e f := by
  let p : Spec (CommRingCat.of K) ⟶ PrimitiveScheme n m := fieldPoint n m I e f
  haveI : IsClosedImmersion (intoAffine n m hm) := closed_intoAffine n m hm
  apply (cancel_mono (intoAffine n m hm)).mp
  change (p ≫ primitiveNeg n m) ≫ intoAffine n m hm = p ≫ intoAffine n m hm
  let pre : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (D n ⧸ I)) :=
    Spec.map (CommRingCat.ofHom f.toRingHom)
  let j : Spec (CommRingCat.of (D n ⧸ I)) ⟶ affine n :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let a : D n →ₐ[R n] K := f.comp (q n I)
  let β : Spec (CommRingCat.of K) ⟶ affine n := Spec.map (CommRingCat.ofHom a.toRingHom)
  let γ : Spec (CommRingCat.of K) ⟶ affine n :=
    Spec.map (CommRingCat.ofHom (a.comp (sign n)).toRingHom)
  let s : affine n ⟶ affine n := GluedNegation318.finiteNeg (A n) (B n)
  have hmap : a.toRingHom = f.toRingHom.comp (Ideal.Quotient.mk I) := by
    apply RingHom.ext
    intro r
    rfl
  have hcomp₀ := @spec_quot_comp (D n) K inferInstance inferInstance I f.toRingHom
  have hcomp : β = pre ≫ j :=
    (congrArg (fun t : D n →+* K => Spec.map (CommRingCat.ofHom t)) hmap).trans hcomp₀
  have hRead : p ≫ intoAffine n m hm = pre ≫ j := by
    have h : intoAffine n m hm = e.hom ≫ j := he
    change (pre ≫ e.inv) ≫ intoAffine n m hm = _
    exact under_chart_iso e _ _ h pre
  have hβ : p ≫ intoAffine n m hm = β := hRead.trans hcomp.symm
  have hsign : β ≫ s = γ := NegationPoints318.finite_evaluation (A n) (B n) a
  have hγ : γ = β := congrArg (fun F : D n →ₐ[R n] K =>
    Spec.map (CommRingCat.ofHom F.toRingHom)) (affine_sign_fixes n I f hy)
  calc
    _ = (p ≫ intoAffine n m hm) ≫ s := by
      change _ = (p ≫ intoAffine n m hm) ≫ GluedNegation318.finiteNeg (A n) (B n)
      rw [Category.assoc,primitiveNeg_affine,← Category.assoc]
    _ = β ≫ s := congrArg (fun g : Spec (CommRingCat.of K) ⟶ affine n => g ≫ s) hβ
    _ = γ := hsign
    _ = β := hγ
    _ = _ := hβ.symm

/-- The actual geometric/field point of a primitive chart cannot have
zero ordinate when the marked order is greater than two. -/
theorem field_eval_ne_zero (hm : 1 < m) (I : Ideal (D n))
    (e : PrimitiveScheme n m ≅ Spec (CommRingCat.of (D n ⧸ I)))
    (he : intoAffine n m hm = e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (f : (D n ⧸ I) →ₐ[R n] K) (hm₂ : 2 < m) : f (ybar n I) ≠ 0 := by
  intro hy
  let p : Spec (CommRingCat.of K) ⟶ PrimitiveScheme n m := fieldPoint n m I e f
  let k : Spec (CommRingCat.of K) ⟶ Kernel n m := p ≫ inclusionOpen n m
  let P := pointOf n m k
  have hRange : Set.range (inclusionOpen n m) =
      ((primitive n m : (Kernel n m).Opens) : Set (Kernel n m)) := by
    rw [Scheme.Opens.range_ι]
  have hp : k default ∈ primitive n m := by
    change (p ≫ inclusionOpen n m) default ∈ primitive n m
    rw [Scheme.Hom.comp_apply]
    change inclusionOpen n m (p default) ∈
      ((primitive n m : (Kernel n m).Opens) : Set (Kernel n m))
    rw [← hRange]
    exact ⟨p default,rfl⟩
  have ht : addOrderOf P = m :=
    (primitive_iff_order n m k default (lt_trans (by decide : 0 < 2) hm₂)).mp hp
  have hneg : -P = P := by
    apply Subtype.ext
    have hfix : p ≫ primitiveNeg n m = p := fixes_primitive n m hm I e he f hy
    have h := congrArg (fun z : Spec (CommRingCat.of K) ⟶ PrimitiveScheme n m =>
      z ≫ inclusionOpen n m ≫ inclusion n m) hfix
    change ((p ≫ inclusionOpen n m) ≫ inclusion n m) ≫ curveNeg n =
      (p ≫ inclusionOpen n m) ≫ inclusion n m
    simpa only [Category.assoc,primitiveNeg_open_assoc,kernelNeg_inclusion] using h
  have htwo : (2:ℕ) • P = 0 := by
    rw [two_nsmul]
    calc
      P + P = (-P) + P := congrArg (fun x => x + P) hneg.symm
      _ = 0 := neg_add_cancel P
  have hd : addOrderOf P ∣ 2 := addOrderOf_dvd_iff_nsmul_eq_zero.mpr htwo
  rw [ht] at hd
  exact (Nat.not_le_of_gt hm₂) (Nat.le_of_dvd (by decide : 0 < 2) hd)
end Fields

private theorem unit_of_all_maximal_quotients {B : Type*} [CommRing B] (b : B)
    (h : ∀ (M : Ideal B), M.IsMaximal → Ideal.Quotient.mk M b ≠ 0) :
    IsUnit b := by
  classical
  by_contra hn
  have hProper : Ideal.span ({b} : Set B) ≠ ⊤ := by
    exact fun ht => hn ((Ideal.span_singleton_eq_top (x := b)).mp ht)
  obtain ⟨M,hM,hinc⟩ := Ideal.exists_le_maximal _ hProper
  exact h M hM (Ideal.Quotient.eq_zero_iff_mem.mpr
    (hinc (Ideal.subset_span (Set.mem_singleton _))))

/-- The true primitive ordinate is a unit in the whole actual affine
coordinate algebra. Residue tests detect nonunits; no field-point
criterion is used to assert equality of arbitrary Scheme maps. -/
theorem ordinate_unit (hm : 1 < m) (I : Ideal (D n))
    (e : PrimitiveScheme n m ≅ Spec (CommRingCat.of (D n ⧸ I)))
    (he : intoAffine n m hm = e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (hm₂ : 2 < m) : IsUnit (ybar n I) := by
  refine @unit_of_all_maximal_quotients (D n ⧸ I) inferInstance (ybar n I) ?_
  intro M hM
  letI : M.IsMaximal := hM
  letI : Field ((D n ⧸ I) ⧸ M) := Ideal.Quotient.field M
  let f : (D n ⧸ I) →ₐ[R n] ((D n ⧸ I) ⧸ M) := Ideal.Quotient.mkₐ (R n) M
  change f (ybar n I) ≠ 0
  exact field_eval_ne_zero n m hm I e he f hm₂

end SelectedPrimitiveOrdinateUnit318

#print axioms SelectedPrimitiveOrdinateUnit318.field_eval_ne_zero
#print axioms SelectedPrimitiveOrdinateUnit318.ordinate_unit
