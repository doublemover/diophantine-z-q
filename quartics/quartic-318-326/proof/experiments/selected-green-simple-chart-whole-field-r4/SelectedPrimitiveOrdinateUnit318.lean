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

private theorem spec_alg_comp {S A₀ A₁ A₂ : Type} [CommRing S]
    [CommRing A₀] [CommRing A₁] [CommRing A₂]
    [Algebra S A₀] [Algebra S A₁] [Algebra S A₂]
    (a : A₀ →ₐ[S] A₁) (b : A₁ →ₐ[S] A₂) :
    Spec.map (CommRingCat.ofHom (b.comp a).toRingHom) =
      Spec.map (CommRingCat.ofHom b.toRingHom) ≫ Spec.map (CommRingCat.ofHom a.toRingHom) := by
  rw [← Spec.map_comp] <;> rfl

section Fields
variable {K : Type} [Field K] [Algebra (R n) K]

private def fieldPoint (I : Ideal (D n))
    (e : PrimitiveScheme n m ≅ Spec (CommRingCat.of (D n ⧸ I)))
    (f : (D n ⧸ I) →ₐ[R n] K) : Spec (CommRingCat.of K) ⟶ PrimitiveScheme n m :=
  Spec.map (CommRingCat.ofHom f.toRingHom) ≫ e.inv

private theorem affine_eval (hm : 1 < m) (I : Ideal (D n))
    (e : PrimitiveScheme n m ≅ Spec (CommRingCat.of (D n ⧸ I)))
    (he : intoAffine n m hm = e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (f : (D n ⧸ I) →ₐ[R n] K) :
    fieldPoint n m I e f ≫ intoAffine n m hm =
      Spec.map (CommRingCat.ofHom (f.comp (q n I)).toRingHom) := by
  let j : Spec (CommRingCat.of (D n ⧸ I)) ⟶ affine n :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let p : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (D n ⧸ I)) :=
    Spec.map (CommRingCat.ofHom f.toRingHom)
  have h : intoAffine n m hm = e.hom ≫ j := he
  change (p ≫ e.inv) ≫ intoAffine n m hm = _
  calc
    _ = p ≫ j := under_chart_iso e _ _ h p
    _ = _ := (spec_alg_comp (q n I) f).symm

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
  have hread : p ≫ intoAffine n m hm =
      Spec.map (CommRingCat.ofHom (f.comp (q n I)).toRingHom) :=
    affine_eval n m hm I e he f
  calc
    _ = (p ≫ intoAffine n m hm) ≫ GluedNegation318.finiteNeg (A n) (B n) := by
      rw [Category.assoc,primitiveNeg_affine,← Category.assoc]
    _ = _ := by
      let a : D n →ₐ[R n] K := f.comp (q n I)
      let AChart := affine n
      let β : Spec (CommRingCat.of K) ⟶ AChart := Spec.map (CommRingCat.ofHom a.toRingHom)
      let γ : Spec (CommRingCat.of K) ⟶ AChart :=
        Spec.map (CommRingCat.ofHom (a.comp (sign n)).toRingHom)
      let s : AChart ⟶ AChart := GluedNegation318.finiteNeg (A n) (B n)
      have hβ : p ≫ intoAffine n m hm = β := hread
      have hsign : β ≫ s = γ := NegationPoints318.finite_evaluation (A n) (B n) a
      have hγ : γ = β := congrArg (fun F : D n →ₐ[R n] K =>
        Spec.map (CommRingCat.ofHom F.toRingHom)) (affine_sign_fixes n I f hy)
      exact (congrArg (fun g : Spec (CommRingCat.of K) ⟶ AChart => g ≫ s) hβ).trans
        (hsign.trans (hγ.trans hβ.symm))

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
