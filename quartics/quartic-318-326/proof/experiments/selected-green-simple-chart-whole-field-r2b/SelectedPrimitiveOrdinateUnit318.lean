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
variable (n m : ℕ) [IsFinite (kernelProjection n m)] [Etale (kernelProjection n m)]
variable (hm : 1 < m) (I : Ideal (D n))
local notation "Q" => D n ⧸ I
variable (e : PrimitiveScheme n m ≅ Spec (CommRingCat.of Q))
section Field
variable {K : Type} [Field K] [Algebra (R n) K]

private theorem affine_eval
    (hcompare : intoAffine n m hm =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (f : Q →ₐ[R n] K) :
    (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ e.inv) ≫ intoAffine n m hm =
      Spec.map (CommRingCat.ofHom (f.comp (q n I)).toRingHom) := by
  simp only [Category.assoc,hcompare,e.inv_hom_id_assoc]
  rw [←Spec.map_comp] <;> rfl

private theorem affine_sign_fixes (f : Q →ₐ[R n] K)
    (hy : f (ybar n I) = 0) : (f.comp (q n I)).comp (sign n) = f.comp (q n I) := by
  apply AffineEquationFunctor318.hom_ext
  · simp only [AlgHom.comp_apply,ChartNegation318.affineNeg_x]
  · rw [AlgHom.comp_apply,ChartNegation318.affineNeg_y,map_neg]
    change -(f (ybar n I)) = f (ybar n I)
    rw [hy,neg_zero]

private theorem fixes_primitive
    (hcompare : intoAffine n m hm =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (f : Q →ₐ[R n] K) (hy : f (ybar n I) = 0) :
    (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ e.inv) ≫ primitiveNeg n m =
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫ e.inv := by
  let p := Spec.map (CommRingCat.ofHom f.toRingHom) ≫ e.inv
  change p ≫ primitiveNeg n m = p
  haveI : IsClosedImmersion (intoAffine n m hm) := closed_intoAffine n m hm
  apply (cancel_mono (intoAffine n m hm)).mp
  calc
    _ = (p ≫ intoAffine n m hm) ≫ GluedNegation318.finiteNeg (A n) (B n) := by
      rw [Category.assoc,primitiveNeg_affine,←Category.assoc]
    _ = _ := by
      rw [affine_eval n m hm I e hcompare f,NegationPoints318.finite_evaluation,
        affine_sign_fixes n I f hy]

/-- The actual geometric/field point of a primitive chart cannot have
zero ordinate when the marked order is greater than two. -/
theorem field_eval_ne_zero
    (hcompare : intoAffine n m hm =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (f : Q →ₐ[R n] K) (hm₂ : 2 < m) : f (ybar n I) ≠ 0 := by
  intro hy
  let p := Spec.map (CommRingCat.ofHom f.toRingHom) ≫ e.inv
  let k := p ≫ inclusionOpen n m
  let P := pointOf n m k
  have hp : k default ∈ primitive n m := by
    change (p ≫ inclusionOpen n m) default ∈ primitive n m
    rw [Scheme.Hom.comp_apply,←Scheme.Opens.range_ι]
    exact ⟨p default,rfl⟩
  have ht : addOrderOf P = m :=
    (primitive_iff_order n m k default (lt_trans (by decide : 0 < 2) hm₂)).mp hp
  have hneg : -P = P := by
    apply Subtype.ext
    have h := congrArg (fun z => z ≫ inclusionOpen n m ≫ inclusion n m)
      (fixes_primitive n m hm I e hcompare f hy)
    change ((p ≫ inclusionOpen n m) ≫ inclusion n m) ≫ curveNeg n =
      (p ≫ inclusionOpen n m) ≫ inclusion n m
    simpa only [Category.assoc,primitiveNeg_open_assoc,kernelNeg_inclusion] using h
  have htwo : (2:ℕ) • P = 0 := by
    rw [two_nsmul]
    calc
      P + P = (-P) + P := congrArg (fun x => x + P) hneg.symm
      _ = 0 := neg_add_cancel P
  have hd := addOrderOf_dvd_iff_nsmul_eq_zero.mpr htwo
  rw [ht] at hd
  exact (Nat.not_le_of_gt hm₂) (Nat.le_of_dvd (by decide : 0 < 2) hd)
end Field

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
theorem ordinate_unit
    (hcompare : intoAffine n m hm =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (hm₂ : 2 < m) : IsUnit (ybar n I) := by
  refine @unit_of_all_maximal_quotients Q inferInstance (ybar n I) ?_
  intro M hM
  let K := Q ⧸ M
  letI : M.IsMaximal := hM
  letI : Field K := Ideal.Quotient.field M
  let f : Q →ₐ[R n] K := Ideal.Quotient.mkₐ (R n) M
  change f (ybar n I) ≠ 0
  exact field_eval_ne_zero n m hm I e hcompare f hm₂

end SelectedPrimitiveOrdinateUnit318

#print axioms SelectedPrimitiveOrdinateUnit318.field_eval_ne_zero
#print axioms SelectedPrimitiveOrdinateUnit318.ordinate_unit
