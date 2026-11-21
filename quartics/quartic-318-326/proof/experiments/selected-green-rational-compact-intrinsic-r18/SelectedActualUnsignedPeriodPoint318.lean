module
public import SelectedActualPrimitiveMark318
public import SelectedPrimitiveFixedX318
import all LiteralSchemePointGroup318
public section
noncomputable section

open AlgebraicGeometry CategoryTheory
open SelectedLiteralTorsionKernel318 SelectedPrimitiveOpen318
open SelectedPrimitiveAffineSign318 SelectedPrimitiveFixedX318
open OpenJComplexEvaluation318 LiteralSchemePointOperations318

namespace SelectedActualUnsignedPeriodPoint318

/-- Transport only the base morphism by its proved equality; neither
the curve morphism nor the selected affine coordinate changes. -/
@[expose] def overEq (N : ℕ) {T : Scheme} {b c : T ⟶ Base N} (h : b = c) :
    Points N b ≃+ Points N c := by
  subst c
  exact AddEquiv.refl _

theorem overEq_val (N : ℕ) {T : Scheme} {b c : T ⟶ Base N} (h : b = c)
    (p : Points N b) : (overEq N h p).val = p.val := by
  subst c
  rfl

private theorem spec_quot_comp {B F : Type} [CommRing B] [CommRing F]
    (I : Ideal B) (f : (B ⧸ I) →+* F) :
    Spec.map (CommRingCat.ofHom (f.comp (Ideal.Quotient.mk I))) =
      Spec.map (CommRingCat.ofHom f) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) :=
  (congrArg (fun t : CommRingCat.of B ⟶ CommRingCat.of F => Spec.map t)
    (CommRingCat.ofHom_comp (Ideal.Quotient.mk I) f)).trans
      (Spec.map_comp (CommRingCat.ofHom (Ideal.Quotient.mk I)) (CommRingCat.ofHom f))

variable (N : ℕ) [NeZero N] [IsFinite (kernelProjection N N)]
  [Etale (kernelProjection N N)]
variable (hN : 1 < N) (I : Ideal (D N))
variable (e : PrimitiveScheme N N ≅ Spec (CommRingCat.of (D N ⧸ I)))
variable (hb : primitiveProjection N N = e.hom ≫ Spec.algebraMap (R N) (D N ⧸ I))
variable (he : intoAffine N N hN = e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
variable (τ : UpperHalfPlane) (hτ : Admissible τ)

include hb he in
/-- An actual evaluation of the whole unsigned affine ring is an actual
primitive point of the evaluated short curve, with its own abscissa. -/
theorem read_point (f : (D N ⧸ I) →+* ℂ)
    (hf : f.comp (algebraMap (R N) (D N ⧸ I)) = evaluation N τ hτ) :
    ∃ P : (fiber N τ hτ).toAffine.Point,
      addOrderOf P = N ∧ CanonicalXModularity318.pointX P = f (xbar N I) := by
  letI : Algebra (R N) ℂ := (evaluation N τ hτ).toAlgebra
  let fA : (D N ⧸ I) →ₐ[R N] ℂ :=
    { toRingHom := f
      commutes' := fun r => DFunLike.congr_fun hf r }
  let a := fA.comp (q N I)
  let g : AffineSchemeSolutions318.SchemePoints (K := ℂ) (A N) (B N) :=
    Spec.homEquivAlgHom.symm a
  let p := Spec.map (CommRingCat.ofHom f) ≫ e.inv
  let k := p ≫ inclusionOpen N N
  have hb' : k ≫ kernelProjection N N = Spec.algebraMap (R N) ℂ := by
    change p ≫ primitiveProjection N N = _
    rw [hb]
    change (Spec.map (CommRingCat.ofHom f) ≫ e.inv) ≫
      e.hom ≫ Spec.algebraMap (R N) (D N ⧸ I) = _
    rw [Category.assoc,← Category.assoc e.inv,e.inv_hom_id,Category.id_comp]
    rw [← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom (f.comp (algebraMap (R N) (D N ⧸ I)))) =
      Spec.map (CommRingCat.ofHom (evaluation N τ hτ))
    rw [hf]
  have ho : addOrderOf (pointOf N N k) = N := by
    apply (primitive_iff_order N N k default (Nat.pos_of_ne_zero (NeZero.ne N))).mp
    have hRange : Set.range (inclusionOpen N N) =
        ((primitive N N : (Kernel N N).Opens) : Set (Kernel N N)) := by
      rw [Scheme.Opens.range_ι]
    change (p ≫ inclusionOpen N N) default ∈ _
    rw [Scheme.Hom.comp_apply]
    change inclusionOpen N N (p default) ∈
      ((primitive N N : (Kernel N N).Opens) : Set (Kernel N N))
    rw [← hRange]
    exact ⟨p default,rfl⟩
  have hval : (CompletedFieldPoints318.finiteInclusion (A N) (B N) g).val =
      (pointOf N N k).val := by
    let AChart := affine N
    let j : Spec (CommRingCat.of (D N ⧸ I)) ⟶ AChart :=
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
    let pre : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of (D N ⧸ I)) :=
      Spec.map (CommRingCat.ofHom f)
    let v : Spec (CommRingCat.of ℂ) ⟶ AChart := Spec.map (CommRingCat.ofHom a.toRingHom)
    have hmap : a.toRingHom = f.comp (Ideal.Quotient.mk I) := by
      apply RingHom.ext
      intro r
      rfl
    have hcomp₀ := @spec_quot_comp (D N) ℂ inferInstance inferInstance I f
    have hcomp : v = pre ≫ j :=
      (congrArg (fun t : D N →+* ℂ => Spec.map (CommRingCat.ofHom t)) hmap).trans hcomp₀
    have h' : p ≫ intoAffine N N hN = pre ≫ j := by
      change (pre ≫ e.inv) ≫ intoAffine N N hN = _
      have hi : intoAffine N N hN = e.hom ≫ j := he
      rw [hi,Category.assoc,e.inv_hom_id_assoc]
    change v ≫ chart N = _
    calc
      _ = (p ≫ intoAffine N N hN) ≫ chart N :=
        congrArg (fun t : Spec (CommRingCat.of ℂ) ⟶ AChart => t ≫ chart N) (hcomp.trans h'.symm)
      _ = _ := by rw [Category.assoc,intoAffine_chart] <;> rfl
  let E := SelectedActualPrimitiveMark318.fieldAddEquiv N (K := ℂ)
  let i : Points N (Spec.algebraMap (R N) ℂ) :=
    CompletedFieldPoints318.finiteInclusion (A N) (B N) g
  let P := E i
  have hRead : CompletedAdditionPoints318.finiteHom N g = a :=
    Spec.homEquivAlgHom.apply_symm_apply a
  have hP : i = overEq N hb' (pointOf N N k) :=
    Subtype.ext (hval.trans (overEq_val N hb' (pointOf N N k)).symm)
  refine ⟨P,?_,?_⟩
  · let T := overEq N hb'
    change addOrderOf (E.toAddMonoidHom i) = N
    calc
      _ = addOrderOf i := addOrderOf_injective E.toAddMonoidHom E.injective i
      _ = addOrderOf (T.toAddMonoidHom (pointOf N N k)) :=
        congrArg addOrderOf (show i = T.toAddMonoidHom (pointOf N N k) from hP)
      _ = addOrderOf (pointOf N N k) :=
        addOrderOf_injective T.toAddMonoidHom T.injective (pointOf N N k)
      _ = N := ho
  · have hEq :
        P = LiteralCompletedPoints318.fieldPointEquiv N
          (CompletedFieldPoints318.finiteInclusion (A N) (B N) g) := rfl
    rw [hEq,CompletedAdditionPoints318.finite_reading,hRead] <;> rfl

end SelectedActualUnsignedPeriodPoint318

#print axioms SelectedActualUnsignedPeriodPoint318.read_point
