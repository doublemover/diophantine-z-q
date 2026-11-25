module
public import OriginalAffineOriginFirstOrder318
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

@[expose] public section
noncomputable section

namespace OriginalActualOriginAffineJet318

open AlgebraicGeometry CategoryTheory MonoidalCategory
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open OriginalAffineOriginCotangent318 OriginalAffineOriginFirstOrder318

universe u

def sp {P Q : Type u} [CommRing P] [CommRing Q] (f : P →+* Q) :
    Spec (.of Q) ⟶ Spec (.of P) := Spec.map (CommRingCat.ofHom f)

theorem sp_comp {P Q T : Type u} [CommRing P] [CommRing Q] [CommRing T]
    (f : P →+* Q) (g : Q →+* T) : sp g ≫ sp f = sp (g.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

variable (R : Type u) [CommRing R]

abbrev Thick (M : Type u) [AddCommGroup M] [Module R M] := TrivSqZeroExt R M

def testBase (M : Type u) [AddCommGroup M] [Module R M] :
    Spec (.of (Thick R M)) ⟶ Spec (.of R) := sp (algebraMap R (Thick R M))

def zeroSection (M : Type u) [AddCommGroup M] [Module R M] :
    Spec (.of R) ⟶ Spec (.of (Thick R M)) :=
  sp (TrivSqZeroExt.fstHom R R M).toRingHom

/-- The genuine closed zero section is onto on the underlying space.
We do not assume or conclude equality of maps from reduced reads. -/
theorem zero_surjective (M : Type u) [AddCommGroup M] [Module R M] :
    Function.Surjective (zeroSection R M) := by
  let p := (TrivSqZeroExt.fstHom R R M).toRingHom
  have hp : Function.Surjective p := fun r => ⟨TrivSqZeroExt.inl r, rfl⟩
  intro x
  change x ∈ Set.range (PrimeSpectrum.comap p)
  rw [PrimeSpectrum.range_comap_of_surjective p hp]
  intro t ht
  have ht' : t.fst = 0 := ht
  have hsq : t ^ 2 = 0 := by
    rw [pow_two]
    apply TrivSqZeroExt.ext
    · simp [ht']
    · simp [ht']
  exact x.isPrime.mem_of_pow_mem 2 (by rw [hsq]; exact x.asIdeal.zero_mem)

variable {B : Type u} [CommRing B] [Algebra R B]

/-- Actual affine open in the group, with its genuine identity. The chart
is not asserted affine globally or stable under either endomorphism. -/
structure Chart (A : Over (Spec (.of R))) [MonObj A] (e : B →ₐ[R] R) where
  incl : Spec (.of B) ⟶ A.left
  open_incl : IsOpenImmersion incl
  over : incl ≫ A.hom = sp (algebraMap R B)
  origin : sp e.toRingHom ≫ incl = (η[A]).left

variable {R} {A : Over (Spec (.of R))} [MonObj A] {e : B →ₐ[R] R} (C : Chart R A e)

instance : IsOpenImmersion C.incl := C.open_incl

abbrev ActualBased (M : Type u) [AddCommGroup M] [Module R M] :=
  {q : (Over.mk (testBase R M)) ⟶ A // zeroSection R M ≫ q.left = (η[A]).left}

/-- The actual chart contains every based first-order point, because its
topological support is in the true origin, even if the base is nonreduced. -/
theorem support_in_chart {M : Type u} [AddCommGroup M] [Module R M]
    (q : ActualBased (R := R) (A := A) M) : Set.range q.1.left ⊆ Set.range C.incl := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, rfl⟩ := zero_surjective R M x
  refine ⟨sp e.toRingHom y, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, C.origin, q.2]

def throughChart {M : Type u} [AddCommGroup M] [Module R M]
    (q : ActualBased (R := R) (A := A) M) :
    Spec (.of (Thick R M)) ⟶ Spec (.of B) :=
  IsOpenImmersion.lift C.incl q.1.left (support_in_chart C q)

@[reassoc (attr := simp)] theorem throughChart_incl {M : Type u} [AddCommGroup M] [Module R M]
    (q : ActualBased (R := R) (A := A) M) : throughChart C q ≫ C.incl = q.1.left :=
  IsOpenImmersion.lift_fac _ _ _

theorem throughChart_origin {M : Type u} [AddCommGroup M] [Module R M]
    (q : ActualBased (R := R) (A := A) M) :
    zeroSection R M ≫ throughChart C q = sp e.toRingHom := by
  apply (cancel_mono C.incl).mp
  rw [Category.assoc, throughChart_incl, q.2, C.origin]

private def comorphism {M : Type u} [AddCommGroup M] [Module R M]
    (q : ActualBased (R := R) (A := A) M) : B →ₐ[R] Thick R M :=
  let a := Spec.preimage (throughChart C q)
  { toRingHom := a.hom
    commutes' r := by
      have h : CommRingCat.ofHom (algebraMap R B) ≫ a =
          CommRingCat.ofHom (algebraMap R (Thick R M)) := by
        apply Spec.map_injective
        rw [Spec.map_comp, Spec.map_preimage]
        change throughChart C q ≫ sp (algebraMap R B) = testBase R M
        rw [← C.over, ← Category.assoc, throughChart_incl]
        exact Over.w q.1
      exact congrArg (fun k => k.hom r) h }

private theorem sp_comorphism {M : Type u} [AddCommGroup M] [Module R M]
    (q : ActualBased (R := R) (A := A) M) :
    sp (comorphism C q).toRingHom = throughChart C q :=
  Spec.map_preimage _

private def readLift {M : Type u} [AddCommGroup M] [Module R M]
    (q : ActualBased (R := R) (A := A) M) : Lift (S := R) (M := M) e :=
  ⟨comorphism C q, by
    have h : CommRingCat.ofHom ((TrivSqZeroExt.fstHom R R M).comp
          (comorphism C q)).toRingHom = CommRingCat.ofHom e.toRingHom := by
      apply Spec.map_injective
      change sp ((TrivSqZeroExt.fstHom R R M).toRingHom.comp (comorphism C q).toRingHom) =
        sp e.toRingHom
      rw [← sp_comp, sp_comorphism]
      exact throughChart_origin C q
    ext b
    exact congrArg (fun k => k.hom b) h⟩

private def ofLift {M : Type u} [AddCommGroup M] [Module R M]
    (f : Lift (S := R) (M := M) e) : ActualBased (R := R) (A := A) M :=
  ⟨Over.homMk (sp f.1.toRingHom ≫ C.incl) (by
    rw [Category.assoc, C.over, sp_comp]
    change sp (f.1.toRingHom.comp (algebraMap R B)) = sp (algebraMap R (Thick R M))
    congr 1
    ext r
    exact f.1.commutes r),
  by
    change zeroSection R M ≫ (sp f.1.toRingHom ≫ C.incl) = (η[A]).left
    rw [← Category.assoc, zeroSection, sp_comp]
    have he : (TrivSqZeroExt.fstHom R R M).toRingHom.comp f.1.toRingHom = e.toRingHom := by
      ext r
      exact congrArg (fun k : B →ₐ[R] R => k r) f.2
    rw [he, C.origin]⟩

/-- Actual based jet equivalence on one given group. Unlike assigning a
new frame to a geometric point, this tests the whole Spec of the nonreduced ring. -/
def actual {M : Type u} [AddCommGroup M] [Module R M] :
    (Cot e →ₗ[R] M) ≃ ActualBased (R := R) (A := A) M :=
  (points (S := R) e).trans
    { toFun := ofLift C
      invFun := readLift C
      left_inv := fun f => by
        apply Subtype.ext
        apply AlgHom.toRingHom_injective
        have h : CommRingCat.ofHom (comorphism C (ofLift C f)).toRingHom =
            CommRingCat.ofHom f.1.toRingHom := by
          apply Spec.map_injective
          change sp (comorphism C (ofLift C f)).toRingHom = sp f.1.toRingHom
          rw [sp_comorphism]
          apply (cancel_mono C.incl).mp
          exact throughChart_incl C _
        exact congrArg (fun k : CommRingCat.of B ⟶ CommRingCat.of (Thick R M) => k.hom) h
      right_inv := fun q => by
        apply Subtype.ext
        apply Over.OverMorphism.ext
        change sp (comorphism C q).toRingHom ≫ C.incl = q.1.left
        rw [sp_comorphism, throughChart_incl] }

theorem actual_left {M : Type u} [AddCommGroup M] [Module R M] (v : Cot e →ₗ[R] M) :
    (actual C v).1.left = sp ((points (S := R) e v).1).toRingHom ≫ C.incl := rfl

end OriginalActualOriginAffineJet318

#print axioms OriginalActualOriginAffineJet318.zero_surjective
#print axioms OriginalActualOriginAffineJet318.throughChart_origin
#print axioms OriginalActualOriginAffineJet318.actual
