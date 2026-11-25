module
public import OriginalLiteralContactQuotientPoint318
public import SourceNormalChart318
public import SourceTwistArithmetic318
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

@[expose] public section
noncomputable section

namespace OriginalCanonicalContactOpenRecognition318
open AlgebraicGeometry CategoryTheory
open ContactKummerOrder318 (OpenBase OpenOrder)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section IntegralRestriction

variable {U A D L M : Type}
  [CommRing U] [CommRing A] [CommRing D] [CommRing L] [CommRing M]
  [Algebra U A] [Algebra U D] [Algebra U L] [Algebra U M]
  [Algebra A L] [Algebra D M] [IsScalarTower U A L] [IsScalarTower U D M]
  [IsFractionRing A L] [IsFractionRing D M]
  [IsIntegrallyClosed A] [IsIntegrallyClosed D]
  [Module.Finite U A] [Module.Finite U D]

/-- A comparison of the genuine function fields descends to the full
normal finite affine orders, without choosing one point or one factor. -/
def orderEquiv (e : L ≃ₐ[U] M) : A ≃ₐ[U] D := by
  letI : IsIntegralClosure A U L := IsIntegralClosure.of_isIntegrallyClosed A U L
  letI : IsIntegralClosure D U M := IsIntegralClosure.of_isIntegrallyClosed D U M
  exact (IsIntegralClosure.equiv U A L (integralClosure U L)).trans
    (e.mapIntegralClosure.trans (IsIntegralClosure.equiv U (integralClosure U M) M D))

/-- The affine comparison really restricts the supplied field map. -/
theorem orderEquiv_read (e : L ≃ₐ[U] M) (a : A) :
    algebraMap D M (orderEquiv e a) = e (algebraMap A L a) := by
  let r := IsIntegralClosure.equiv U A L (integralClosure U L)
  let s := IsIntegralClosure.equiv U (integralClosure U M) M D
  change algebraMap D M (s (e.mapIntegralClosure (r a))) = e (algebraMap A L a)
  calc
    _ = (e.mapIntegralClosure (r a) : M) :=
      IsIntegralClosure.algebraMap_equiv U (integralClosure U M) M D _
    _ = _ := congrArg e (IsIntegralClosure.algebraMap_equiv U A L (integralClosure U L) a)

/-- No choice of origin, sign or other normalization remains after
the actual function-field comparison is fixed. -/
theorem orderEquiv_unique (e : L ≃ₐ[U] M) (g : A →ₐ[U] D)
    (hg : ∀ a, algebraMap D M (g a) = e (algebraMap A L a)) :
    (orderEquiv e).toAlgHom = g := by
  ext a
  apply IsFractionRing.injective D M
  exact (orderEquiv_read e a).trans (hg a).symm

end IntegralRestriction

local notation "U" => OpenBase
local notation "c" => SourceTwistArithmetic318.units
local notation "A" => OpenOrder c
local notation "L" => SourceOpenFractionField318.L c
local notation "P" => ProjectiveJLine318.scheme ℚ
local notation "q" => OriginalLiteralContactQuotientPoint318.point

local instance originalFractionAlgebra : Algebra A L :=
  (SourceOpenFractionField318.openEmbedding c).toAlgebra
local instance originalFraction : IsFractionRing A L :=
  SourceOpenFractionField318.open_fractionField c
local instance originalBaseAlgebra : Algebra U L :=
  ((SourceOpenFractionField318.openEmbedding c).comp (algebraMap U A)).toAlgebra
local instance originalTower : IsScalarTower U A L :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)
local instance originalNormal : IsIntegrallyClosed A :=
  SourceNormalChart318.source_integrallyClosed c
local instance originalFinite : Module.Finite U A :=
  (ContactKummerOrder318.open_finite_free_etale c).1

variable {D M : Type} [CommRing D] [CommRing M] [Algebra U D] [Algebra U M] [Algebra D M]
  [IsScalarTower U D M] [IsFractionRing D M] [IsIntegrallyClosed D] [Module.Finite U D]
variable (e : L ≃ₐ[U] M)

/-- Restriction to the actual original (U), before any specialization
or chosen fine-level point. The direction on schemes is contravariant. -/
def sourceToCanonical : ContactKummerCover318.cover c ≅ Spec (CommRingCat.of D) :=
  Scheme.Spec.mapIso (orderEquiv e).symm.toCommRingCatIso.op

theorem sourceToCanonical_over :
    (sourceToCanonical e).hom ≫ Spec.algebraMap U D = ContactKummerCover318.structureMap c := by
  change Spec.map (CommRingCat.ofHom (orderEquiv e).symm.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap U D)) =
    Spec.map (CommRingCat.ofHom (algebraMap U A))
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact RingHom.ext (orderEquiv e).symm.commutes

variable {C Z : Scheme} (j : Spec (CommRingCat.of D) ⟶ C) (chi : C ⟶ P)
  (hj : j ≫ chi = Spec.algebraMap U D ≫ ContactProjectiveModel318.baseOpen)
  (f : Z ⟶ C) [Surjective f]

/-- The actual finite PEL forget can now be evaluated over the literal
point using just its canonical open chart and the rational function
field identification. No global isomorphism to the explicit model is
an extra input. The chart equation is an equality of scheme arrows. -/
theorem fine_point_over_original (u v : ℤ)
    (hne : ∀ i : Fin 5, ContactRadical318.forms u v i ≠ 0) :
    ∃ z : Z, (f ≫ chi) z = q u v (⊥ : PrimeSpectrum ℚ) := by
  let p := OriginalLiteralContactQuotientPoint318.openPoint u v hne
  let i := (sourceToCanonical e).hom
  letI := (ContactKummerCover318.flat_surjective c).2
  obtain ⟨a,ha⟩ := (ContactKummerCover318.structureMap c).surjective (p (⊥ : PrimeSpectrum ℚ))
  obtain ⟨z,hz⟩ := f.surjective (j (i a))
  have w : i ≫ j ≫ chi = ContactKummerCover318.structureMap c ≫
      ContactProjectiveModel318.baseOpen := by
    rw [hj, ← Category.assoc]
    exact congrArg (fun k : ContactKummerCover318.cover c ⟶ ContactKummerCover318.base =>
      k ≫ ContactProjectiveModel318.baseOpen) (sourceToCanonical_over e)
  have hw := congrArg (fun k : ContactKummerCover318.cover c ⟶ P => k a) w
  have hq := congrArg (fun k : Spec (CommRingCat.of ℚ) ⟶ P => k (⊥ : PrimeSpectrum ℚ))
    (OriginalLiteralContactQuotientPoint318.openPoint_is_original u v hne)
  simp only [Scheme.Hom.comp_apply] at hw hq
  rw [ha] at hw
  rw [Scheme.Hom.comp_apply, hz]
  exact hw.trans hq

end OriginalCanonicalContactOpenRecognition318

#print axioms OriginalCanonicalContactOpenRecognition318.orderEquiv
#print axioms OriginalCanonicalContactOpenRecognition318.orderEquiv_read
#print axioms OriginalCanonicalContactOpenRecognition318.orderEquiv_unique
#print axioms OriginalCanonicalContactOpenRecognition318.sourceToCanonical_over
#print axioms OriginalCanonicalContactOpenRecognition318.fine_point_over_original
