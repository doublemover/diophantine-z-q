module
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import GlobalNormalization318
public section
noncomputable section
namespace GlobalOpenNormalization318
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
universe u v

/-- An actual affine restriction is locally quasi-finite when its actual
section-ring map is quasi-finite. -/
theorem quasiFinite_restrict {X Y:Scheme.{u}} (f:X⟶Y) (U:Y.Opens)
    (hU:IsAffineOpen U) (hV:IsAffineOpen (f⁻¹ᵁU))
    (h:(f.app U).hom.QuasiFinite) : LocallyQuasiFinite (f ∣_ U) := by
  letI : IsAffine (U : Scheme) := hU
  letI : IsAffine ((f⁻¹ᵁU) : Scheme) := hV
  rw [HasRingHomProperty.iff_of_isAffine (P:=@LocallyQuasiFinite)]
  letI : (RingHom.toMorphismProperty RingHom.QuasiFinite).RespectsIso :=
    RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.QuasiFinite.respectsIso
  simpa only [RingHom.toMorphismProperty, Scheme.Hom.resLE_eq_morphismRestrict] using
    (MorphismProperty.arrow_mk_iso_iff
    (RingHom.toMorphismProperty RingHom.QuasiFinite)
    (arrowResLEAppIso f U (f⁻¹ᵁU) le_rfl)).mpr (by simpa [RingHom.toMorphismProperty, Scheme.Hom.appLE] using h)

/-- The parallel actual finite-type restriction statement. -/
theorem finiteType_restrict {X Y:Scheme.{u}} (f:X⟶Y) (U:Y.Opens)
    (hU:IsAffineOpen U) (hV:IsAffineOpen (f⁻¹ᵁU))
    (h:(f.app U).hom.FiniteType) : LocallyOfFiniteType (f ∣_ U) := by
  letI : IsAffine (U : Scheme) := hU
  letI : IsAffine ((f⁻¹ᵁU) : Scheme) := hV
  rw [HasRingHomProperty.iff_of_isAffine (P:=@LocallyOfFiniteType)]
  letI : (RingHom.toMorphismProperty RingHom.FiniteType).RespectsIso :=
    RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.finiteType_respectsIso
  simpa only [RingHom.toMorphismProperty, Scheme.Hom.resLE_eq_morphismRestrict] using
    (MorphismProperty.arrow_mk_iso_iff
    (RingHom.toMorphismProperty RingHom.FiniteType)
    (arrowResLEAppIso f U (f⁻¹ᵁU) le_rfl)).mpr (by simpa [RingHom.toMorphismProperty, Scheme.Hom.appLE] using h)

variable {X Y:Scheme.{u}} (f:X⟶Y) [IsAffineHom f]
  {ι:Type v} (U:ι→Y.affineOpens) (hcover:⨆i,(U i).1=⊤)
  (Rf:ι→Type u) [∀i,CommRing (Rf i)]
  [∀i,Algebra Γ(Y,(U i).1) (Rf i)]
  [∀i,Algebra (Rf i) Γ(X,f⁻¹ᵁ(U i).1)]
  [∀i,Module.Finite (Rf i) Γ(X,f⁻¹ᵁ(U i).1)]
  (d:∀i,Γ(Y,(U i).1)) [∀i,IsLocalization.Away (d i) (Rf i)]
  (htower:∀i,letI:=(f.app (U i).1).hom.toAlgebra;
    IsScalarTower Γ(Y,(U i).1) (Rf i) Γ(X,f⁻¹ᵁ(U i).1))

include U hcover Rf d htower

/-- Genuine finite algebras over denominator opens give a locally
quasi-finite actual scheme map, not an assumed finite-fiber statement. -/
theorem locally_quasiFinite : LocallyQuasiFinite f := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P:=@LocallyQuasiFinite) _ hcover]
  intro i
  apply quasiFinite_restrict f (U i).1 (U i).2 ((U i).2.preimage f)
  letI:=(f.app (U i).1).hom.toAlgebra
  letI:=htower i
  letI : Algebra.QuasiFinite Γ(Y,(U i).1) (Rf i) :=
    Algebra.QuasiFinite.of_isLocalization (Submonoid.powers (d i))
  letI := Algebra.QuasiFinite.trans Γ(Y,(U i).1) (Rf i) Γ(X,f⁻¹ᵁ(U i).1)
  exact RingHom.quasiFinite_algebraMap.mpr inferInstance

/-- The same actual open-algebra data imply local finite type. -/
theorem locally_finiteType : LocallyOfFiniteType f := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P:=@LocallyOfFiniteType) _ hcover]
  intro i
  apply finiteType_restrict f (U i).1 (U i).2 ((U i).2.preimage f)
  letI:=(f.app (U i).1).hom.toAlgebra
  letI:=htower i
  letI:=IsLocalization.Away.finitePresentation (d i) (S:=Rf i)
  letI : Algebra.FiniteType Γ(Y,(U i).1) Γ(X,f⁻¹ᵁ(U i).1) :=
    Algebra.FiniteType.trans (S:=Rf i) inferInstance inferInstance
  exact RingHom.finiteType_algebraMap.mpr inferInstance

/-- Mathlib's proved Zariski main theorem identifies the actual source as
an actual open subscheme of its constructed global normalization. -/
theorem toNormalization_open : IsOpenImmersion f.toNormalization := by
  letI:=locally_quasiFinite f U hcover Rf d htower
  letI:=locally_finiteType f U hcover Rf d htower
  infer_instance

end GlobalOpenNormalization318
