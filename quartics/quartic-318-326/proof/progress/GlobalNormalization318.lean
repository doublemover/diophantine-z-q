module
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import LocalizedNormalModel318
public section
noncomputable section
namespace GlobalNormalization318
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {X Y:Scheme.{u}} (f:X⟶Y) [QuasiCompact f] [QuasiSeparated f]
  {ι:Type v} (U:ι→Y.affineOpens)
  (hcover:⨆i,(U i).1=⊤)

include hcover

/-- Actual global relative normalization is finite when its actual affine
integral-closure pieces are finite. The scheme and gluing are Mathlib's real
normalization, not a parallel collection of affine rings. -/
theorem finite_of_affine_pieces
    (hfinite:∀i,letI:=(f.app (U i).1).hom.toAlgebra;
      Module.Finite Γ(Y,(U i).1) (integralClosure Γ(Y,(U i).1) Γ(X,f⁻¹ᵁ(U i).1))) :
    IsFinite f.fromNormalization := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P:=@IsFinite) _ hcover]
  intro i
  let V:=U i
  let e:=IsOpenImmersion.isoOfRangeEq (f.fromNormalization⁻¹ᵁV).ι
    (f.normalizationOpenCover.f V)
    (by simpa using congr($(f.fromNormalization_preimage V).1))
  rw [←MorphismProperty.cancel_left_of_respectsIso @IsFinite e.inv,
    ←MorphismProperty.cancel_right_of_respectsIso @IsFinite _ V.2.isoSpec.hom]
  have hf:(f.normalizationDiagramMap.app (.op V)).hom.Finite:=by
    letI:=(f.app V).hom.toAlgebra
    change (algebraMap Γ(Y,V) (integralClosure Γ(Y,V) Γ(X,f⁻¹ᵁV))).Finite
    exact RingHom.finite_algebraMap.mpr (hfinite i)
  convert! (IsFinite.SpecMap_iff _).mpr hf
  rw [←cancel_mono V.2.fromSpec]
  simp [IsAffineOpen.isoSpec_hom,e,V,Scheme.Hom.ι_fromNormalization] <;> rfl

/-- The actual global factorization map is proper over the actual target. -/
theorem proper_of_affine_pieces
    (hfinite:∀i,letI:=(f.app (U i).1).hom.toAlgebra;
      Module.Finite Γ(Y,(U i).1) (integralClosure Γ(Y,(U i).1) Γ(X,f⁻¹ᵁ(U i).1))) :
    IsProper f.fromNormalization := by
  letI:=finite_of_affine_pieces f U hcover hfinite
  infer_instance

end GlobalNormalization318

namespace GlobalNormalization318
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {X Y:Scheme.{u}} (f:X⟶Y) [QuasiCompact f] [QuasiSeparated f]
  {ι:Type v} (U:ι→Y.affineOpens) (hcover:⨆i,(U i).1=⊤)
  (Rf:ι→Type u) [∀i,CommRing (Rf i)]
  [∀i,IsDomain Γ(Y,(U i).1)] [∀i,CharZero Γ(Y,(U i).1)]
  [∀i,IsNoetherianRing Γ(Y,(U i).1)] [∀i,IsIntegrallyClosed Γ(Y,(U i).1)]
  [∀i,Algebra Γ(Y,(U i).1) (Rf i)]
  [∀i,IsDomain Γ(X,f⁻¹ᵁ(U i).1)]
  [∀i,Algebra (Rf i) Γ(X,f⁻¹ᵁ(U i).1)]
  [∀i,Algebra.Smooth (Rf i) Γ(X,f⁻¹ᵁ(U i).1)]
  [∀i,Module.Finite (Rf i) Γ(X,f⁻¹ᵁ(U i).1)]
  (d:∀i,Γ(Y,(U i).1)) [∀i,IsLocalization.Away (d i) (Rf i)]
  (hd:∀i,d i≠0)
  (htower:∀i,letI:=(f.app (U i).1).hom.toAlgebra;
    IsScalarTower Γ(Y,(U i).1) (Rf i) Γ(X,f⁻¹ᵁ(U i).1))

include U hcover Rf d hd htower

/-- Actual global finiteness is derived from actual connected finite smooth
open algebras on an actual affine cover. No finite-integral-closure or final
global finite-morphism premise is supplied. -/
theorem finite_of_smooth_open_pieces : IsFinite f.fromNormalization := by
  apply finite_of_affine_pieces f U hcover
  intro i
  letI:=(f.app (U i).1).hom.toAlgebra
  letI:=htower i
  exact (LocalizedNormalModel318.finite_normal_model (Rf:=Rf i)
    (B:=Γ(X,f⁻¹ᵁ(U i).1)) (d i) (hd i)).1

/-- If the actual target is proper over a base, its constructed global
normalization is genuinely proper over the same base. -/
theorem proper_over_base {S:Scheme.{u}} (g:Y⟶S) [IsProper g] :
    IsProper (f.fromNormalization≫g) := by
  letI:=finite_of_smooth_open_pieces f U hcover Rf d hd htower
  infer_instance

end GlobalNormalization318
