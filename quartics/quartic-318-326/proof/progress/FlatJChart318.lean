module
public import NormalJStalk318
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.Flat.TorsionFree
public section
noncomputable section
namespace FlatJChart318
open CategoryTheory AlgebraicGeometry Opposite
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

/-- Every actual affine characteristic-zero integral scheme is flat over Z. -/
theorem affine_flat (X:Scheme) [IsAffine X] [IsDomain Γ(X,⊤)] [CharZero Γ(X,⊤)]
    (f:X⟶Spec (CommRingCat.of ℤ)) : Flat f := by
  apply (MorphismProperty.cancel_left_of_respectsIso @Flat X.isoSpec.inv f).mp
  rw [←Scheme.Spec.map_preimage (X.isoSpec.inv≫f)]
  change Flat (Spec.map (Scheme.Spec.preimage (X.isoSpec.inv≫f)).unop)
  apply Flat.SpecMap_iff.mpr
  have he : (Scheme.Spec.preimage (X.isoSpec.inv≫f)).unop.hom=
      algebraMap ℤ Γ(X,⊤):=Subsingleton.elim _ _
  rw [he]
  rw [RingHom.flat_algebraMap_iff]
  infer_instance

variable (N:ℕ) (B:Type) [CommRing B] [IsDomain B]
  [Algebra (OpenJModel318.Base N) B] [Module.Finite (OpenJModel318.Base N) B]
  [Algebra.Etale (OpenJModel318.Base N) B]

theorem cover_charZero (hN:N≠0) : CharZero B := by
  let R:=OpenJModel318.Base N
  have hd:=OpenJNormalModel318.denominator_ne_zero N hN
  letI:IsDomain R:=IsLocalization.Away.isDomain R hd
  letI:CharZero R:=charZero_of_injective_algebraMap
    (IsLocalization.injective (M:=Submonoid.powers (OpenJModel318.denominator N)) R
      (by rintro x ⟨n,rfl⟩; exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n hd)))
  exact Algebra.charZero_of_charZero R B

section Generic
variable {A C:CommRingCat} {Y:Scheme} (φ:A⟶C) (c:Spec A⟶Y) [IsOpenImmersion c]
  [QuasiCompact (Spec.map φ≫c)] [QuasiSeparated (Spec.map φ≫c)] [CharZero C]

theorem chart_charZero_of_factor
    (f:Spec C⟶Y) [QuasiCompact f] [QuasiSeparated f] (hf:f=Spec.map φ≫c) :
    CharZero Γ(f.normalization,f.fromNormalization⁻¹ᵁ(c ''ᵁ ⊤)) := by
  subst f
  letI:=φ.hom.toAlgebra
  exact ((integralClosure A C).val.toRingHom.comp
    (NormalChart318.sectionsEquiv φ c).toRingHom).charZero
end Generic

theorem chart_charZero (hN:N≠0) (j:Fin 2) :
    CharZero (NormalJModel318.chartRing N B j) := by
  letI:=cover_charZero N B hN
  fin_cases j
  · exact chart_charZero_of_factor
      (CommRingCat.ofHom (ReciprocalCover318.polynomialMap N B)) (JLineAtlas318.chart ℤ 0)
      (OpenJProjectiveMap318.coverMap N B) (ReciprocalProjective318.coverMap_infinity N B)
  · exact chart_charZero_of_factor
      (CommRingCat.ofHom (ProperOpenJNormalization318.finitePolynomial N B))
      (JLineAtlas318.chart ℤ 1) (OpenJProjectiveMap318.coverMap N B)
      (ProperOpenJNormalization318.finite_factor N B)

/-- Flatness of the actual proper global normalization over Z, derived from
its concrete normal characteristic-zero domain charts. -/
theorem model_flat (hN:N≠0) :
    Flat ((OpenJProjectiveMap318.coverMap N B).fromNormalization≫
      ProjectiveJLine318.structureMap ℤ) := by
  apply IsZariskiLocalAtSource.of_iSup_eq_top
    (fun j=>(NormalJModel318.sourceCover N B j).1) (NormalJModel318.sourceCover_covers N B)
  intro j
  let U:=NormalJModel318.sourceCover N B j
  letI:IsAffine U.1:=U.2
  letI:IsDomain Γ((OpenJProjectiveMap318.coverMap N B).normalization,U):=
    (NormalJModel318.chart_properties N B hN j).1
  letI:CharZero Γ((OpenJProjectiveMap318.coverMap N B).normalization,U):=chart_charZero N B hN j
  let e:Γ(U.1,⊤) ≃+* Γ((OpenJProjectiveMap318.coverMap N B).normalization,U):=
    (Scheme.restrictFunctorΓ.app (op U.1)).commRingCatIsoToRingEquiv
  letI:IsDomain Γ(U.1,⊤):=MulEquiv.isDomain _ e.toMulEquiv
  letI:CharZero Γ(U.1,⊤):=e.toRingHom.charZero
  exact affine_flat U.1 _

end FlatJChart318
