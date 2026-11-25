module
public import OriginalR47RetainedDenominatorSpread318
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public section
noncomputable section

namespace OriginalR47RetainedAffineSpread318

open AlgebraicGeometry CategoryTheory Set
open OriginalR47RetainedDenominatorSpread318 (canonical)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {R : Type u} [CommRing R] [IsDomain R]
local notation "B" => Spec (CommRingCat.of R)
variable {Y : Scheme.{u}}

abbrev toLocal (p : Ideal R) [p.IsPrime] (d : R) (hd : d ∉ p) :
    Spec (CommRingCat.of (Localization.AtPrime p)) ⟶ Spec (CommRingCat.of (Localization.Away d)) :=
  Spec.map (CommRingCat.ofHom (canonical p d hd).toRingHom)

/-- Spread the prescribed whole actual local section inside one true old
Y-affine chart and on one true principal neighbourhood in Spec R.
The essential finite type is the literal structural map of that old
chart. There are no quotients by rational-map germs, no auxiliary Y,
and no changed section. -/
theorem at_local (t : Y ⟶ B) [LocallyOfFiniteType t]
    (p : Ideal R) [p.IsPrime] (f : Spec (CommRingCat.of (Localization.AtPrime p)) ⟶ Y)
    (hf : f ≫ t = Spec.algebraMap R (Localization.AtPrime p)) :
    ∃ (d : R) (hd : d ∉ p) (F : Spec (CommRingCat.of (Localization.Away d)) ⟶ Y),
      toLocal p d hd ≫ F = f := by
  let Aₚ := Localization.AtPrime p
  let w : PrimeSpectrum Aₚ := IsLocalRing.closedPoint Aₚ
  obtain ⟨i,z,hz⟩ := Y.affineOpenCover.openCover.exists_eq (f w)
  let A := Y.affineOpenCover.X i
  let j : Spec A ⟶ Y := Y.affineOpenCover.f i
  let : IsOpenImmersion j := Y.affineOpenCover.map_prop i
  have hr : Set.range f ⊆ Set.range j := by
    rintro _ ⟨v,rfl⟩
    have hzw : f w ∈ Set.range j := ⟨z,hz⟩
    exact ((IsLocalRing.specializes_closedPoint v).map f.continuous).mem_open
      (IsOpenImmersion.isOpen_range j) hzw
  let f' := IsOpenImmersion.lift j f hr
  have hf' : f' ≫ j = f := IsOpenImmersion.lift_fac j f hr
  let c : CommRingCat.of R ⟶ A := Spec.preimage (j ≫ t)
  let a : A ⟶ CommRingCat.of Aₚ := Spec.preimage f'
  have hscalar : c ≫ a = CommRingCat.ofHom (algebraMap R Aₚ) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, ← Category.assoc, hf']
    exact hf
  let : Algebra R A := c.hom.toAlgebra
  let aR : A →ₐ[R] Aₚ := ⟨a.hom,fun r =>
    congrArg (fun g : CommRingCat.of R ⟶ CommRingCat.of Aₚ => g.hom r) hscalar⟩
  have hft : LocallyOfFiniteType (Spec.map c) :=
    (Spec.map_preimage (j ≫ t)).symm ▸ (inferInstance : LocallyOfFiniteType (j ≫ t))
  let : Algebra.FiniteType R A := RingHom.finiteType_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P:=@LocallyOfFiniteType)).mp hft)
  obtain ⟨d,hd,g,hg⟩ := OriginalR47RetainedDenominatorSpread318.spread p aR
  let b : A ⟶ CommRingCat.of (Localization.Away d) := CommRingCat.ofHom g.toRingHom
  refine ⟨d,hd,Spec.map b ≫ j,?_⟩
  have heb : b ≫ CommRingCat.ofHom (canonical p d hd).toRingHom = a := by
    ext r
    exact DFunLike.congr_fun hg r
  rw [toLocal,← Spec.map_comp_assoc,heb,Spec.map_preimage,hf']

end OriginalR47RetainedAffineSpread318

#print axioms OriginalR47RetainedAffineSpread318.at_local
