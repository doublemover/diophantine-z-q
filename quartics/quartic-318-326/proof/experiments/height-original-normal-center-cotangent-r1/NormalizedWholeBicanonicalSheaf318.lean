module
public import NormalizedWholeDualitySheaf318
public import NormalizedDualBicanonicalSections318
public import ClutchedModuleTop318
public import ClutchedCoordinateFrames318
public section
noncomputable section
namespace NormalizedWholeBicanonicalSheaf318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
open NormalizedReciprocalLaurent318 NormalizedWholeOverlap318 NormalizedWholeOpenMaps318
open NormalizedWholeGluing318 NormalizedWholeDualitySheaf318
open NormalizedDualBicanonicalSections318 FiniteDualTransport318
universe u
set_option maxHeartbeats 2400000
variable (R : Type u) [CommRing R] (d a : Fin 4 → R)
local notation "C" => CommonOrder R d a

@[expose] def overlapUnit : Cˣ := Units.map (algebraMap (Laurent R) C) ((coordinate R)^4)
@[expose] def sectionUnit : Γ(overlap R d a,⊤)ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (overlapUnit R d a)

/-- The actual squared transition, with both sides in the SAME original
whole-overlap section ring. A global tensor comparison is not assumed. -/
theorem transition_square : (NormalizedWholeDualitySheaf318.sectionUnit R d a).val^2=
    (sectionUnit R d a).val := by
  change ((Scheme.ΓSpecIso (CommRingCat.of C)).inv
    (algebraMap (Laurent R) C (-((coordinate R:Laurent R)^2))))^2=
      (Scheme.ΓSpecIso (CommRingCat.of C)).inv
        (algebraMap (Laurent R) C ((coordinate R:Laurent R)^4))
  rw [←map_pow,←map_pow]
  congr 2
  ring

/-- Genuine global module sheaf for the proved squared transition. Its
identification with the intrinsic sheaf tensor square is a separate comparison. -/
@[expose] def line : (scheme R d a).Modules :=
  ClutchedModule318.sheaf (finiteChart R d a) (infinityChart R d a)
    (intoFinite R d a) (intoInfinity R d a) (gluing_square R d a) (sectionUnit R d a).val
@[expose] def finiteFrame : (line R d a).restrict (finiteChart R d a) ≅
    SheafOfModules.unit (finiteScheme R d a).ringCatSheaf :=
  ClutchedModuleFrames318.firstFrame _ _ _ _ (gluing_square R d a) _
    (sectionUnit R d a).isUnit (infinity_range R d a)
@[expose] def infinityFrame : (line R d a).restrict (infinityChart R d a) ≅
    SheafOfModules.unit (infinityScheme R d a).ringCatSheaf :=
  ClutchedModuleFrames318.secondFrame _ _ _ _ (gluing_square R d a) _ (finite_range R d a)

@[expose] def finiteDualSquareIso : (line R d a).restrict (finiteChart R d a) ≅
    tilde (R:=CommRingCat.of (FiniteOrder R d a)) (ModuleCat.of (FiniteOrder R d a)
      (Square (R:=R[X]) (A:=FiniteOrder R d a))) :=
  finiteFrame R d a ≪≫ tildeSelf.symm ≪≫
    (tilde.functor (CommRingCat.of (FiniteOrder R d a))).mapIso
      (squareFrame (FourRootIntegralDuality318.frame (DVRNormalizedFiniteOrder318.coefficient R d a))).toModuleIso
@[expose] def infinityDualSquareIso : (line R d a).restrict (infinityChart R d a) ≅
    tilde (R:=CommRingCat.of (InfinityOrder R d a)) (ModuleCat.of (InfinityOrder R d a)
      (Square (R:=R[X]) (A:=InfinityOrder R d a))) :=
  infinityFrame R d a ≪≫ tildeSelf.symm ≪≫
    (tilde.functor (CommRingCat.of (InfinityOrder R d a))).mapIso
      (squareFrame (FourRootIntegralDuality318.frame (DVRNormalizedInfinityOrder318.coefficient R d a))).toModuleIso

@[expose] def openFrame (i : ULift.{u} Bool) :
    SheafOfModules.free (R:=(NormalizedWholeDualitySheaf318.cover R d a i).toScheme.ringCatSheaf) PUnit.{u+1} ≅
      (line R d a).restrict (NormalizedWholeDualitySheaf318.cover R d a i).ι := by
  rcases i with ⟨i⟩
  cases i
  · exact OpenClutchedLocallyFree318.freeUnit _ ≪≫
      ActualOpenImmersionLineFrame318.ambientFrame (finiteChart R d a) (line R d a) (finiteFrame R d a).symm
  · exact OpenClutchedLocallyFree318.freeUnit _ ≪≫
      ActualOpenImmersionLineFrame318.ambientFrame (infinityChart R d a) (line R d a) (infinityFrame R d a).symm

theorem locallyFree : (line R d a).IsLocallyFree :=
  ModuleFreeOpenFrames318.locallyFree (line R d a) PUnit.{u+1}
    (NormalizedWholeDualitySheaf318.cover R d a)
    (OpenClutchedLocallyFree318.cover_top _ _ (cover_top R d a)) (openFrame R d a)

lemma finiteMap_polynomial (p : R[X]) : finiteMap R d a (algebraMap R[X] (FiniteOrder R d a) p)=
    algebraMap (Laurent R) C (algebraMap R[X] (Laurent R) p) := by
  change FourRootSignBaseChange318.coefficientMap
    (DVRNormalizedFiniteOrder318.coefficient R d a) (Laurent R) (algebraMap R[X] _ p)=_
  rw [AlgHom.commutes,IsScalarTower.algebraMap_apply R[X] (Laurent R)]
lemma infinityMap_polynomial (p : R[X]) : infinityMap R d a (algebraMap R[X] (InfinityOrder R d a) p)=
    algebraMap (Laurent R) C (reciprocalMap R p) := by
  letI : Algebra R[X] (Laurent R) := (reciprocalMap R).toRingHom.toAlgebra
  change (fullOverlap R d a).symm
    (FourRootSignBaseChange318.coefficientMap (DVRNormalizedInfinityOrder318.coefficient R d a)
      (Laurent R) (algebraMap R[X] _ p))=_
  rw [AlgHom.commutes,IsScalarTower.algebraMap_apply R[X] (Laurent R),AlgEquiv.commutes] <;> rfl

@[expose] def finiteSectionValue (p : R[X]) : Γ(finiteScheme R d a,⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (FiniteOrder R d a))).inv
    (algebraMap R[X] (FiniteOrder R d a) p)
@[expose] def infinitySectionValue (p : R[X]) : Γ(infinityScheme R d a,⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (InfinityOrder R d a))).inv
    (algebraMap R[X] (InfinityOrder R d a) p)

lemma finite_restrict (p : R[X]) : (intoFinite R d a).appTop (finiteSectionValue R d a p)=
    (Scheme.ΓSpecIso (CommRingCat.of C)).inv
      (algebraMap (Laurent R) C (algebraMap R[X] (Laurent R) p)) := by
  have h := congrArg (fun f => f (algebraMap R[X] (FiniteOrder R d a) p))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (finiteMap R d a)))
  simp only [CommRingCat.comp_apply,CommRingCat.ofHom_apply] at h
  change (Scheme.ΓSpecIso (CommRingCat.of C)).inv
    (finiteMap R d a (algebraMap R[X] (FiniteOrder R d a) p))=
      (intoFinite R d a).appTop (finiteSectionValue R d a p) at h
  rw [finiteMap_polynomial] at h
  exact h.symm
lemma infinity_restrict (p : R[X]) : (intoInfinity R d a).appTop (infinitySectionValue R d a p)=
    (Scheme.ΓSpecIso (CommRingCat.of C)).inv
      (algebraMap (Laurent R) C (reciprocalMap R p)) := by
  have h := congrArg (fun f => f (algebraMap R[X] (InfinityOrder R d a) p))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (infinityMap R d a)))
  simp only [CommRingCat.comp_apply,CommRingCat.ofHom_apply] at h
  change (Scheme.ΓSpecIso (CommRingCat.of C)).inv
    (infinityMap R d a (algebraMap R[X] (InfinityOrder R d a) p))=
      (intoInfinity R d a).appTop (infinitySectionValue R d a p) at h
  rw [infinityMap_polynomial] at h
  exact h.symm

lemma compatible (p q : R[X])
    (hpq : algebraMap R[X] (Laurent R) p*(↑(coordinate R)⁻¹:Laurent R)^4=reciprocalMap R q) :
    (intoFinite R d a).appTop (finiteSectionValue R d a p)=
      (intoInfinity R d a).appTop (infinitySectionValue R d a q)*(sectionUnit R d a).val := by
  have h := congrArg (fun z : Laurent R => z*(coordinate R:Laurent R)^4) hpq
  rw [mul_assoc,←mul_pow,Units.inv_mul,one_pow,mul_one] at h
  rw [finite_restrict,infinity_restrict]
  change (Scheme.ΓSpecIso (CommRingCat.of C)).inv (algebraMap (Laurent R) C _)=
    (Scheme.ΓSpecIso (CommRingCat.of C)).inv (algebraMap (Laurent R) C _)*
    (Scheme.ΓSpecIso (CommRingCat.of C)).inv (algebraMap (Laurent R) C ((coordinate R:Laurent R)^4))
  rw [←map_mul,←map_mul,h]

/-- Actual global sections, constructed by the categorical sheaf pullback
universal property from the proven full-chart identities. -/
@[expose] def section0 : Γ(line R d a,⊤) :=
  ClutchedModuleTop318.sectionTop _ _ _ _ (gluing_square R d a) (sectionUnit R d a).val
    (finiteSectionValue R d a (finite0 R d)) (infinitySectionValue R d a (infinity0 R d))
      (compatible R d a _ _ (coefficient_overlap0 R d))
@[expose] def section1 : Γ(line R d a,⊤) :=
  ClutchedModuleTop318.sectionTop _ _ _ _ (gluing_square R d a) (sectionUnit R d a).val
    (finiteSectionValue R d a (finite1 R d)) (infinitySectionValue R d a (infinity1 R d))
      (compatible R d a _ _ (coefficient_overlap1 R d))

lemma section0_finite : (finiteFrame R d a).hom.app ⊤
    ((line R d a).presheaf.map (homOfLE (show finiteChart R d a ''ᵁ ⊤≤⊤ from le_top)).op
      (section0 R d a))=finiteSectionValue R d a (finite0 R d) :=
  ClutchedCoordinateFrames318.first_value _ _ _ _ (gluing_square R d a) (sectionUnit R d a).val
    _ _ (compatible R d a _ _ (coefficient_overlap0 R d)) (sectionUnit R d a).isUnit (infinity_range R d a)
lemma section0_infinity : (infinityFrame R d a).hom.app ⊤
    ((line R d a).presheaf.map (homOfLE (show infinityChart R d a ''ᵁ ⊤≤⊤ from le_top)).op
      (section0 R d a))=infinitySectionValue R d a (infinity0 R d) :=
  ClutchedCoordinateFrames318.second_value _ _ _ _ (gluing_square R d a) (sectionUnit R d a).val
    _ _ (compatible R d a _ _ (coefficient_overlap0 R d)) (finite_range R d a)
lemma section1_finite : (finiteFrame R d a).hom.app ⊤
    ((line R d a).presheaf.map (homOfLE (show finiteChart R d a ''ᵁ ⊤≤⊤ from le_top)).op
      (section1 R d a))=finiteSectionValue R d a (finite1 R d) :=
  ClutchedCoordinateFrames318.first_value _ _ _ _ (gluing_square R d a) (sectionUnit R d a).val
    _ _ (compatible R d a _ _ (coefficient_overlap1 R d)) (sectionUnit R d a).isUnit (infinity_range R d a)
lemma section1_infinity : (infinityFrame R d a).hom.app ⊤
    ((line R d a).presheaf.map (homOfLE (show infinityChart R d a ''ᵁ ⊤≤⊤ from le_top)).op
      (section1 R d a))=infinitySectionValue R d a (infinity1 R d) :=
  ClutchedCoordinateFrames318.second_value _ _ _ _ (gluing_square R d a) (sectionUnit R d a).val
    _ _ (compatible R d a _ _ (coefficient_overlap1 R d)) (finite_range R d a)
end NormalizedWholeBicanonicalSheaf318
