module
public import NormalizedWholeIntrinsicTensor318
public import TildeFramedTop318
public section
noncomputable section
namespace NormalizedWholeTensorSections318
open AlgebraicGeometry CategoryTheory
open NormalizedWholeGluing318 NormalizedWholeOpenMaps318 NormalizedWholeOverlap318
open NormalizedDualBicanonicalSections318 FiniteDualTransport318
universe u
variable (R : Type u) [CommRing R] (d a : Fin 4 → R)
local notation "L" => NormalizedWholeDualitySheaf318.line R d a
local notation "T" => IntrinsicTensorSheaf318.tensor L L
local notation "B" => NormalizedWholeBicanonicalSheaf318.line R d a

@[expose] def finiteFrame : T.restrict (finiteChart R d a) ≅
    SheafOfModules.unit (finiteScheme R d a).ringCatSheaf :=
  (Scheme.Modules.restrictFunctor (finiteChart R d a)).mapIso
    (NormalizedWholeIntrinsicTensor318.iso R d a) ≪≫
      NormalizedWholeBicanonicalSheaf318.finiteFrame R d a
@[expose] def infinityFrame : T.restrict (infinityChart R d a) ≅
    SheafOfModules.unit (infinityScheme R d a).ringCatSheaf :=
  (Scheme.Modules.restrictFunctor (infinityChart R d a)).mapIso
    (NormalizedWholeIntrinsicTensor318.iso R d a) ≪≫
      NormalizedWholeBicanonicalSheaf318.infinityFrame R d a

/-- Genuine tilde comparisons with the actual ENTIRE balanced finite-dual
tensor modules on the two whole model charts. -/
@[expose] def finiteDualSquareIso : T.restrict (finiteChart R d a) ≅
    tilde (R:=CommRingCat.of (FiniteOrder R d a)) (ModuleCat.of (FiniteOrder R d a)
      (Square (R:=R[X]) (A:=FiniteOrder R d a))) :=
  (Scheme.Modules.restrictFunctor (finiteChart R d a)).mapIso
    (NormalizedWholeIntrinsicTensor318.iso R d a) ≪≫
      NormalizedWholeBicanonicalSheaf318.finiteDualSquareIso R d a
@[expose] def infinityDualSquareIso : T.restrict (infinityChart R d a) ≅
    tilde (R:=CommRingCat.of (InfinityOrder R d a)) (ModuleCat.of (InfinityOrder R d a)
      (Square (R:=R[X]) (A:=InfinityOrder R d a))) :=
  (Scheme.Modules.restrictFunctor (infinityChart R d a)).mapIso
    (NormalizedWholeIntrinsicTensor318.iso R d a) ≪≫
      NormalizedWholeBicanonicalSheaf318.infinityDualSquareIso R d a

lemma finite_coefficient (s : Γ(T,⊤)) :
    (finiteFrame R d a).hom.app ⊤
      (T.presheaf.map (homOfLE (show finiteChart R d a ''ᵁ ⊤≤⊤ from le_top)).op s) =
    (NormalizedWholeBicanonicalSheaf318.finiteFrame R d a).hom.app ⊤
      (B.presheaf.map (homOfLE (show finiteChart R d a ''ᵁ ⊤≤⊤ from le_top)).op
        ((NormalizedWholeIntrinsicTensor318.iso R d a).hom.app ⊤ s)) := by
  have h := congrArg (fun f => f s)
    ((NormalizedWholeIntrinsicTensor318.iso R d a).hom.mapPresheaf.naturality
      (homOfLE (show finiteChart R d a ''ᵁ ⊤≤⊤ from le_top)).op)
  exact congrArg ((NormalizedWholeBicanonicalSheaf318.finiteFrame R d a).hom.app ⊤) h
lemma infinity_coefficient (s : Γ(T,⊤)) :
    (infinityFrame R d a).hom.app ⊤
      (T.presheaf.map (homOfLE (show infinityChart R d a ''ᵁ ⊤≤⊤ from le_top)).op s) =
    (NormalizedWholeBicanonicalSheaf318.infinityFrame R d a).hom.app ⊤
      (B.presheaf.map (homOfLE (show infinityChart R d a ''ᵁ ⊤≤⊤ from le_top)).op
        ((NormalizedWholeIntrinsicTensor318.iso R d a).hom.app ⊤ s)) := by
  have h := congrArg (fun f => f s)
    ((NormalizedWholeIntrinsicTensor318.iso R d a).hom.mapPresheaf.naturality
      (homOfLE (show infinityChart R d a ''ᵁ ⊤≤⊤ from le_top)).op)
  exact congrArg ((NormalizedWholeBicanonicalSheaf318.infinityFrame R d a).hom.app ⊤) h

/-- Actual restriction, exact affine scalar comparison and the original
whole dual-square frame, defined on EVERY global tensor section. -/
@[expose] def finiteTensor (s : Γ(T,⊤)) : Square (R:=R[X]) (A:=FiniteOrder R d a) :=
  squareFrame (FourRootIntegralDuality318.frame (DVRNormalizedFiniteOrder318.coefficient R d a))
    ((Scheme.ΓSpecIso (CommRingCat.of (FiniteOrder R d a))).hom
      ((finiteFrame R d a).hom.app ⊤
        (T.presheaf.map (homOfLE (show finiteChart R d a ''ᵁ ⊤≤⊤ from le_top)).op s)))
@[expose] def infinityTensor (s : Γ(T,⊤)) : Square (R:=R[X]) (A:=InfinityOrder R d a) :=
  squareFrame (FourRootIntegralDuality318.frame (DVRNormalizedInfinityOrder318.coefficient R d a))
    ((Scheme.ΓSpecIso (CommRingCat.of (InfinityOrder R d a))).hom
      ((infinityFrame R d a).hom.app ⊤
        (T.presheaf.map (homOfLE (show infinityChart R d a ''ᵁ ⊤≤⊤ from le_top)).op s)))

/-- These coordinate formulas are literally evaluation of the previously
constructed whole tilde-module comparison, followed by its canonical
inverse top-section map. No surrogate coefficient section is substituted. -/
lemma finiteTensor_tilde (s : Γ(T,⊤)) :
    (tilde.isoTop (R:=CommRingCat.of (FiniteOrder R d a))
      (ModuleCat.of (FiniteOrder R d a) (Square (R:=R[X]) (A:=FiniteOrder R d a)))).inv
      ((finiteDualSquareIso R d a).hom.app ⊤
        (T.presheaf.map (homOfLE (show finiteChart R d a ''ᵁ ⊤≤⊤ from le_top)).op s)) =
      finiteTensor R d a s :=
  TildeFramedTop318.frame_section _ _ _ _
lemma infinityTensor_tilde (s : Γ(T,⊤)) :
    (tilde.isoTop (R:=CommRingCat.of (InfinityOrder R d a))
      (ModuleCat.of (InfinityOrder R d a) (Square (R:=R[X]) (A:=InfinityOrder R d a)))).inv
      ((infinityDualSquareIso R d a).hom.app ⊤
        (T.presheaf.map (homOfLE (show infinityChart R d a ''ᵁ ⊤≤⊤ from le_top)).op s)) =
      infinityTensor R d a s :=
  TildeFramedTop318.frame_section _ _ _ _

lemma section0_finite : finiteTensor R d a (NormalizedWholeIntrinsicTensor318.section0 R d a) =
    finiteSection R d a (finite0 R d) := by
  rw [finiteTensor,finite_coefficient,NormalizedWholeIntrinsicTensor318.section0_image,
    NormalizedWholeBicanonicalSheaf318.section0_finite]
  exact congrArg _ (Iso.inv_hom_id_apply _ _)
lemma section1_finite : finiteTensor R d a (NormalizedWholeIntrinsicTensor318.section1 R d a) =
    finiteSection R d a (finite1 R d) := by
  rw [finiteTensor,finite_coefficient,NormalizedWholeIntrinsicTensor318.section1_image,
    NormalizedWholeBicanonicalSheaf318.section1_finite]
  exact congrArg _ (Iso.inv_hom_id_apply _ _)
lemma section0_infinity : infinityTensor R d a (NormalizedWholeIntrinsicTensor318.section0 R d a) =
    infinitySection R d a (infinity0 R d) := by
  rw [infinityTensor,infinity_coefficient,NormalizedWholeIntrinsicTensor318.section0_image,
    NormalizedWholeBicanonicalSheaf318.section0_infinity]
  exact congrArg _ (Iso.inv_hom_id_apply _ _)
lemma section1_infinity : infinityTensor R d a (NormalizedWholeIntrinsicTensor318.section1 R d a) =
    infinitySection R d a (infinity1 R d) := by
  rw [infinityTensor,infinity_coefficient,NormalizedWholeIntrinsicTensor318.section1_image,
    NormalizedWholeBicanonicalSheaf318.section1_infinity]
  exact congrArg _ (Iso.inv_hom_id_apply _ _)
end NormalizedWholeTensorSections318
