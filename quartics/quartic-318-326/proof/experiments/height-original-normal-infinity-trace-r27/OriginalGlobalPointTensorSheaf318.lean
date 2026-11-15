module
public import OriginalArithmeticTensorFiber318
public import TildePullback318
public import PullbackPathComposition318
public section
noncomputable section
namespace OriginalGlobalPointTensorSheaf318
open NumberField OriginalPointFinitePlaceRoots318 AlgebraicGeometry CategoryTheory
open OriginalArchimedeanCotangentFiber318
variable (c : Fin 4 → ℚˣ) (t : ℚ)
    (hn : ∀ i,RationalContactPoint318.parameters c t i≠0) (i : Fin 4)
local notation "T" => ContactGlobalBicanonical318.tensor c
local notation "j" => ContactIntrinsicFrames318.branchEmbedding c i
local notation "q" => ContactBranchPoint318.branchMap c t hn i
local notation "p" => RationalContactPoint318.point c t

/-- Actual restriction of the ORIGINAL global intrinsic tensor sheaf is
identified with tilde of its entire algebraic cotangent tensor square.
The isomorphism uses the existing normalized universal-coordinate frame,
not a new rank-one assertion. -/
@[expose] def chartIso : T.restrict j ≅
    tilde (R:=CommRingCat.of (A c i))
      (ModuleCat.of (A c i) (OriginalArithmeticTensorFiber318.square c i)) :=
  IntrinsicTensorGenerator318.frame j (ContactIntrinsicDifferentials318.structureMap c)
    (ContactIntrinsicFrames318.branch_structure c i)
    (ContactDifferentialFrames318.sourceLocalizationFrame c i) ≪≫
      (tildeSelf (R:=CommRingCat.of (A c i))).symm ≪≫
        (tilde.functor (CommRingCat.of (A c i))).mapIso
          (OriginalArchimedeanComplexFiber318.squareFrame c i).toModuleIso.symm

/-- Pullback of the original proper-curve tensor sheaf at the SINGLE
original whole Spec(K)-valued point. This object has no branch index. -/
@[expose] def pointSheaf := (Scheme.Modules.pullback p).obj T

/-- Genuine sheaf isomorphism between the whole-point pullback and tilde
of the exact arithmetic fiber used by the finite lattices. Actual branch
factorization, pullback composition, open restriction/pullback comparison
and the canonical affine scalar-extension adjunction are all retained. -/
@[expose] def pointIso : pointSheaf c t ≅
    tilde (R:=CommRingCat.of (K c t))
      (ModuleCat.of (K c t) (OriginalArithmeticTensorFiber318.fiber c t hn i)) :=
  ((PullbackPathComposition318.iso q j p (ContactBranchPoint318.branchMap_original c t hn i)).app T).symm ≪≫
    (Scheme.Modules.pullback q).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback j).app T).symm ≪≫
        (Scheme.Modules.pullback q).mapIso (chartIso c i) ≪≫
          (TildePullback318.pullbackIso
            (CommRingCat.ofHom (OriginalArithmeticTensorFiber318.point c t hn i))).app
              (ModuleCat.of (A c i) (OriginalArithmeticTensorFiber318.square c i))

/-- Actual comparison between any two branch scalar-fiber sheaves,
through the SAME original point pullback, not by choosing vector spaces
of matching dimension. Coefficient and section normalizations are kept
as separate statements; no global arithmetic model is inferred. -/
@[expose] def branchIso (k : Fin 4) :
    tilde (R:=CommRingCat.of (K c t))
      (ModuleCat.of (K c t) (OriginalArithmeticTensorFiber318.fiber c t hn i)) ≅
    tilde (R:=CommRingCat.of (K c t))
      (ModuleCat.of (K c t) (OriginalArithmeticTensorFiber318.fiber c t hn k)) :=
  (pointIso c t hn i).symm ≪≫ pointIso c t hn k

lemma branchIso_cocycle (k l : Fin 4) :
    branchIso c t hn i k ≪≫ branchIso c t hn k l=branchIso c t hn i l := by
  apply Iso.ext
  simp only [branchIso,Iso.trans_hom,Iso.symm_hom,Category.assoc,Iso.hom_inv_id_assoc]
end OriginalGlobalPointTensorSheaf318
