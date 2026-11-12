module
public import ActualTwoDescentOriginalArbitraryLiftSectionBijection318
public section
noncomputable section
namespace ActualTwoDescentOriginalArbitraryLiftNativePullback318
open AlgebraicGeometry CategoryTheory
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalSchemeIntegral318
open ActualTwoDescentOriginalDoublePoleSheaf318 ActualTwoDescentOriginalDoublePoleRationalEmbedding318
open ActualTwoDescentOriginalDoublePoleLocalGlobal318 ActualTwoDescentOriginalFourGenericLatticeAction318
open ActualTwoDescentSemilinearLatticeLiftGroup318
variable {K : Type*} [Field K] [CharZero K]
open ActualTwoDescentOriginalArbitraryLiftOpenAction318 ActualTwoDescentOriginalArbitraryLiftAllOpenHom318
def pullbackMap (n : K) (hn : n≠0) (a : Lift (data n hn)) :
    (Scheme.Modules.pullback (translation n hn a).hom).obj (sheaf n) ⟶ sheaf n :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (translation n hn a).hom).homEquiv _ _).symm (hom n hn a)
lemma adjoint (n : K) (hn : n≠0) (a : Lift (data n hn)) :
    (Scheme.Modules.pullbackPushforwardAdjunction (translation n hn a).hom).homEquiv _ _
      (pullbackMap n hn a)=hom n hn a :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (translation n hn a).hom).homEquiv _ _).apply_symm_apply _
lemma counit_formula (n : K) (hn : n≠0) (a : Lift (data n hn)) :
    pullbackMap n hn a=(Scheme.Modules.pullback (translation n hn a).hom).map (hom n hn a) ≫
      (Scheme.Modules.pullbackPushforwardAdjunction (translation n hn a).hom).counit.app (sheaf n) :=
  (Scheme.Modules.pullbackPushforwardAdjunction (translation n hn a).hom).homEquiv_counit _
instance pullbackMap_isIso (n : K) (hn : n≠0) (a : Lift (data n hn)) : IsIso (pullbackMap n hn a) := by
  rw [counit_formula]
  infer_instance
def iso (n : K) (hn : n≠0) (a : Lift (data n hn)) :
    (Scheme.Modules.pullback (translation n hn a).hom).obj (sheaf n) ≅ sheaf n := asIso (pullbackMap n hn a)
lemma normalized_adjoint (n : K) (hn : n≠0) (a : Lift (data n hn))
    (U : (originalCubicScheme n).Opens) [Nonempty U] (s : Γ(sheaf n,U)) :
    value n (inverseOpen n hn a U)
      (((Scheme.Modules.pullbackPushforwardAdjunction (translation n hn a).hom).homEquiv _ _
        (iso n hn a).hom).app U s)=operator (data n hn) a (value n U s) := by
  change value n (inverseOpen n hn a U)
    (((Scheme.Modules.pullbackPushforwardAdjunction (translation n hn a).hom).homEquiv _ _
      (pullbackMap n hn a)).app U s)=_
  rw [adjoint,coefficient]
lemma unique (n : K) (hn : n≠0) (a : Lift (data n hn))
    (f : (Scheme.Modules.pullback (translation n hn a).hom).obj (sheaf n) ⟶ sheaf n)
    (hf : ∀ (U : (originalCubicScheme n).Opens) [Nonempty U] (s : Γ(sheaf n,U)),
      value n (inverseOpen n hn a U)
        (((Scheme.Modules.pullbackPushforwardAdjunction (translation n hn a).hom).homEquiv _ _ f).app U s)=
          operator (data n hn) a (value n U s)) : f=(iso n hn a).hom := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (translation n hn a).hom).homEquiv _ _).injective
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  classical
  by_cases hU : Nonempty U
  · letI := hU
    apply value_injective n (inverseOpen n hn a U)
    rw [hf,normalized_adjoint]
  · haveI := ActualTwoDescentEmptyModuleSections318.empty_sections_subsingleton (pushed n hn a) U hU
    exact Subsingleton.elim _ _

end ActualTwoDescentOriginalArbitraryLiftNativePullback318
