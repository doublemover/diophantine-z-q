module
public import OriginalTensorScalarNormalization318
public import OriginalFramePullbackUnits318
public section
noncomputable section
namespace OriginalModulePullbackScalar318
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
/-- The same actual global regular function, transported through the
native whole-open section map, acts on the actual pushforward module. -/
lemma pushforward (N : X.Modules) (a : Γ(Y,⊤)) :
    ModuleScalar318.map ((Scheme.Modules.pushforward f).obj N) a=
      (Scheme.Modules.pushforward f).map (ModuleScalar318.map N (f.appTop a)) := by
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  change (f.app U (Y.presheaf.map (homOfLE (show U≤⊤ from le_top)).op a)) • s=
    (X.presheaf.map (homOfLE (show f ⁻¹ᵁ U≤⊤ from le_top)).op (f.appTop a)) • s
  have h := congrArg (fun q => q a) (f.naturality (homOfLE (show U≤⊤ from le_top)).op)
  exact congrArg (fun r : Γ(X,f ⁻¹ᵁ U) => r • s) h
/-- Actual module pullback sends scalar multiplication to multiplication
by the actual pulled regular function. This applies to every module,
without a line frame, flatness or global-section generation hypothesis. -/
lemma pullback (M : Y.Modules) (a : Γ(Y,⊤)) :
    (Scheme.Modules.pullback f).map (ModuleScalar318.map M a)=
      ModuleScalar318.map ((Scheme.Modules.pullback f).obj M) (f.appTop a) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit,Adjunction.homEquiv_unit]
  have hn := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality
    (ModuleScalar318.map M a)
  change ModuleScalar318.map M a ≫ (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M=
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M ≫
      (Scheme.Modules.pushforward f).map ((Scheme.Modules.pullback f).map (ModuleScalar318.map M a)) at hn
  rw [←hn,←pushforward]
  exact ModuleScalar318.natural a ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
lemma unitIso (M : Y.Modules) (a : Γ(Y,⊤)ˣ) :
    (Scheme.Modules.pullback f).mapIso (ModuleScalarComposition318.unitIso M a)=
      ModuleScalarComposition318.unitIso ((Scheme.Modules.pullback f).obj M)
        (OriginalFramePullbackUnits318.units f a) := by
  apply Iso.ext
  exact pullback f M (a:Γ(Y,⊤))
end OriginalModulePullbackScalar318
