module
public import AffineLineFrameCover318
public import AffineModuleSectionEquiv318
public section
noncomputable section
namespace AffineLineSections318
open AlgebraicGeometry CategoryTheory TopologicalSpace
set_option maxHeartbeats 650000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}} (M:X.Modules) (U:X.Opens) (hU:IsAffineOpen U)
variable {κ:Type u} (V:κ→X.Opens) (hc:(⊤:X.Opens)≤⨆i,V i)
  (frames:∀i,SheafOfModules.unit ((V i):Scheme).ringCatSheaf≅M.restrict (V i).ι)
include hU hc frames in
/-- Genuine source line frames imply finite presentation, flatness and
rank one for the literal section module on any actual affine open. -/
lemma properties:Module.FinitePresentation Γ(X,U) Γ(M,U) ∧
    Module.Flat Γ(X,U) Γ(M,U) ∧
    ∀p:PrimeSpectrum Γ(X,U),Module.rankAtStalk Γ(M,U) p=1:=by
  obtain ⟨hp,hf,hr⟩:=AffineLineFrameCover318.properties Γ(X,U) (M.restrict hU.fromSpec)
    (fun i=>hU.fromSpec⁻¹ᵁV i) (OpenLineRestriction318.covers hU.fromSpec V hc)
    (fun i=>OpenLineRestriction318.frame hU.fromSpec M (V i) (frames i))
  letI:=hp
  letI:=hf
  let e:=AffineModuleSectionEquiv318.equiv M U hU
  refine ⟨Module.FinitePresentation.of_equiv e,Module.Flat.of_linearEquiv e.symm,?_⟩
  intro p
  have he:=congrArg (fun g=>g p) (Module.rankAtStalk_eq_of_equiv e)
  exact he.symm.trans (hr p)
end AffineLineSections318
