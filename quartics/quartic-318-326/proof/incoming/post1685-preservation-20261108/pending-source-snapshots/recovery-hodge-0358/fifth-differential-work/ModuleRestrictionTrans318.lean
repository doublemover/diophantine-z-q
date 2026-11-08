module
public import ScaledGlobalSectionRestriction318
public section
noncomputable section
namespace ModuleRestrictionTrans318
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {X:Scheme.{u}} (M:X.Modules) {U V:X.Opens} (h:V≤U)
    (s:Γ(M,⊤)) (u:Γ(M,U)) (v:Γ(M,V))
theorem top (hu:u=M.presheaf.map (homOfLE (show U≤⊤ from le_top)).op s)
    (hv:M.presheaf.map (homOfLE h).op u=v):
    M.presheaf.map (homOfLE (show V≤⊤ from le_top)).op s=v:=by
  have he:=congrArg (M.presheaf.map (homOfLE h).op) hu
  exact (CategoryTheory.Functor.map_comp_apply M.presheaf
    (homOfLE (show U≤⊤ from le_top)).op (homOfLE h).op s).trans (he.symm.trans hv)
end ModuleRestrictionTrans318
