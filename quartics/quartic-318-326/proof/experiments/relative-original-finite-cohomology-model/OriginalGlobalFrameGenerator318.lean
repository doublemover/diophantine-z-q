module
public import OpenLineFrameCoordinates318
public import SectionGeneratedGluing318
public section
noncomputable section
namespace OriginalGlobalFrameGenerator318
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
  (e : SheafOfModules.unit U.toScheme.ringCatSheaf ≅ M.restrict U.ι)
  (s : Γ(M,⊤))

/-- A specified original global section equal to the old frame generator
on U gives exactly that same frame on every ambient subopen of U. -/
lemma apply (hs : M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s =
    OpenLineFrameCoordinates318.frame M U e U le_rfl 1)
    (V : X.Opens) (hV : V ≤ U) (a : Γ(X,V)) :
    SectionGeneratedGluing318.genLinear (ModuleGlobalSections318.ofTop M s) V a =
      OpenLineFrameCoordinates318.frame M U e V hV a := by
  change (ModuleGlobalSections318.ofTop M s).val.app (op V) a = _
  rw [ModuleGlobalSections318.ofTop_apply]
  have hr : M.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op s =
      OpenLineFrameCoordinates318.frame M U e V hV 1 := by
    calc
      _ = M.presheaf.map (homOfLE hV).op
          (M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s) := by
        rw [← Functor.map_comp_apply] <;> rfl
      _ = M.presheaf.map (homOfLE hV).op
          (OpenLineFrameCoordinates318.frame M U e U le_rfl 1) := congrArg _ hs
      _ = _ := by rw [OpenLineFrameCoordinates318.natural,map_one]
  rw [hr,← LinearEquiv.map_smul]
  simp only [smul_eq_mul,mul_one]

lemma bijective (hs : M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s =
    OpenLineFrameCoordinates318.frame M U e U le_rfl 1)
    (V : X.Opens) (hV : V ≤ U) :
    Function.Bijective (SectionGeneratedGluing318.genLinear (ModuleGlobalSections318.ofTop M s) V) := by
  have he : (SectionGeneratedGluing318.genLinear (ModuleGlobalSections318.ofTop M s) V :
      Γ(X,V) → Γ(M,V)) = OpenLineFrameCoordinates318.frame M U e V hV :=
    funext (apply M U e s hs V hV)
  rw [he]
  exact (OpenLineFrameCoordinates318.frame M U e V hV).bijective
end OriginalGlobalFrameGenerator318
