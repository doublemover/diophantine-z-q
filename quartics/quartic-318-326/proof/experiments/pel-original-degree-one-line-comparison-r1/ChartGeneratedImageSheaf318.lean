module
public import LocallyPrincipalImageFrame318
public import GlobalScalarSheafEndomorphism318
public section
noncomputable section
namespace ChartGeneratedImageSheaf318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable {U X : Scheme} (j : U ⟶ X) [IsOpenImmersion j]
variable {ι : Type} (r : ι → Γ(U,⊤))

/-- The actual direct image of the structure sheaf on the chosen chart.
This serves as a common ambient module sheaf, not a presheaf of guessed
rational functions and not a transported analytic line bundle. -/
@[expose] def ambient : X.Modules :=
  (Scheme.Modules.pushforward j).obj (SheafOfModules.unit U.ringCatSheaf)

@[expose] def generator (i : ι) : SheafOfModules.unit X.ringCatSheaf ⟶ ambient j :=
  (Scheme.Modules.restrictAdjunction j).homEquiv _ _
    ((Scheme.Modules.restrictUnitIso j).hom ≫
      GlobalScalarSheafEndomorphism318.endomorphism U (r i))

@[expose] def presentation : SheafOfModules.free (R := X.ringCatSheaf) ι ⟶ ambient j :=
  (ambient j).freeHomEquiv.symm (fun i => (ambient j).unitHomEquiv (generator j r i))

@[reassoc] lemma generator_presentation (i : ι) :
    SheafOfModules.ιFree i ≫ presentation j r = generator j r i := by
  rw [←SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
  simp only [presentation,Equiv.apply_symm_apply,Equiv.symm_apply_apply]

/-- A globally defined actual image in the abelian category of module
sheaves. Its later frames must be proved on the complete chart cover. -/
@[expose] def sheaf : X.Modules := image (presentation j r)

@[reassoc] lemma restricted_generator (i : ι) :
    (Scheme.Modules.restrictFunctor j).map (generator j r i) ≫
      (Scheme.Modules.restrictAdjunction j).counit.app (SheafOfModules.unit U.ringCatSheaf) =
    (Scheme.Modules.restrictUnitIso j).hom ≫
      GlobalScalarSheafEndomorphism318.endomorphism U (r i) := by
  exact ((Scheme.Modules.restrictAdjunction j).homEquiv _ _).symm_apply_apply _

@[expose] def coefficientRow :
    (Scheme.Modules.restrictFunctor j).obj (SheafOfModules.free (R := X.ringCatSheaf) ι) ⟶
      SheafOfModules.unit U.ringCatSheaf :=
  (Scheme.Modules.restrictFunctor j).map (presentation j r) ≫
    (Scheme.Modules.restrictAdjunction j).counit.app _

lemma coefficientRow_split (i : ι) (hi : r i = 1) :
    ((Scheme.Modules.restrictUnitIso j).inv ≫
      (Scheme.Modules.restrictFunctor j).map (SheafOfModules.ιFree i)) ≫
      coefficientRow j r = 𝟙 _ := by
  rw [coefficientRow,Category.assoc,←Category.assoc
    ((Scheme.Modules.restrictFunctor j).map (SheafOfModules.ιFree i)),
    ←Functor.map_comp,generator_presentation,restricted_generator,hi,
    GlobalScalarSheafEndomorphism318.endomorphism_one,Category.comp_id,Iso.inv_hom_id]

/-- The anchor chart is genuinely trivial whenever one of its chosen
coordinate ratios is literally one. This is a produced frame of the
actual global image sheaf, not an assumed local-freeness condition. -/
@[expose] def anchorFrame (i : ι) (hi : r i = 1) :
    SheafOfModules.unit U.ringCatSheaf ≅
      (Scheme.Modules.restrictFunctor j).obj (sheaf j r) := by
  letI : Epi (coefficientRow j r) := epi_of_epi_fac (coefficientRow_split j r i hi)
  let a := (asIso ((Scheme.Modules.restrictAdjunction j).counit.app
    (SheafOfModules.unit U.ringCatSheaf))).inv
  exact LocallyPrincipalImageFrame318.frame j (presentation j r)
    (coefficientRow j r) a (by simp [coefficientRow,a])
end ChartGeneratedImageSheaf318
