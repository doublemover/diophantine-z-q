module
public import GlobalScalarSheafEndomorphism318
public import OpenRestrictionImages318
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public section
noncomputable section
namespace RestrictedFreeScalarRow318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable {U X : Scheme} (k : U ⟶ X) [IsOpenImmersion k]
variable {ι : Type} (c : ι → Γ(U,⊤))

@[expose] def freeIso : SheafOfModules.free (R := U.ringCatSheaf) ι ≅
    (Scheme.Modules.restrictFunctor k).obj (SheafOfModules.free (R := X.ringCatSheaf) ι) :=
  SheafOfModules.mapFreeIso (Scheme.Modules.restrictFunctor k) ι
    (Scheme.Modules.restrictUnitIso k).symm

@[expose] def localRow : SheafOfModules.free (R := U.ringCatSheaf) ι ⟶
    SheafOfModules.unit U.ringCatSheaf :=
  (SheafOfModules.unit U.ringCatSheaf).freeHomEquiv.symm
    (fun i => GlobalScalarSheafEndomorphism318.section U (c i))

@[reassoc] lemma localRow_generator (i : ι) :
    SheafOfModules.ιFree i ≫ localRow c =
      GlobalScalarSheafEndomorphism318.endomorphism U (c i) := by
  rw [←SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
  simp only [localRow,Equiv.apply_symm_apply,GlobalScalarSheafEndomorphism318.endomorphism]

@[expose] def row :
    (Scheme.Modules.restrictFunctor k).obj (SheafOfModules.free (R := X.ringCatSheaf) ι) ⟶
      SheafOfModules.unit U.ringCatSheaf :=
  (freeIso (ι := ι) k).inv ≫ localRow c

@[reassoc] lemma row_generator (i : ι) :
    (Scheme.Modules.restrictFunctor k).map (SheafOfModules.ιFree i) ≫ row k c =
      (Scheme.Modules.restrictUnitIso k).hom ≫
        GlobalScalarSheafEndomorphism318.endomorphism U (c i) := by
  rw [row,←Category.assoc,freeIso,SheafOfModules.map_ιFree_mapFreeIso_inv,
    Category.assoc,localRow_generator]
  rfl

lemma row_split (i : ι) (hi : c i=1) :
    ((Scheme.Modules.restrictUnitIso k).inv ≫
      (Scheme.Modules.restrictFunctor k).map (SheafOfModules.ιFree i)) ≫ row k c = 𝟙 _ := by
  rw [Category.assoc,row_generator,hi,GlobalScalarSheafEndomorphism318.endomorphism_one,
    Category.comp_id,Iso.inv_hom_id]

lemma row_epi (i : ι) (hi : c i=1) : Epi (row k c) :=
  epi_of_epi_fac (row_split k c i hi)

/-- Literal generator identities imply equality of the WHOLE restricted
presentation, through the actual restriction/free-sheaf isomorphism. -/
theorem factorization {N : X.Modules}
    (f : SheafOfModules.free (R := X.ringCatSheaf) ι ⟶ N)
    (a : SheafOfModules.unit U.ringCatSheaf ⟶ (Scheme.Modules.restrictFunctor k).obj N)
    (h : ∀ i : ι,
      (Scheme.Modules.restrictFunctor k).map (SheafOfModules.ιFree i ≫ f) =
      (Scheme.Modules.restrictUnitIso k).hom ≫
        GlobalScalarSheafEndomorphism318.endomorphism U (c i) ≫ a) :
    row k c ≫ a = (Scheme.Modules.restrictFunctor k).map f := by
  apply (cancel_epi (freeIso (ι := ι) k).hom).1
  apply ((Scheme.Modules.restrictFunctor k).obj N).freeHomEquiv.injective
  funext i
  change ((Scheme.Modules.restrictFunctor k).obj N).unitHomEquiv
      (SheafOfModules.ιFree i ≫ (freeIso (ι := ι) k).hom ≫ row k c ≫ a) =
    ((Scheme.Modules.restrictFunctor k).obj N).unitHomEquiv
      (SheafOfModules.ιFree i ≫ (freeIso (ι := ι) k).hom ≫
        (Scheme.Modules.restrictFunctor k).map f)
  congr 1
  rw [freeIso,SheafOfModules.ιFree_mapFreeIso_hom]
  simp only [Iso.symm_hom,Category.assoc]
  rw [←Category.assoc ((Scheme.Modules.restrictFunctor k).map (SheafOfModules.ιFree i)),
    row_generator,←Functor.map_comp,h]
  simp only [Iso.inv_hom_id_assoc]
end RestrictedFreeScalarRow318
