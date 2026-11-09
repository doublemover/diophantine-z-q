module
public import OriginalOpenRestrictionComposition318
public import ModuleLocalGluing318
public section
noncomputable section
namespace AffineBasisModuleMaps318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace ModuleLocalGluing318
set_option maxHeartbeats 2200000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} (M N : X.Modules)

/-- Linear maps only on actual affine opens, with naturality only for
nested affine opens. No maps on non-affine opens are supplied. -/
structure Data where
  app : ∀ U : X.affineOpens, Γ(M,U.1) →ₗ[Γ(X,U.1)] Γ(N,U.1)
  natural : ∀ (U V : X.affineOpens) (h : V.1 ≤ U.1) (s : Γ(M,U.1)),
    res N h (app U s) = app V (res M h s)

variable {M N} (D : Data M N)

lemma section_ext (W : X.Opens) (s t : Γ(N,W))
    (h : ∀ (V : X.affineOpens) (hV : V.1 ≤ W), res N hV s = res N hV t) : s = t := by
  apply TopCat.Presheaf.IsSheaf.section_ext N.isSheaf
  intro x hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx W.isOpen
  exact ⟨V, hVW, hxV, h ⟨V,hV⟩ hVW⟩

abbrev basis (X : Scheme.{u}) : X.affineOpens → X.Opens := fun U => U.1

lemma basis_range : Set.range (basis X) = X.affineOpens := by
  ext U
  constructor
  · rintro ⟨⟨V,hV⟩,rfl⟩
    exact hV
  · intro hU
    exact ⟨⟨U,hU⟩,rfl⟩

/-- The actual additive presheaf map on the entire affine-open basis. -/
@[expose] def basisMap :
    (inducedFunctor (basis X)).op ⋙ M.presheaf ⟶
      (inducedFunctor (basis X)).op ⋙ N.presheaf where
  app U := AddCommGrpCat.ofHom (D.app U.unop).toAddMonoidHom
  naturality {U V} h := by
    ext s
    exact (D.natural U.unop V.unop
      (leOfHom ((inducedFunctor (basis X)).map h.unop)) s).symm

/-- The original sheaf basis-extension equivalence constructs the map on
all opens, including non-affine intersections. -/
@[expose] def additiveMap : M.presheaf ⟶ N.presheaf :=
  TopCat.Sheaf.restrictHomEquivHom M.presheaf ⟨N.presheaf,N.isSheaf⟩
    (show Opens.IsBasis (Set.range (basis X)) from by
      simpa only [basis_range] using X.isBasis_affineOpens)
    (basisMap D)

lemma additiveMap_affine (U : X.affineOpens) :
    (additiveMap D).app (op U.1) = AddCommGrpCat.ofHom (D.app U).toAddMonoidHom := by
  have hh := (TopCat.Sheaf.restrictHomEquivHom M.presheaf ⟨N.presheaf,N.isSheaf⟩
    (B:=basis X) (show Opens.IsBasis (Set.range (basis X)) from by
      simpa only [basis_range] using X.isBasis_affineOpens)).left_inv
    (basisMap D)
  exact congrArg (fun k => k.app (op U)) hh

lemma additive_natural {W V : X.Opens} (h : V ≤ W) (s : Γ(M,W)) :
    res N h ((additiveMap D).app (op W) s) =
      (additiveMap D).app (op V) (res M h s) :=
  (congrArg (fun k => k s) ((additiveMap D).naturality (homOfLE h).op)).symm

/-- Linearity over every original section ring follows from affine-basis
linearity and genuine sheaf separation; it is not assumed globally. -/
lemma additive_smul (W : X.Opens) (a : Γ(X,W)) (s : Γ(M,W)) :
    (additiveMap D).app (op W) (a • s) = a • (additiveMap D).app (op W) s := by
  apply section_ext W
  intro V hV
  rw [additive_natural]
  have hm : res M hV (a • s) = X.presheaf.map (homOfLE hV).op a • res M hV s :=
    M.val.map_smul (homOfLE hV).op a s
  have hn : res N hV (a • (additiveMap D).app (op W) s) =
      X.presheaf.map (homOfLE hV).op a • res N hV ((additiveMap D).app (op W) s) :=
    N.val.map_smul (homOfLE hV).op a ((additiveMap D).app (op W) s)
  rw [hm, hn, additive_natural, additiveMap_affine]
  exact (D.app V).map_smul _ _

@[expose] def hom : M ⟶ N where
  val.app W := ModuleCat.ofHom
    { toFun := (additiveMap D).app W
      map_add' := map_add ((additiveMap D).app W)
      map_smul' := additive_smul D W.unop }
  val.naturality h := by
    ext s
    exact (additive_natural D (leOfHom h.unop) s).symm

lemma hom_affine (U : X.affineOpens) (s : Γ(M,U.1)) :
    (hom D).app U.1 s = D.app U s :=
  congrArg (fun k => k s) (additiveMap_affine D U)

/-- Every actual sheaf map is determined by its original affine components. -/
lemma hom_ext {a b : M ⟶ N}
    (h : ∀ (U : X.affineOpens) (s : Γ(M,U.1)), a.app U.1 s = b.app U.1 s) : a = b := by
  apply Scheme.Modules.hom_ext
  intro W
  ext s
  apply section_ext W
  intro V hV
  have ha := PresheafOfModules.naturality_apply a.val (homOfLE hV).op s
  have hb := PresheafOfModules.naturality_apply b.val (homOfLE hV).op s
  exact ha.symm.trans ((h V _).trans hb)

lemma hom_unique (a : M ⟶ N)
    (h : ∀ (U : X.affineOpens) (s : Γ(M,U.1)), a.app U.1 s = D.app U s) : a = hom D := by
  apply hom_ext
  intro U s
  exact (h U s).trans (hom_affine D U s).symm
end AffineBasisModuleMaps318
