module
public import NormalizedSectionFrame318
public section
noncomputable section
namespace LocalCoordinateRelation318
open AlgebraicGeometry CategoryTheory Opposite
open ClutchedModule318
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    {M : X.Modules}
@[expose] def localMap (f : unit X ⟶ M) : unit Y ⟶ M.restrict j :=
  (Scheme.Modules.restrictUnitIso j).inv ≫ (Scheme.Modules.restrictFunctor j).map f

/-- The canonical local coordinate map sends one to the literal restricted section. -/
theorem localMap_top_one (f : unit X ⟶ M) :
    (localMap j f).app ⊤ (show Γ(Y,⊤) from 1)=
      M.presheaf.map (homOfLE (show j ''ᵁ ⊤≤⊤ from le_top)).op
        (f.app ⊤ (show Γ(X,⊤) from 1)) := by
  have hu : (Scheme.Modules.restrictUnitIso j).inv.app ⊤
      (show Γ(Y,⊤) from 1)=(show Γ(X,j ''ᵁ ⊤) from 1) := by
    change (j.appIso ⊤).inv.hom 1=1
    exact map_one _
  change f.app (j ''ᵁ ⊤) ((Scheme.Modules.restrictUnitIso j).inv.app ⊤
    (show Γ(Y,⊤) from 1))=_
  rw [hu]
  have hn := congrArg (fun q => q (show Γ(X,⊤) from 1))
    (f.mapPresheaf.naturality (homOfLE (show j ''ᵁ ⊤≤⊤ from le_top)).op)
  change f.app (j ''ᵁ ⊤) (X.presheaf.map (homOfLE (show j ''ᵁ ⊤≤⊤ from le_top)).op 1)=
    M.presheaf.map (homOfLE (show j ''ᵁ ⊤≤⊤ from le_top)).op
      (f.app ⊤ (show Γ(X,⊤) from 1)) at hn
  simpa only [map_one] using hn

theorem localMap_recover (f : unit X ⟶ M) :
    (Scheme.Modules.restrictFunctor j).map f=
      (Scheme.Modules.restrictUnitIso j).hom ≫ localMap j f := by
  simp [localMap]

theorem multiply_comp (a b : Γ(Y,⊤)) : multiply a ≫ multiply b=multiply (a*b) := by
  apply ModuleTopExt318.ext
  change (multiply b).app ⊤ ((multiply a).app ⊤ (show Γ(Y,⊤) from 1))=
    (multiply (a*b)).app ⊤ (show Γ(Y,⊤) from 1)
  rw [multiply_top,multiply_top,multiply_top,one_mul,one_mul]

/-- Exact frame coefficients give the literal local ratio identity for both
coordinate morphisms, without choosing a new unit rescaling. -/
theorem relation (e : M.restrict j ≅ unit Y) (f₀ f₁ : unit X ⟶ M)
    (a b₀ b₁ : Γ(Y,⊤))
    (h₀ : e.hom.app ⊤ (M.presheaf.map (homOfLE (show j ''ᵁ ⊤≤⊤ from le_top)).op
      (f₀.app ⊤ (show Γ(X,⊤) from 1)))=b₀)
    (h₁ : e.hom.app ⊤ (M.presheaf.map (homOfLE (show j ''ᵁ ⊤≤⊤ from le_top)).op
      (f₁.app ⊤ (show Γ(X,⊤) from 1)))=b₁)
    (hr : b₁=a*b₀) : localMap j f₁=multiply a ≫ localMap j f₀ := by
  apply (cancel_mono e.hom).mp
  have h0 := NormalizedSectionFrame318.framedMap_eq j M e f₀ b₀ h₀
  have h1 := NormalizedSectionFrame318.framedMap_eq j M e f₁ b₁ h₁
  change localMap j f₀≫e.hom=multiply b₀ at h0
  change localMap j f₁≫e.hom=multiply b₁ at h1
  rw [Category.assoc,h0,h1,multiply_comp,hr]
end LocalCoordinateRelation318
