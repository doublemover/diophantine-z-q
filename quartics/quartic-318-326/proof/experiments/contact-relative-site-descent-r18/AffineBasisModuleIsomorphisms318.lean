module
public import AffineBasisModuleMaps318
public section
noncomputable section
namespace AffineBasisModuleIsomorphisms318
open AlgebraicGeometry CategoryTheory Opposite ModuleLocalGluing318
open AffineBasisModuleMaps318
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} {M N Q : X.Modules}

@[expose] def identity (M : X.Modules) : Data M M where
  app _ := LinearMap.id
  natural _ _ _ _ := rfl

@[expose] def comp (D : Data M N) (E : Data N Q) : Data M Q where
  app U := (E.app U).comp (D.app U)
  natural U V h s := by
    change res Q h (E.app U (D.app U s)) = E.app V (D.app V (res M h s))
    rw [E.natural,D.natural]

lemma hom_id (M : X.Modules) : hom (identity M) = 𝟙 M := by
  apply hom_ext
  intro U s
  exact hom_affine (identity M) U s

lemma hom_comp (D : Data M N) (E : Data N Q) : hom (comp D E) = hom D ≫ hom E := by
  apply hom_ext
  intro U s
  change (hom (comp D E)).app U.1 s = (hom E).app U.1 ((hom D).app U.1 s)
  rw [hom_affine,hom_affine,hom_affine]

/-- Original affine component isomorphisms need naturality only in the
forward direction; inverse naturality is derived by the same actual maps. -/
structure IsoData (M N : X.Modules) where
  app : ∀ U : X.affineOpens, Γ(M,U.1) ≃ₗ[Γ(X,U.1)] Γ(N,U.1)
  natural : ∀ (U V : X.affineOpens) (h : V.1 ≤ U.1) (s : Γ(M,U.1)),
    res N h (app U s) = app V (res M h s)

@[expose] def forward (D : IsoData M N) : Data M N where
  app U := (D.app U).toLinearMap
  natural := D.natural

@[expose] def backward (D : IsoData M N) : Data N M where
  app U := (D.app U).symm.toLinearMap
  natural U V h s := by
    apply (D.app V).injective
    simpa only [LinearEquiv.apply_symm_apply] using (D.natural U V h ((D.app U).symm s)).symm

/-- A genuine global original sheaf iso reconstructed from the whole
actual affine basis. No pair intersection is assumed affine. -/
@[expose] def iso (D : IsoData M N) : M ≅ N where
  hom := hom (forward D)
  inv := hom (backward D)
  hom_inv_id := by
    apply hom_ext
    intro U s
    change (hom (backward D)).app U.1 ((hom (forward D)).app U.1 s) = s
    rw [hom_affine,hom_affine]
    exact (D.app U).symm_apply_apply s
  inv_hom_id := by
    apply hom_ext
    intro U s
    change (hom (forward D)).app U.1 ((hom (backward D)).app U.1 s) = s
    rw [hom_affine,hom_affine]
    exact (D.app U).apply_symm_apply s

lemma iso_affine (D : IsoData M N) (U : X.affineOpens) (s : Γ(M,U.1)) :
    (iso D).hom.app U.1 s = D.app U s := hom_affine (forward D) U s

/-- The whole-sheaf cocycle is reflected by the original affine component
cocycle, rather than being supplied as an additional global condition. -/
lemma hom_cocycle (D : Data M N) (E : Data N Q) (F : Data M Q)
    (h : ∀ (U : X.affineOpens) (s : Γ(M,U.1)), E.app U (D.app U s) = F.app U s) :
    hom D ≫ hom E = hom F := by
  apply hom_ext
  intro U s
  change (hom E).app U.1 ((hom D).app U.1 s) = (hom F).app U.1 s
  rw [hom_affine,hom_affine,hom_affine]
  exact h U s
end AffineBasisModuleIsomorphisms318
