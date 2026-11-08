module
public import AffineDerivationExtension318
public section
noncomputable section
namespace AffineIntrinsicIso318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- Morphisms from the actual tilde Kähler sheaf are determined by their values
on the actual global universal differential sections. -/
theorem tildeHom_ext {M : (Spec S).Modules}
    (a b : tilde (CommRingCat.KaehlerDifferential f) ⟶ M)
    (h : ∀ s : S,
      moduleSpecΓFunctor.map a
        ((tilde.isoTop (CommRingCat.KaehlerDifferential f)).hom
          (CommRingCat.KaehlerDifferential.d s)) =
      moduleSpecΓFunctor.map b
        ((tilde.isoTop (CommRingCat.KaehlerDifferential f)).hom
          (CommRingCat.KaehlerDifferential.d s))) : a=b := by
  apply ((tilde.adjunction (R:=S)).homEquiv _ _).injective
  apply CommRingCat.KaehlerDifferential.ext
  intro s
  exact h s

/-- The actual universal algebraic derivation viewed in genuine global sections
of its tilde sheaf. -/
@[expose] def topUniversal :
    (moduleSpecΓFunctor.obj (tilde (CommRingCat.KaehlerDifferential f))).Derivation f :=
  ModuleCat.Derivation.mk
    (fun s => (tilde.isoTop (CommRingCat.KaehlerDifferential f)).hom
      (CommRingCat.KaehlerDifferential.d s))
    (by intro a b; simp [CommRingCat.KaehlerDifferential.d,ModuleCat.Derivation.d_add])
    (by
      intro a b
      rw [CommRingCat.KaehlerDifferential.d,ModuleCat.Derivation.d_mul,map_add,
        map_smul,map_smul])
    (by intro r; rw [CommRingCat.KaehlerDifferential.d,ModuleCat.Derivation.d_map,map_zero])

/-- A genuine sheaf derivation into tilde(Omega), constructed from localized
jets and sheaf gluing on the actual affine basis. -/
@[expose] def tildeD :=
  AffineDerivationExtension318.extend (tilde (CommRingCat.KaehlerDifferential f)) f (topUniversal f)

/-- The intrinsic universal property supplies the actual inverse candidate. -/
@[expose] def inverse : AffineIntrinsicComparison318.omega f ⟶
    tilde (CommRingCat.KaehlerDifferential f) :=
  UniversalSheafDifferentials318.desc (AffineIntrinsicComparison318.coefficients f) (tildeD f)

theorem comparison_inverse : AffineIntrinsicComparison318.comparison f ≫ inverse f = 𝟙 _ := by
  apply tildeHom_ext f
  intro s
  simp only [Functor.map_comp,ModuleCat.comp_apply,Functor.map_id,ModuleCat.id_apply,
    AffineIntrinsicComparison318.comparison_global]
  have h := PresheafOfModulesOfCommRing.Derivation.congr_d
    (UniversalSheafDifferentials318.desc_fac (AffineIntrinsicComparison318.coefficients f)
      (tildeD f)) (X:=op ⊤) ((Scheme.ΓSpecIso S).inv s)
  exact h.trans (AffineDerivationExtension318.extend_top
    (tilde (CommRingCat.KaehlerDifferential f)) f (topUniversal f) s)

theorem inverse_comparison : inverse f ≫ AffineIntrinsicComparison318.comparison f = 𝟙 _ := by
  letI := AffineIntrinsicComparison318.comparison_epi f
  apply (cancel_epi (AffineIntrinsicComparison318.comparison f)).1
  rw [←Category.assoc,comparison_inverse,Category.id_comp,Category.comp_id]

/-- The intrinsic all-open sheafification of relative Kähler differentials is
canonically the actual tilde Kähler sheaf on every affine scheme. Both directions
are constructed; no affine-comparison or quasi-coherence premise is supplied. -/
@[expose] def iso : tilde (CommRingCat.KaehlerDifferential f) ≅
    AffineIntrinsicComparison318.omega f :=
  ⟨AffineIntrinsicComparison318.comparison f,inverse f,comparison_inverse f,inverse_comparison f⟩

theorem iso_global_D (s : S) :
    moduleSpecΓFunctor.map (iso f).hom
      ((tilde.isoTop (CommRingCat.KaehlerDifferential f)).hom
        (CommRingCat.KaehlerDifferential.d s)) =
      (AffineIntrinsicComparison318.D f).d ((Scheme.ΓSpecIso S).inv s) :=
  AffineIntrinsicComparison318.comparison_global f s
end AffineIntrinsicIso318
