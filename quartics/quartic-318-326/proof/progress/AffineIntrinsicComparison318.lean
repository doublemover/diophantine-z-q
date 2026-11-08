module
public import AffineDerivationDetermination318
public section
noncomputable section
namespace AffineIntrinsicComparison318
open AlgebraicGeometry CategoryTheory Opposite
open PresheafOfModulesOfCommRing
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- Literal base coefficients in the regular-function sheaf of Spec S. -/
@[expose] def coefficients : (Functor.const (Spec S).Opensᵒᵖ).obj R ⟶ (Spec S).presheaf :=
  FamilyIntrinsicDifferentials318.coefficientPresheaf R (f ≫ (Scheme.ΓSpecIso S).inv)

@[expose] def omega : (Spec S).Modules := UniversalSheafDifferentials318.omega (coefficients f)
@[expose] def D := UniversalSheafDifferentials318.D (coefficients f)

/-- Global evaluation of an actual sheaf-valued derivation, retaining the actual
Gamma-Spec coefficient isomorphism. -/
@[expose] def topDerivation {M : (Spec S).Modules}
    (d : PresheafOfModulesOfCommRing.Derivation' M.val (coefficients f)) :
    (moduleSpecΓFunctor.obj M).Derivation f :=
  ModuleCat.Derivation.mk (fun s => d.d ((Scheme.ΓSpecIso S).inv s))
    (by intro a b; simp)
    (by intro a b; change d.d ((Scheme.ΓSpecIso S).inv (a*b)) = _; rw [map_mul,d.d_mul]; rfl)
    (by
      intro r
      have h := d.d_app (X:=op ⊤) r
      change d.d ((Spec S).presheaf.map (𝟙 (op ⊤))
        ((Scheme.ΓSpecIso S).inv (f r)))=0 at h
      have hi := congrArg (fun k => k ((Scheme.ΓSpecIso S).inv (f r)))
        ((Spec S).presheaf.map_id (op ⊤))
      exact (congrArg (fun z => d.d (X:=op ⊤) z) hi).symm.trans h)

/-- The canonical actual affine comparison from tilde of the algebraic Kähler
module to the intrinsic universal differential sheaf. No isomorphism is assumed. -/
@[expose] def comparison : tilde (CommRingCat.KaehlerDifferential f) ⟶ omega f :=
  ((tilde.adjunction (R:=S)).homEquiv _ _).symm (topDerivation f (D f)).desc

theorem comparison_global (s : S) :
    moduleSpecΓFunctor.map (comparison f)
      ((tilde.isoTop (CommRingCat.KaehlerDifferential f)).hom
        (CommRingCat.KaehlerDifferential.d s)) =
      (D f).d ((Scheme.ΓSpecIso S).inv s) := by
  have h := ((tilde.adjunction (R:=S)).homEquiv _ _).apply_symm_apply
    (topDerivation f (D f)).desc
  change (tilde.adjunction (R:=S)).homEquiv _ _ (comparison f) = _ at h
  rw [Adjunction.homEquiv_unit] at h
  have hh := congrArg (fun k => k (CommRingCat.KaehlerDifferential.d s)) h
  change moduleSpecΓFunctor.map (comparison f)
    ((tilde.isoTop (CommRingCat.KaehlerDifferential f)).hom
      (CommRingCat.KaehlerDifferential.d s)) = _ at hh
  exact hh.trans (ModuleCat.Derivation.desc_d _ s)

/-- The canonical affine comparison is an epimorphism of actual O-module
sheaves. This is proved by global derivation determination, not by assuming
quasi-coherence or invertibility of the comparison. -/
theorem comparison_epi : Epi (comparison f) := by
  constructor
  intro M a b hab
  apply UniversalSheafDifferentials318.hom_ext (coefficients f)
  apply AffineDerivationDetermination318.ext_top
  intro z
  let s := (Scheme.ΓSpecIso S).hom z
  have hz : (Scheme.ΓSpecIso S).inv s = z :=
    Iso.hom_inv_id_apply (Scheme.ΓSpecIso S) z
  rw [←hz]
  have hh := congrArg (fun k => moduleSpecΓFunctor.map k
    ((tilde.isoTop (CommRingCat.KaehlerDifferential f)).hom
      (CommRingCat.KaehlerDifferential.d s))) hab
  simp only [Functor.map_comp, ModuleCat.comp_apply, comparison_global] at hh
  exact hh
end AffineIntrinsicComparison318
