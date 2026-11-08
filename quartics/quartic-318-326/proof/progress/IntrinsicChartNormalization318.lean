module
public import AffineIntrinsicNormalization318
public import FamilyRestrictionNormalization318
public section
noncomputable section
namespace IntrinsicChartNormalization318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u

section RestrictionInverse
variable {X Y : Scheme.{u}} {j : X ⟶ Y} [IsOpenImmersion j]
    {R : CommRingCat.{u}}
    {φ : (Functor.const Y.Opensᵒᵖ).obj R ⟶ Y.presheaf}
    {ψ : (Functor.const X.Opensᵒᵖ).obj R ⟶ X.presheaf}

theorem inverse_fac (d : FamilyRestrictionNormalization318.Data j φ ψ)
    (U : X.Opens) (s : Γ(X,U)) :
    d.iso.inv.val.app (op U) ((UniversalSheafDifferentials318.D ψ).d s) =
      (UniversalSheafDifferentials318.D φ).d ((j.appIso U).inv s) := by
  have h := congrArg (d.iso.inv.val.app (op U)) (d.fac U s)
  have hc := congrArg (fun f => f.val.app (op U)
      ((UniversalSheafDifferentials318.D φ).d ((j.appIso U).inv s))) d.iso.hom_inv_id
  exact h.symm.trans hc
end RestrictionInverse

variable {Y : Scheme.{u}} {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (j : Spec (CommRingCat.of S) ⟶ Y) [IsOpenImmersion j]
    (p : Y ⟶ Spec (CommRingCat.of R))
    (h : j ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R S)))

@[expose] def restrictionData :
    FamilyRestrictionNormalization318.Data j (FamilyIntrinsicDifferentials318.coefficients p)
      (FamilyIntrinsicDifferentials318.coefficients (Spec.map (CommRingCat.ofHom (algebraMap R S)))) :=
  congrArg FamilyIntrinsicDifferentials318.coefficients h ▸ FamilyRestrictionNormalization318.familyData j p

/-- The actual chart comparison points from ordinary algebraic differentials
into the restriction of intrinsic global Omega. -/
@[expose] def iso : AffineDifferentialSheaf318.differentialSheaf (R:=R) (S:=S) ≅
    (FamilyIntrinsicDifferentials318.omega p).restrict j :=
  AffineIntrinsicNormalization318.algebraIso ≪≫ (restrictionData j p h).iso.symm

/-- Every algebraic universal differential has its exact ambient derivative
image under the actual chart comparison. -/
theorem differential (s : S) :
    moduleSpecΓFunctor.map (iso j p h).hom
      ((tilde.isoTop (R:=CommRingCat.of S) (ModuleCat.of S (KaehlerDifferential R S))).hom
        (KaehlerDifferential.D R S s)) =
    (FamilyIntrinsicDifferentials318.D p).d
      ((j.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of S)).inv s)) := by
  change moduleSpecΓFunctor.map (restrictionData j p h).iso.inv
    (moduleSpecΓFunctor.map (AffineIntrinsicNormalization318.algebraIso (R:=R) (S:=S)).hom
      ((tilde.isoTop (R:=CommRingCat.of S) (ModuleCat.of S (KaehlerDifferential R S))).hom
        (KaehlerDifferential.D R S s))) = _
  exact (congrArg (moduleSpecΓFunctor.map (restrictionData j p h).iso.inv)
    (AffineIntrinsicNormalization318.algebra_D (R:=R) (S:=S) s)).trans
    (inverse_fac (restrictionData j p h) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv s))
end IntrinsicChartNormalization318
