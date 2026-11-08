module
public import IntrinsicChartScalarInjection318
public import ActualOpenFractionField318
public section
noncomputable section
namespace AffineGlobalFunction318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 450000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}} {R:Type u} [CommRing R]
    (j:Spec (CommRingCat.of R)⟶X) [IsOpenImmersion j]
/-- The actual value of a global regular function in the whole affine chart. -/
@[expose] def value:Γ(X,⊤)→+*R:=
  (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.comp
    ((j.appIso ⊤).hom.hom.comp (X.presheaf.map (homOfLE (show j ''ᵁ ⊤≤⊤ from le_top)).op).hom)
lemma scalar_value (a:Γ(X,⊤)):
    ScaledGlobalSectionRestriction318.scalar j (value j a)=
      X.presheaf.map (homOfLE (show j ''ᵁ ⊤≤⊤ from le_top)).op a:=by
  simp only [ScaledGlobalSectionRestriction318.scalar,value,RingHom.comp_apply,
    Iso.hom_inv_id_apply]
lemma appTop_square:
    X.presheaf.map (homOfLE (show j ''ᵁ ⊤≤⊤ from le_top)).op≫(j.appIso ⊤).hom=j.appTop:=by
  rw [Scheme.Hom.appIso_hom',Scheme.Hom.map_appLE]
  change j.appTop≫(Spec (CommRingCat.of R)).presheaf.map (𝟙 (op ⊤))=j.appTop
  rw [CategoryTheory.Functor.map_id,Category.comp_id]
lemma value_appTop (a:Γ(X,⊤)):value j a=
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom (j.appTop a):=by
  have hh:=congrArg (fun f=>f a) (appTop_square j)
  exact congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).hom hh
variable [IsIntegral X] [IsDomain R]
local instance affineAlgebra:Algebra R (Spec (CommRingCat.of R)).functionField:=
  AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (CommRingCat.of R)
local instance top_nonempty:Nonempty (⊤:X.Opens):=⟨⟨genericPoint X,trivial⟩⟩
/-- The chart value represents the original generic germ, through the
actual open-immersion generic-stalk equivalence. -/
theorem generic_value (a:Γ(X,⊤)):
    letI:=ActualOpenFractionField318.sourceAlgebra j
    algebraMap R X.functionField (value j a)=X.germToFunctionField ⊤ a:=by
  letI:=ActualOpenFractionField318.sourceAlgebra j
  apply (ActualOpenFractionField318.genericEquiv j).injective
  change ActualOpenFractionField318.genericEquiv j
    ((ActualOpenFractionField318.genericEquiv j).symm
      (algebraMap R (Spec (CommRingCat.of R)).functionField (value j a)))=_
  rw [RingEquiv.apply_symm_apply,value_appTop]
  letI:Nonempty (j⁻¹ᵁ⊤):=⟨⟨genericPoint (Spec (CommRingCat.of R)),trivial⟩⟩
  have hh:=congrArg (fun f=>f a) (ActualOpenFractionField318.generic_germ j ⊤)
  change (OpenFunctionField318.fieldIso j).hom (X.germToFunctionField ⊤ a)=
    (Spec (CommRingCat.of R)).germToFunctionField ⊤ (j.appTop a) at hh
  rw [show ActualOpenFractionField318.genericEquiv j (X.germToFunctionField ⊤ a)=
    (Spec (CommRingCat.of R)).germToFunctionField ⊤ (j.appTop a) from hh]
  change (Spec (CommRingCat.of R)).germToFunctionField ⊤
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv
      ((Scheme.ΓSpecIso (CommRingCat.of R)).hom (j.appTop a)))=_
  rw [Iso.hom_inv_id_apply]
end AffineGlobalFunction318
