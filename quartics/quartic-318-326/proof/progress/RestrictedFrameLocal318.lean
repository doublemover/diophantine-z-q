module
public import ModuleFrameDescent318
public import IntrinsicChartNormalization318
public section
noncomputable section
namespace RestrictedFrameLocal318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (M : Y.Modules)
    (e : (Scheme.Modules.restrictFunctor j).obj (SheafOfModules.unit Y.ringCatSheaf) ≅ M.restrict j)
    (s : Γ(M,j ''ᵁ ⊤))
    (he : e.hom.val.app (op ⊤) (show Γ(Y,j ''ᵁ ⊤) from 1)=s)

include he

/-- A genuine frame on an actual open restriction gives a free generator on
every ambient subopen of that chart image. -/
theorem generator_bijective (V : Y.Opens) (hV : V ≤ j ''ᵁ ⊤) :
    Function.Bijective (fun a : Γ(Y,V) =>
      a • M.presheaf.map (homOfLE hV).op s) := by
  let P (V : Y.Opens) := ∀ hV : V ≤ j ''ᵁ ⊤,
    Function.Bijective (fun a : Γ(Y,V) => a • M.presheaf.map (homOfLE hV).op s)
  have hchart (U : X.Opens) : P (j ''ᵁ U) := by
    intro hU
    let q : Γ(Y,j ''ᵁ U) →+ Γ(M,j ''ᵁ U) := (e.hom.val.app (op U)).hom.toAddMonoidHom
    let i := (homOfLE (show U ≤ ⊤ from le_top)).op
    have hn := PresheafOfModules.naturality_apply e.hom.val i (show Γ(Y,j ''ᵁ ⊤) from 1)
    change q (Y.presheaf.map (homOfLE hU).op 1) =
      M.presheaf.map (homOfLE hU).op (e.hom.val.app (op ⊤) (show Γ(Y,j ''ᵁ ⊤) from 1)) at hn
    rw [map_one,he] at hn
    have hq (a : Γ(Y,j ''ᵁ U)) : q a = a • M.presheaf.map (homOfLE hU).op s := by
      have hl := (e.hom.val.app (op U)).hom.map_smul ((j.appIso U).hom a)
        (show Γ(Y,j ''ᵁ U) from 1)
      change q ((j.appIso U).inv ((j.appIso U).hom a) * 1) =
        (j.appIso U).inv ((j.appIso U).hom a) • q 1 at hl
      rw [Iso.hom_inv_id_apply,mul_one,hn] at hl
      exact hl
    have hb : Function.Bijective q := ConcreteCategory.bijective_of_isIso (e.hom.app U)
    have hfun : (fun a : Γ(Y,j ''ᵁ U) => a • M.presheaf.map (homOfLE hU).op s) = q :=
      funext (fun a => (hq a).symm)
    rw [hfun]
    exact hb
  have htop : j ''ᵁ (j ⁻¹ᵁ V) = V := by
    apply TopologicalSpace.Opens.ext
    apply Set.image_preimage_eq_of_subset
    intro x hx
    have h := hV hx
    rcases h with ⟨a,_,ha⟩
    exact ⟨a,ha⟩
  exact (Eq.mp (congrArg P htop) (hchart (j ⁻¹ᵁ V))) hV
end RestrictedFrameLocal318
