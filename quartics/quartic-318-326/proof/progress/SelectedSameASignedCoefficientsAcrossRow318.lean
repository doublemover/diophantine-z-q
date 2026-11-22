module

public import SelectedSameASignedLiftCocycle318

/-! Transport the actual local lifts, not a representative selected afterwards
from the same cohomology class. All coefficients use right minus left. -/
public section
noncomputable section
open CategoryTheory Opposite TopologicalSpace

namespace SelectedSameASignedCoefficientsAcrossRow318

universe u
open SelectedSameAActualLiftDifference318 (Sh local_inclusion_injective)
open SelectedSameASignedLiftCocycle318 (res res_natural coeff coeff_beta)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : TopCat.{u})
variable {S T : ShortComplex (Sh X)} {I : Type u} (V : I → Opens X)
variable (G : S ⟶ T)
variable (z : S.X₃.obj.obj (op (⊤ : Opens X))) (t : ∀ j, S.X₂.obj.obj (op (V j)))
variable (ht : ∀ j, S.g.hom.app (op (V j)) (t j) = res X S.X₃ le_top z)

include ht in
theorem map_lifts (j : I) :
    T.g.hom.app (op (V j)) (G.τ₂.hom.app (op (V j)) (t j)) =
      res X T.X₃ le_top (G.τ₃.hom.app (op (⊤ : Opens X)) z) := by
  have h := congrArg (fun f : S.X₂ ⟶ T.X₃ => f.hom.app (op (V j)) (t j)) G.comm₂₃
  change T.g.hom.app _ (G.τ₂.hom.app _ (t j)) =
    G.τ₃.hom.app _ (S.g.hom.app _ (t j)) at h
  exact h.trans ((congrArg (fun x => G.τ₃.hom.app (op (V j)) x) (ht j)).trans
    (res_natural X G.τ₃ le_top z))

variable [HasSheafify (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u}]

/-- Naturality on sections of each full named intersection. The target lift
and its proof are produced here; no assumption of compatibility of cocycles. -/
theorem map_coeff (hS : S.ShortExact) (hT : T.ShortExact) (j l : I) :
    coeff X T hT V (G.τ₃.hom.app (op (⊤ : Opens X)) z)
      (fun s => G.τ₂.hom.app (op (V s)) (t s)) (map_lifts X V G z t ht) j l =
    G.τ₁.hom.app (op (V j ⊓ V l)) (coeff X S hS V z t ht j l) := by
  let W := V j ⊓ V l
  let b := coeff X S hS V z t ht j l
  have h := congrArg (fun f : S.X₁ ⟶ T.X₂ => f.hom.app (op W) b) G.comm₁₂
  change T.f.hom.app (op W) (G.τ₁.hom.app (op W) b) =
    G.τ₂.hom.app (op W) (S.f.hom.app (op W) b) at h
  apply local_inclusion_injective X T hT W
  refine (coeff_beta X T hT V _ _ _ j l).trans ?_
  rw [h]
  change _ = G.τ₂.hom.app (op W) (S.f.hom.app (op W) (coeff X S hS V z t ht j l))
  rw [coeff_beta, map_sub, res_natural X G.τ₂, res_natural X G.τ₂]

/-- Going back with the actual comparison iso recovers the *same* old
contracted section. In particular no global gauge is introduced by transport. -/
theorem contract_inverse_coeff (E : T ≅ S) (hS : S.ShortExact) (hT : T.ShortExact)
    {L : Sh X} (ell : S.X₁ ⟶ L) (j l : I) :
    (E.hom.τ₁ ≫ ell).hom.app (op (V j ⊓ V l))
      (coeff X T hT V (E.inv.τ₃.hom.app (op (⊤ : Opens X)) z)
        (fun s => E.inv.τ₂.hom.app (op (V s)) (t s))
        (map_lifts X V E.inv z t ht) j l) =
    ell.hom.app (op (V j ⊓ V l)) (coeff X S hS V z t ht j l) := by
  rw [map_coeff X V E.inv z t ht hS hT]
  let W := V j ⊓ V l
  let b := coeff X S hS V z t ht j l
  have h := congrArg (fun f : S ⟶ S => f.τ₁.hom.app (op W) b) E.inv_hom_id
  change E.hom.τ₁.hom.app (op W) (E.inv.τ₁.hom.app (op W) b) = b at h
  exact congrArg (fun x => ell.hom.app (op W) x) h

end SelectedSameASignedCoefficientsAcrossRow318
