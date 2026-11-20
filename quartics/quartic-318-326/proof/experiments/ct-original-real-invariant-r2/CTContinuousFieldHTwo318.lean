module
public import CTFieldPrimitiveRestriction318
public import CTActualKrullCoordinateOrbit318
public import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Abel
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import all CTFieldPrimitiveRestriction318
public section
noncomputable section

namespace CTContinuousFieldHTwo318

open CategoryTheory groupCohomology CTFieldPrimitiveRestriction318
open CTActualKrullCoordinateOrbit318

variable (K : Type) [Field K] [CharZero K] [DecidableEq K]

/-- The actual degree-one continuous source with discrete field units.
The topology is used only on the native profinite domain. -/
def continuousOne : AddSubgroup ((Fin 1 → Gal K) → FieldUnitRep K) where
  carrier := {u | IsLocallyConstant u}
  zero_mem' := IsLocallyConstant.const 0
  add_mem' := fun hu hv => (hu.prodMk hv).comp fun p => p.1+p.2
  neg_mem' := fun hu => hu.comp Neg.neg

/-- The continuous cycles as actual cochain functions. They use the
pinned ordinary differential, but never quotient by ordinary cochains. -/
def continuousCycles : AddSubgroup ((Fin 2 → Gal K) → FieldUnitRep K) where
  carrier := {z | inhomogeneousCochains.d (FieldUnitRep K) 2 z=0 ∧ IsLocallyConstant z}
  zero_mem' := ⟨map_zero _,IsLocallyConstant.const 0⟩
  add_mem' := by
    rintro a b ⟨ha,hca⟩ ⟨hb,hcb⟩
    exact ⟨by rw [map_add,ha,hb,zero_add], (hca.prodMk hcb).comp fun p => p.1+p.2⟩
  neg_mem' := by
    rintro a ⟨ha,hca⟩
    exact ⟨by rw [map_neg,ha,neg_zero],hca.comp Neg.neg⟩

/-- The actual Mathlib cycle returned by the corrected cup supplies
exactly its literal included cochain, not a newly chosen representative. -/
def includeCycle (z : cocycles (FieldUnitRep K) 2)
    (hz : IsLocallyConstant (iCocycles (FieldUnitRep K) 2 z)) : continuousCycles K :=
  ⟨iCocycles (FieldUnitRep K) 2 z,by
    have h := (inhomogeneousCochains (FieldUnitRep K)).iCycles_d 2 3
    rw [inhomogeneousCochains.d_def (FieldUnitRep K) 2] at h
    exact ⟨congrArg (fun a : cocycles (FieldUnitRep K) 2 ⟶
      ModuleCat.of ℤ ((Fin 3 → Gal K) → FieldUnitRep K) => a z) h,hz⟩⟩

theorem fieldUnit_orbit (u : FieldUnitRep K) :
    IsLocallyConstant (fun g : Gal K => (FieldUnitRep K).ρ g u) := by
  let coeff (a : FieldUnitRep K) : AlgebraicClosure K := (a.toMul : AlgebraicClosure K)
  apply IsLocallyConstant.desc _ coeff
  · have h (g : Gal K) : coeff ((FieldUnitRep K).ρ g u) = (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from g) (coeff u) := by
      change ((((FieldUnitRep K).ρ g u).toMul):(AlgebraicClosure K)) = _
      rw [show FieldUnitRep K = Rep.ofMulDistribMulAction (Gal K) (AlgebraicClosure K)ˣ from rfl,
        Rep.ofMulDistribMulAction_ρ_apply_apply]
      simp only [AlgEquiv.smul_units_def,Units.coe_map,MonoidHom.coe_ofClass] <;> rfl
    have he : (fun g : Gal K => coeff ((FieldUnitRep K).ρ g u)) =
        fun g : Gal K => (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from g) (coeff u) := funext h
    rw [he]
    exact field_coordinate_locally_constant (coeff u)
  · intro a b h
    exact congrArg Additive.ofMul (Units.ext h)

private theorem action_lc {X : Type} [TopologicalSpace X]
    (g : X → Gal K) (hg : Continuous g) (u : X → FieldUnitRep K) (hu : IsLocallyConstant u) :
    IsLocallyConstant (fun x => (FieldUnitRep K).ρ (g x) (u x)) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro x
  obtain ⟨U,hU,hx,he⟩ := (IsLocallyConstant.iff_exists_open _).mp hu x
  obtain ⟨V,hV,hgx,hv⟩ := (IsLocallyConstant.iff_exists_open _).mp (fieldUnit_orbit K (u x)) (g x)
  refine ⟨U ∩ g ⁻¹' V,hU.inter (hV.preimage hg),⟨hx,hgx⟩,?_⟩
  intro y hy
  change (FieldUnitRep K).ρ (g y) (u y) = (FieldUnitRep K).ρ (g x) (u x)
  rw [he y hy.1]
  exact hv (g y) hy.2

theorem native_d₁_apply (u : (Fin 1 → Gal K) → FieldUnitRep K) (s : Fin 2 → Gal K) :
    inhomogeneousCochains.d (FieldUnitRep K) 1 u s =
      (FieldUnitRep K).ρ (s 0) (u fun _ => s 1) -
        u (fun _ => s 0*s 1) + u (fun _ => s 0) := by
  change (FieldUnitRep K).ρ (s 0) (u fun i => s i.succ) +
    (Finset.univ.sum fun i : Fin 2 =>
      (-1:ℤ)^((i:ℕ)+1) • u (Fin.contractNth i (· * ·) s)) = _
  have ct : (fun i : Fin 1 => s i.succ) = fun _ => s 1 := by
    funext i
    have h : i=(0:Fin 1) := Subsingleton.elim _ _
    subst i
    rfl
  have c₀ : Fin.contractNth (0:Fin 2) (· * ·) s = fun _ => s 0*s 1 := by
    funext i
    have h : i=(0:Fin 1) := Subsingleton.elim _ _
    subst i
    rfl
  have c₁ : Fin.contractNth (1:Fin 2) (· * ·) s = fun _ => s 0 := by
    funext i
    have h : i=(0:Fin 1) := Subsingleton.elim _ _
    subst i
    rfl
  rw [Fin.sum_univ_two,ct,c₀,c₁]
  simp only [Fin.val_zero,Fin.val_one,zero_add]
  norm_num <;> abel

theorem native_d₁_lc (u : (Fin 1 → Gal K) → FieldUnitRep K) (hu : IsLocallyConstant u) :
    IsLocallyConstant (inhomogeneousCochains.d (FieldUnitRep K) 1 u) := by
  let v := fun g : Gal K => u (fun _ => g)
  have hv : IsLocallyConstant v :=
    hu.comp_continuous (continuous_pi fun _ : Fin 1 => continuous_id)
  have h₀ : IsLocallyConstant (fun s : Fin 2 → Gal K => (FieldUnitRep K).ρ (s 0) (v (s 1))) :=
    action_lc K (fun s => s 0) (continuous_apply 0) (fun s => v (s 1))
      (hv.comp_continuous (continuous_apply 1))
  have h₁ : IsLocallyConstant (fun s : Fin 2 → Gal K => v (s 0*s 1)) :=
    hv.comp_continuous ((continuous_apply 0).mul (continuous_apply 1))
  have h₂ : IsLocallyConstant (fun s : Fin 2 → Gal K => v (s 0)) :=
    hv.comp_continuous (continuous_apply 0)
  have he : (inhomogeneousCochains.d (FieldUnitRep K) 1 u : (Fin 2 → Gal K) → FieldUnitRep K) =
      fun s => (FieldUnitRep K).ρ (s 0) (v (s 1)) - v (s 0*s 1) + v (s 0) :=
    funext (native_d₁_apply K u)
  rw [he]
  exact ((h₀.prodMk h₁).prodMk h₂).comp fun p => p.1.1-p.1.2+p.2

private theorem native_d₁_closed (u : (Fin 1 → Gal K) → FieldUnitRep K) :
    inhomogeneousCochains.d (FieldUnitRep K) 2
      (inhomogeneousCochains.d (FieldUnitRep K) 1 u) = 0 := by
  have h := inhomogeneousCochains.d_comp_d (A := FieldUnitRep K) (n := 1)
  exact congrArg (fun a : ModuleCat.of ℤ ((Fin 1 → Gal K) → FieldUnitRep K) ⟶
    ModuleCat.of ℤ ((Fin 3 → Gal K) → FieldUnitRep K) => a u) h

def continuousBoundary : continuousOne K →+ continuousCycles K where
  toFun u := ⟨inhomogeneousCochains.d (FieldUnitRep K) 1 u.val,
    ⟨native_d₁_closed K u.val,native_d₁_lc K u.val u.property⟩⟩
  map_zero' := by apply Subtype.ext; exact map_zero (inhomogeneousCochains.d (FieldUnitRep K) 1)
  map_add' u v := by
    apply Subtype.ext
    exact map_add (inhomogeneousCochains.d (FieldUnitRep K) 1) u.val v.val

/-- Actual continuous cohomological H², not the algebraic Brauer
algebra quotient and not the ambient ordinary H². -/
abbrev ContH2 := continuousCycles K ⧸ (continuousBoundary K).range

abbrev classOf : continuousCycles K →+ ContH2 K :=
  QuotientAddGroup.mk' (continuousBoundary K).range

@[simp] theorem boundary_value (u : continuousOne K) :
    (continuousBoundary K u).val =
      inhomogeneousCochains.d (FieldUnitRep K) 1 u.val := rfl

theorem class_zero_iff (z : continuousCycles K) :
    classOf K z=0 ↔ ∃ u : continuousOne K,
      z.val = inhomogeneousCochains.d (FieldUnitRep K) 1 u.val := by
  rw [QuotientAddGroup.eq_zero_iff]
  change (∃ u : continuousOne K, continuousBoundary K u=z) ↔ _
  constructor
  · rintro ⟨u,rfl⟩
    exact ⟨u,boundary_value K u⟩
  · rintro ⟨u,hu⟩
    exact ⟨u,Subtype.ext hu.symm⟩

/-- Independence under an actual continuous one-cochain boundary. -/
theorem class_eq_of_boundary (z z' : continuousCycles K) (u : continuousOne K)
    (h : z.val - z'.val = inhomogeneousCochains.d (FieldUnitRep K) 1 u.val) :
    classOf K z = classOf K z' := by
  rw [← sub_eq_zero, ← map_sub, class_zero_iff]
  exact ⟨u,h⟩

end CTContinuousFieldHTwo318
