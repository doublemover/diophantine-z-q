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
  let U (a : FieldUnitRep K) : (AlgebraicClosure K)ˣ :=
    (show Additive ((AlgebraicClosure K)ˣ) from a).toMul
  let coeff (a : FieldUnitRep K) : AlgebraicClosure K := (U a : AlgebraicClosure K)
  apply IsLocallyConstant.desc _ coeff
  · have h (g : Gal K) : coeff ((FieldUnitRep K).ρ g u) =
        (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from g) (coeff u) := by
      let σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := g
      change ((σ • U u : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)=σ (U u : AlgebraicClosure K)
      rw [AlgEquiv.smul_units_def,Units.coe_map] <;> rfl
    have he : (fun g : Gal K => coeff ((FieldUnitRep K).ρ g u)) =
        fun g : Gal K => (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from g) (coeff u) := funext h
    rw [he]
    exact field_coordinate_locally_constant (coeff u)
  · intro a b h
    change (U a : AlgebraicClosure K)=(U b : AlgebraicClosure K) at h
    have huv : U a=U b := Units.ext h
    exact congrArg (fun v : (AlgebraicClosure K)ˣ => (Additive.ofMul v : FieldUnitRep K)) huv

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
    IsLocallyConstant
      (fun s : Fin 2 → Gal K => inhomogeneousCochains.d (FieldUnitRep K) 1 u s) := by
  let v : Gal K → FieldUnitRep K := fun g => u (fun _ => g)
  have hdiag : Continuous (fun g : Gal K => (fun _ : Fin 1 => g)) :=
    continuous_pi fun _ => continuous_id
  have hv : IsLocallyConstant v := hu.comp_continuous hdiag
  let g₀ : (Fin 2 → Gal K) → Gal K := fun s => s 0
  let g₁ : (Fin 2 → Gal K) → Gal K := fun s => s 1
  have hg₀ : Continuous g₀ := continuous_apply 0
  have hg₁ : Continuous g₁ := continuous_apply 1
  have h₀ : IsLocallyConstant (fun s => (FieldUnitRep K).ρ (g₀ s) (v (g₁ s))) :=
    action_lc K g₀ hg₀ (v ∘ g₁) (hv.comp_continuous hg₁)
  have h₁ : IsLocallyConstant (fun s => v (g₀ s*g₁ s)) := hv.comp_continuous (hg₀.mul hg₁)
  have h₂ : IsLocallyConstant (fun s => v (g₀ s)) := hv.comp_continuous hg₀
  let F (p : (FieldUnitRep K × FieldUnitRep K) × FieldUnitRep K) : FieldUnitRep K :=
    p.1.1-p.1.2+p.2
  have hsum : IsLocallyConstant (fun s =>
      (FieldUnitRep K).ρ (g₀ s) (v (g₁ s)) - v (g₀ s*g₁ s) + v (g₀ s)) :=
    ((h₀.prodMk h₁).prodMk h₂).comp F
  have he : (fun s : Fin 2 → Gal K => inhomogeneousCochains.d (FieldUnitRep K) 1 u s) =
      fun s => (FieldUnitRep K).ρ (g₀ s) (v (g₁ s)) - v (g₀ s*g₁ s) + v (g₀ s) :=
    funext (native_d₁_apply K u)
  exact he.symm ▸ hsum

private theorem native_d₁_closed (u : (Fin 1 → Gal K) → FieldUnitRep K) :
    inhomogeneousCochains.d (FieldUnitRep K) 2
      (inhomogeneousCochains.d (FieldUnitRep K) 1 u) = 0 := by
  have h := inhomogeneousCochains.d_comp_d (A := FieldUnitRep K) (n := 1)
  exact congrArg (fun a : ModuleCat.of ℤ ((Fin 1 → Gal K) → FieldUnitRep K) ⟶
    ModuleCat.of ℤ ((Fin 3 → Gal K) → FieldUnitRep K) => a u) h

def continuousBoundary : continuousOne K →+ continuousCycles K where
  toFun u := ⟨inhomogeneousCochains.d (FieldUnitRep K) 1 u.val,
    ⟨native_d₁_closed K u.val,native_d₁_lc K u.val u.property⟩⟩
  map_zero' := by
    apply Subtype.ext
    let d : ((Fin 1 → Gal K) → FieldUnitRep K) →ₗ[ℤ] ((Fin 2 → Gal K) → FieldUnitRep K) :=
      (inhomogeneousCochains.d (FieldUnitRep K) 1).hom
    change d 0=0
    exact d.map_zero
  map_add' u v := by
    apply Subtype.ext
    let d : ((Fin 1 → Gal K) → FieldUnitRep K) →ₗ[ℤ] ((Fin 2 → Gal K) → FieldUnitRep K) :=
      (inhomogeneousCochains.d (FieldUnitRep K) 1).hom
    change d (u.val+v.val)=d u.val+d v.val
    exact d.map_add u.val v.val

/-- Actual continuous cohomological H², not the algebraic Brauer
algebra quotient and not the ambient ordinary H². -/
abbrev ContH2 := continuousCycles K ⧸ (continuousBoundary K).range

abbrev classOf : continuousCycles K →+ ContH2 K :=
  QuotientAddGroup.mk' (continuousBoundary K).range

@[simp] theorem boundary_value (u : continuousOne K) :
    (continuousBoundary K u).val =
      inhomogeneousCochains.d (FieldUnitRep K) 1 u.val := by rfl

theorem class_zero_iff (z : continuousCycles K) :
    classOf K z=0 ↔ ∃ u : continuousOne K,
      z.val = inhomogeneousCochains.d (FieldUnitRep K) 1 u.val := by
  have hz := QuotientAddGroup.eq_zero_iff (N:=(continuousBoundary K).range) z
  change classOf K z=0 ↔ (∃ u : continuousOne K, continuousBoundary K u=z) at hz
  refine hz.trans ?_
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
