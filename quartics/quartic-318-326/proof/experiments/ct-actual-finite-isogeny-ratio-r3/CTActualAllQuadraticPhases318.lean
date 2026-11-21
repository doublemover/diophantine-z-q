module
public import CTActualQuadraticRootSigns318
public import CTActualClosedGaloisHilbert90318
import all Mathlib.FieldTheory.AbsoluteGaloisGroup
import all CTActualQuadraticRootSigns318
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.Tactic.NormNum
public section

noncomputable section

namespace CTActualAllQuadraticPhases318

open CTActualQuadraticRootSigns318 CTFieldPrimitiveRestriction318
open CTActualClosedGaloisHilbert90318

variable (K : Type) [Field K] [CharZero K]
local notation "A" => AlgebraicClosure K
local notation "G" => (A ≃ₐ[K] A)

private def sign (b : Bool) : Aˣ := if b then -1 else 1

private theorem sign_xor (a b : Bool) : sign K (xor a b)=sign K a*sign K b := by
  cases a <;> cases b <;> apply Units.ext <;> simp [sign,xor]

private theorem sign_fixed (g : G) (b : Bool) : g • sign K b=sign K b := by
  cases b <;> apply Units.ext <;>
    simp [sign,AlgEquiv.smul_units_def,Units.coe_map,MonoidHom.coe_ofClass]

/-- Every genuine locally constant quadratic character in the actual
Krull topology is the scalar Kummer phase of a base-field squareclass.
Uses the same absolute group and the closed Hilbert 90 theorem at ⊤,
not finite character enumeration or a Selmer finiteness input. -/
theorem character_is_actual_phase (χ : Gal K → Bool) (hLC : IsLocallyConstant χ)
    (hχ : ∀ g h : Gal K, χ (g*h)=xor (χ g) (χ h)) :
    ∃ a : Kˣ, ∃ r : Aˣ, (r:A)^2=algebraMap K A (a:K) ∧
      ∀ g : Gal K, phase K r g=χ g := by
  let I : Subgroup G := ⊤
  let j : I → Gal K := fun s => (show Gal K from (s:G))
  let c : I → Aˣ := fun s => sign K (χ (j s))
  have hTop : IsClosed (I : Set G) := by
    change IsClosed (Set.univ : Set G)
    exact isClosed_univ
  have hJ : Continuous j := continuous_subtype_val
  have hcLC : IsLocallyConstant c := (hLC.comp_continuous hJ).comp (sign K)
  have hc (g h : I) : c (g*h)=(g:G) • c h*c g := by
    change sign K (χ (j g*j h))=(g:G) • sign K (χ (j h))*sign K (χ (j g))
    rw [hχ,sign_xor,sign_fixed]
    exact mul_comm _ _
  obtain ⟨r,hr⟩ := actual_closed_hilbert90 K I hTop c hcLC hc
  have hAction (g : Gal K) : act K g (r:A)=fieldSign K (χ g) (r:A) := by
    let s : I := ⟨(show G from g),by simp [I]⟩
    have he := congrArg (fun v : Aˣ => (v:A)) (hr s)
    have hu : act K g (r:A)/(r:A)=(sign K (χ g):Aˣ) := by
      simpa only [c,s,j,Units.val_div_eq_div_val,AlgEquiv.smul_units_def,
        Units.coe_map,MonoidHom.coe_ofClass,act] using he
    have hv := (div_eq_iff r.ne_zero).mp hu
    cases hb : χ g <;> simp [hb,fieldSign,sign] at hv ⊢ <;> exact hv
  have hFix (g : G) : g ((r:A)^2)=(r:A)^2 := by
    let s : Gal K := g
    have he := hAction s
    change g (r:A)=fieldSign K (χ s) (r:A) at he
    rw [map_pow,he]
    cases hb : χ s <;> simp [hb,fieldSign]
  obtain ⟨a,ha⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k:=K) ((r:A)^2)).mpr hFix
  have ha0 : a≠0 := by
    intro h
    rw [h,map_zero] at ha
    exact pow_ne_zero 2 r.ne_zero ha.symm
  refine ⟨Units.mk0 a ha0,r,ha.symm,?_⟩
  intro g
  have h := hAction g
  cases hb : χ g
  · have he : act K g (r:A)=(r:A) := by simpa [hb,fieldSign] using h
    simp [phase,he,hb]
  · have he : act K g (r:A)= -(r:A) := by simpa [hb,fieldSign] using h
    have hne : act K g (r:A)≠(r:A) := by
      intro hfix
      have hsign : -(r:A)=(r:A) := he.symm.trans hfix
      have hz : (2:A)*(r:A)=0 := calc
        _=(r:A)+(r:A) := two_mul _
        _= -(r:A)+(r:A) := congrArg (fun z : A => z+(r:A)) hsign.symm
        _=0 := neg_add_cancel _
      exact mul_ne_zero (by norm_num) r.ne_zero hz
    simp [phase,hne,hb]

end CTActualAllQuadraticPhases318

#print axioms CTActualAllQuadraticPhases318.character_is_actual_phase
