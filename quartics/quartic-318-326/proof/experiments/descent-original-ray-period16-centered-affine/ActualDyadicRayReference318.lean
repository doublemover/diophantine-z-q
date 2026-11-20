module
public import Mathlib
public section
noncomputable section
namespace ActualDyadicRayReference318

abbrev D := ZMod 32

abbrev DyadicSite {J : Type*} (c : J→D) :=
  {z : D×D // ∀ j,z.1+c j*z.2^2=17}

/-- Exact dyadic factor on the original unshifted u,v. There is only
ONE allowed u for each v whose coefficient differences vanish, not
an independent dyadic probability for each polynomial output. -/
theorem slice_iff {J : Type*} (c : J→D) (i₀ : J) (u v : D) :
    (∀ j,u+c j*v^2=17) ↔
    u=17-c i₀*v^2 ∧ ∀ j,(c j-c i₀)*v^2=0 := by
  constructor
  · intro h
    refine ⟨by linear_combination h i₀,?_⟩
    intro j
    linear_combination h j-h i₀
  · rintro ⟨hu,hv⟩ j
    linear_combination hu+hv j

def vFibreEquiv {J : Type*} (c : J→D) (i₀ : J) :
    DyadicSite c ≃ {v : D // ∀ j,(c j-c i₀)*v^2=0} where
  toFun z := ⟨z.val.2,((slice_iff c i₀ z.val.1 z.val.2).mp z.property).2⟩
  invFun v := ⟨(17-c i₀*v.val^2,v.val),
    (slice_iff c i₀ _ v.val).mpr ⟨rfl,v.property⟩⟩
  left_inv z := Subtype.ext (Prod.ext
    ((slice_iff c i₀ z.val.1 z.val.2).mp z.property).1.symm rfl)
  right_inv v := Subtype.ext rfl

@[expose] def step8 (j : Fin 4) : D := ((8*j.val:ℕ):D)

theorem step8_injective : Function.Injective step8 := by
  decide

theorem step8_sq_zero (j : Fin 4) : (step8 j)^2=0 := by
  fin_cases j <;> decide

/-- Uniform nonempty dyadic fibre for the original reference norm.
It includes all four v=0,8,16,24, before applying any odd or prime
condition. The true dyadic base density is therefore at least 1/256. -/
def fourSites {J : Type*} (c : J→D) : Fin 4 ↪ DyadicSite c where
  toFun j := ⟨(17,step8 j),by
    intro i
    change 17+c i*(step8 j)^2=17
    rw [step8_sq_zero,mul_zero,add_zero]⟩
  inj' := by
    intro i j h
    exact step8_injective (congrArg (fun z : DyadicSite c => z.val.2) h)

theorem four_sites_lower {J : Type*} (c : J→D) :
    4≤Nat.card (DyadicSite c) := by
  classical
  letI : Fintype (DyadicSite c) := Fintype.ofFinite _
  have h := Fintype.card_le_of_injective (fourSites c) (fourSites c).injective
  simpa only [Fintype.card_fin,←Nat.card_eq_fintype_card] using h

end ActualDyadicRayReference318
