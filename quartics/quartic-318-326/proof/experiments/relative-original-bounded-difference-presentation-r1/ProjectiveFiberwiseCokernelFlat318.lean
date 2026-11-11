module
public import FreeFiberwiseCokernelFlat318
public section
noncomputable section
namespace ProjectiveFiberwiseCokernelFlat318
universe u
variable {R A B : Type u} [CommRing R]
  [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B]

/-- Stabilize a map from a projective source by its actual chosen free
retract. The extra component retains precisely the complementary summand;
it is not discarded when checking residue fibers. -/
lemma tensor_injective (f : A →ₗ[R] B)
    [Module.Projective R A] [Module.Projective R B]
    (hf : ∀ m : Ideal R, ∀ _ : m.IsMaximal,
      Function.Injective (f.baseChange (R ⧸ m)))
    (N : Type u) [AddCommGroup N] [Module R N] :
    Function.Injective (f.lTensor N) := by
  obtain ⟨i, hi⟩ := Module.projective_def'.mp (inferInstance : Module.Projective R A)
  let F := A →₀ R
  let π : F →ₗ[R] A := Finsupp.linearCombination R id
  have hπ : π.comp i = LinearMap.id := hi
  let j : F →ₗ[R] B × F := (f.comp π).prod (LinearMap.id-i.comp π)
  let p : B × F →ₗ[R] B := LinearMap.fst R B F
  let q : B × F →ₗ[R] F := LinearMap.snd R B F
  let a : B →ₗ[R] B × F := LinearMap.inl R B F
  have hp : p.comp j = f.comp π := by ext x; rfl
  have hq : q.comp j = LinearMap.id-i.comp π := by ext x; rfl
  have hji : j.comp i = a.comp f := by
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · change f (π (i x)) = f x
      rw [show π (i x)=x from LinearMap.congr_fun hπ x]
    · change i x-i (π (i x)) = 0
      rw [show π (i x)=x from LinearMap.congr_fun hπ x, sub_self]
  have hj : ∀ m : Ideal R, ∀ _ : m.IsMaximal,
      Function.Injective (j.baseChange (R ⧸ m)) := by
    intro m hm
    apply (LinearMap.ker_eq_bot).mp
    apply le_antisymm _ bot_le
    intro x hx
    change x=0
    have hx0 : j.baseChange (R ⧸ m) x=0 := hx
    have hxπ : π.baseChange (R ⧸ m) x=0 := by
      apply hf m hm
      rw [map_zero]
      calc
        f.baseChange (R ⧸ m) (π.baseChange (R ⧸ m) x) =
            p.baseChange (R ⧸ m) (j.baseChange (R ⧸ m) x) := by
          rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
            ← hp, LinearMap.baseChange_comp, LinearMap.comp_apply]
        _ = 0 := by rw [hx0, map_zero]
    have hc : x-i.baseChange (R ⧸ m) (π.baseChange (R ⧸ m) x)=0 := by
      calc
        x-i.baseChange (R ⧸ m) (π.baseChange (R ⧸ m) x) =
            (LinearMap.id-i.comp π).baseChange (R ⧸ m) x := by
          rw [LinearMap.baseChange_sub, LinearMap.baseChange_id,
            LinearMap.baseChange_comp]
          rfl
        _ = q.baseChange (R ⧸ m) (j.baseChange (R ⧸ m) x) := by
          rw [← hq, LinearMap.baseChange_comp, LinearMap.comp_apply]
        _ = 0 := by rw [hx0, map_zero]
    simpa only [hxπ, map_zero, sub_zero] using hc
  have hjN := FreeFiberwiseCokernelFlat318.tensor_injective j hj N
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm _ bot_le
  intro x hx
  change x=0
  have hx0 : f.lTensor N x=0 := hx
  have hix : i.lTensor N x=0 := by
    apply hjN
    rw [map_zero]
    calc
      j.lTensor N (i.lTensor N x) = a.lTensor N (f.lTensor N x) := by
        rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hji,
          LinearMap.lTensor_comp, LinearMap.comp_apply]
      _ = 0 := by rw [hx0, map_zero]
  have h := congrArg (π.lTensor N) hix
  rw [map_zero, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hπ,
    LinearMap.lTensor_id, LinearMap.id_apply] at h
  exact h

/-- Genuine fieldwise flatness for an exact cokernel of projective
modules over an arbitrary base. Ambient flatness is internally supplied
by projectivity; residue-field injectivity remains the actual map test. -/
lemma flat {Q : Type u} [AddCommGroup Q] [Module R Q]
    (f : A →ₗ[R] B) (q : B →ₗ[R] Q)
    (he : Function.Exact f q) (hq : Function.Surjective q)
    [Module.Projective R A] [Module.Projective R B]
    (hf : ∀ m : Ideal R, ∀ _ : m.IsMaximal,
      Function.Injective (f.baseChange (R ⧸ m))) : Module.Flat R Q :=
  UniversallyInjectiveCokernelFlat318.flat f q he hq (tensor_injective f hf)
end ProjectiveFiberwiseCokernelFlat318
