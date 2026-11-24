module
public import OriginalTwoMarkedTensorsR8_318
public import OriginalRawImageOnMark318
public import Mathlib.RingTheory.Localization.BaseChange
public section
noncomputable section
namespace OriginalMarkedTraitInverse318
open scoped TensorProduct Pointwise

variable {S E H : Type*} [CommRing S] [Field E] [Algebra S E] [AddCommGroup H] [Module S H]

/-- One affine chart at the closed point of the number-ring mark. A basis of
the relative dualizing square on *this chart only* presents it by R.
The same mark reads its integral coefficients in the fixed generic line.
The raw map may have nonunit image at bad primes; no division is built in. -/
structure Chart (F : H →ₗ[S] E) (phys : Fin 2 → E) (m : Ideal S) [m.IsPrime] where
  A : Type
  [ring : CommRing A]
  mark : A →+* Localization.AtPrime m
  raw : Localization.AtPrime m ⊗[S] H →ₗ[Localization.AtPrime m] Localization.AtPrime m
  read : Localization.AtPrime m →ₗ[S] E
  generic : ∀h, read (raw (1 ⊗ₜ[S] h)) = F h
  image_eq : raw.range=(210:Localization.AtPrime m) • (⊤:Submodule _ _)
  sectionValue : Fin 2→A
  same : ∀i,read (mark (sectionValue i))=phys i

/-- A common denominator outside the actual closed prime is forced by
the localization of the Hodge tensor module. No freeness, Dedekind
decomposition, or principal generator of the global marked Hodge line. -/
theorem clears {F : H →ₗ[S] E} {phys : Fin 2 → E} {m : Ideal S} [m.IsPrime]
    (C : Chart F phys m) (i : Fin 2) :
    ∃ s:S,s∉m ∧ s • ((210:E)*phys i) ∈ F.range := by
  let A := Localization.AtPrime m
  obtain ⟨v,hv⟩ : (210:A) • C.mark (C.sectionValue i) ∈ C.raw.range := by
    rw [C.image_eq]
    exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
  obtain ⟨⟨h,s⟩,e⟩ := IsLocalizedModule.surj m.primeCompl (TensorProduct.mk S A H 1) v
  have vv : C.read (C.raw v)=(210:E)*phys i := by
    rw [hv]; change C.read ((210:A) * _) = _
    rw [show (210:A) * C.mark (C.sectionValue i) = (210:ℕ) • C.mark (C.sectionValue i) by simp [nsmul_eq_mul], map_nsmul,C.same]
    simp [nsmul_eq_mul]
  refine ⟨s,s.2,h,?_⟩
  change (s:S) • v=1 ⊗ₜ[S] h at e
  rw [←C.generic,←e,←vv,C.raw.map_smul_of_tower,map_smul]

/-- Gluing at the finite mark, not on the fine curve: even if the mark
meets a different source chart at every closed point, both multiplied
physical coefficients come from actual *global* marked Hodge tensors. -/
theorem assemble (F : H →ₗ[S] E) (phys : Fin 2 → E)
    (germs : ∀m:Ideal S,∀hm:m.IsMaximal, letI : m.IsPrime := hm.isPrime
      Nonempty (Chart F phys m)) :
    ∃ z : Fin 2→H,∀i,F (z i)=(210:E)*phys i := by
  classical
  have lift (i : Fin 2) : (210:E)*phys i ∈ F.range := by
    let b := (210:E)*phys i
    let J : Ideal S := F.range.comap (LinearMap.toSpanSingleton S E b)
    by_contra no
    have nt : J≠⊤ := by
      intro e
      have h : (1:S)∈J := e ▸ Submodule.mem_top
      exact no (by simpa [J,b] using h)
    obtain ⟨m,hm,le⟩ := J.exists_le_maximal nt
    let : m.IsPrime := hm.isPrime
    obtain ⟨s,hs,mem⟩ := clears (germs m hm).some i
    exact hs (le (show s∈J from mem))
  choose z eq using lift
  exact ⟨z,eq⟩

end OriginalMarkedTraitInverse318
