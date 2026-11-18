module
public import MarkedSquaredKSFiberTransport318
public section
noncomputable section
namespace ActualPELPointSectionsHeight318
open NumberField SectionHeight318 DirectHodgeSectionHeight318 MarkedSquaredKSFiberTransport318
variable {L U V : Type*} [Field L] [NumberField L]
  [AddCommGroup U] [Module L U] [AddCommGroup V] [Module L V]
variable (hSq : L ≃ₗ[L] U) (ψ : U ≃ₗ[L] V)

/-- Literal inverse image of an evaluated bicanonical vector, expressed in
the Hodge-square frame. No matching bicanonical frame or square root of ψ
is chosen. In applications these are the two actual sections on the same
maximal-stack point as the given Hodge line. -/
@[expose] def coordinate : V ≃ₗ[L] L := ψ.symm.trans hSq.symm
theorem evaluates (s : V) : ψ (hSq (coordinate hSq ψ s))=s := by
  simp [coordinate]

/-- The numerical contact-height bound depends only on the ratio of the
two ACTUAL sections at the marked point. The auxiliary number field may
be any field of integral definition for that object, not necessarily the
original four-radical point field or the controlled isogeny field. -/
theorem height_at_same_point (H : FrameNorms L) (hYuan : ℝ) (hdeg : H.normalizedDegree=hYuan)
    (u v : ℤ) (s₀ s₁ : V) (h₀ : s₀≠0)
    (hr : s₁=((32*((u:ℚ)/(v:ℚ)):ℚ):L) • s₀)
    (C : FinitePlace L → Set V)
    (hKS : ∀ (w : FinitePlace L) x, x∈C w→(210:L) • x∈ψ '' squareBall hSq H w)
    (hC : ∀ (w : FinitePlace L) (i : Fin 2),![s₀,s₁] i∈C w)
    (Pet : InfinitePlace L → V → ℝ)
    (hisom : ∀ (w : InfinitePlace L) (z : L),Pet w (ψ (hSq z))=w z*(H.arch w)^2)
    (hPet : ∀ (w : InfinitePlace L) (i : Fin 2),Pet w (![s₀,s₁] i) ≤ ContactMetricSections318.sectionBound) :
    ContactHeight318.pointHeight u v<2*(hYuan-Real.log Real.pi)+120 := by
  let z := coordinate hSq ψ
  have h0 : z s₀≠0 := by
    intro hz
    exact h₀ (z.injective (hz.trans z.map_zero.symm))
  have hratio : z s₁=((32*((u:ℚ)/(v:ℚ)):ℚ):L)*z s₀ := by
    rw [hr,map_smul,smul_eq_mul]
  have hpair (i : Fin 2) : ![z s₀,z s₁] i=z (![s₀,s₁] i) := by fin_cases i <;> rfl
  apply height_from_local_hodge_inequalities H hYuan hdeg u v _ _ h0 hratio
  · intro w i
    rw [hpair,←hisom]
    change Pet w (ψ (hSq (coordinate hSq ψ (![s₀,s₁] i)))) ≤ _
    rw [evaluates]
    exact hPet w i
  · intro w i
    rw [hpair]
    obtain ⟨y,⟨x,hx,rfl⟩,hy⟩ := hKS w _ (hC w i)
    have he : ψ (hSq ((210:L)*z (![s₀,s₁] i)))=(210:L) • ![s₀,s₁] i := by
      change ψ (hSq ((210:L) • coordinate hSq ψ (![s₀,s₁] i)))=_
      rw [map_smul,map_smul,evaluates]
    have hz := hSq.injective (ψ.injective (hy.trans he.symm))
    exact hz ▸ hx
end ActualPELPointSectionsHeight318
