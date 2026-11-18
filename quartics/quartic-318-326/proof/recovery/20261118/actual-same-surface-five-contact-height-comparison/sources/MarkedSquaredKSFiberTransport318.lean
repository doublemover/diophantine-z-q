module
public import DirectHodgeSectionHeight318
public section
noncomputable section
namespace MarkedSquaredKSFiberTransport318
open NumberField SectionHeight318 DirectHodgeSectionHeight318
variable {L U V : Type*} [Field L] [NumberField L]
  [AddCommGroup U] [Module L U] [AddCommGroup V] [Module L V]
variable (hSq : L ≃ₗ[L] U) (e : L ≃ₗ[L] V) (ψ : U ≃ₗ[L] V)

/-- κ compares the genuine SQUARED Hodge frame and the actual bicanonical
frame via the specified generic KS isomorphism. No global or fiberwise
square root of the Kodaira–Spencer isomorphism is required. -/
@[expose] def kappa : L := e.symm (ψ (hSq 1))
theorem kappa_ne : kappa hSq e ψ ≠ 0 := by
  intro hk
  have h1 := e.symm.injective (hk.trans e.symm.map_zero.symm)
  have h2 := ψ.injective (h1.trans ψ.map_zero.symm)
  exact one_ne_zero (hSq.injective (h2.trans hSq.map_zero.symm))

theorem map_coordinate (z : L) : ψ (hSq z)=e (z*kappa hSq e ψ) := by
  have hz : hSq z=z • hSq 1 := by rw [←hSq.map_smul,smul_eq_mul,mul_one]
  rw [hz,map_smul,←smul_eq_mul,map_smul,kappa,LinearEquiv.apply_symm_apply]

theorem marked_value (a : L) : ψ (hSq (a/kappa hSq e ψ))=e a := by
  rw [map_coordinate,div_mul_cancel₀ _ (kappa_ne hSq e ψ)]

/-- The local integral square lattice of the SPECIFIED Hodge frame. This
notation does not define that frame or the geometric KS map. -/
@[expose] def squareBall (H : FrameNorms L) (w : FinitePlace L) : Set U :=
  hSq '' {z : L | w z*(H.finiteNorm w)^2≤1}

/-- Only the inclusion 210*C ⊆ ψ(Hodge_integral²) is used. The actual
maximal-stack image equality implies that inclusion on the integral point;
regularity of a different model does not. -/
theorem finite_from_image (H : FrameNorms L) (w : FinitePlace L) (C : Set V)
    (hKS : ∀ x ∈ C,(210:L) • x ∈ ψ '' squareBall hSq H w) (a : L) (ha : e a∈C) :
    w ((210:L)*(a/kappa hSq e ψ))*(H.finiteNorm w)^2≤1 := by
  obtain ⟨y,⟨z,hz,rfl⟩,hy⟩ := hKS (e a) ha
  have hx : ψ (hSq ((210:L)*(a/kappa hSq e ψ))) = (210:L) • e a := by
    change ψ (hSq ((210:L) • (a/kappa hSq e ψ)))=_
    rw [map_smul,map_smul,marked_value]
  have he := hSq.injective (ψ.injective (hy.trans hx.symm))
  exact he ▸ hz

/-- Characteristic-zero archimedean comparison is literally Yuan's
isometry evaluated on the normalized coefficient, not a presumed equality
of two unrelated chosen frames. -/
theorem arch_from_isometry (H : FrameNorms L) (w : InfinitePlace L)
    (Pet : V → ℝ) (hisom : ∀ z : L,Pet (ψ (hSq z))=w z*(H.arch w)^2)
    (a : L) (C : ℝ) (ha : Pet (e a)≤C) :
    w (a/kappa hSq e ψ)*(H.arch w)^2≤C := by
  rw [←hisom,marked_value]
  exact ha

/-- Both original coordinates are transported by the SAME κ over the
common auxiliary field. This theorem requires the actual integral-section
memberships, the actual KS/image and metric facts, and the Petersson bounds.
It neither infers nor postulates numerical Hodge bounds for those sections. -/
theorem height_from_marked_sections {F : Type*} [Field F] [CharZero F]
    (ι : F →+* L) (a₀ a₁ : F) (u v : ℤ) (h₀ : a₀≠0)
    (hr : a₁=((32*((u:ℚ)/(v:ℚ)):ℚ):F)*a₀)
    (H : FrameNorms L) (hYuan : ℝ) (hdeg : H.normalizedDegree=hYuan)
    (C : FinitePlace L → Set V)
    (hKS : ∀ (w : FinitePlace L) x, x∈C w → (210:L) • x ∈ ψ '' squareBall hSq H w)
    (hC : ∀ (w : FinitePlace L) (i : Fin 2),e (ι (![a₀,a₁] i))∈C w)
    (Pet : InfinitePlace L → V → ℝ)
    (hisom : ∀ (w : InfinitePlace L) (z : L),Pet w (ψ (hSq z))=w z*(H.arch w)^2)
    (hPet : ∀ (w : InfinitePlace L) (i : Fin 2),Pet w (e (ι (![a₀,a₁] i)))≤ContactMetricSections318.sectionBound) :
    ContactHeight318.pointHeight u v<2*(hYuan-Real.log Real.pi)+120 := by
  let κ := kappa hSq e ψ
  have hκ : κ≠0 := kappa_ne hSq e ψ
  have h0 : ι a₀ / κ≠0 := div_ne_zero (map_ne_zero ι h₀) hκ
  have hratio : ι a₁/κ = ((32*((u:ℚ)/(v:ℚ)):ℚ):L)*(ι a₀/κ) := by
    rw [hr,map_mul,map_ratCast]
    ring
  have hpair (i : Fin 2) : ![ι a₀/κ,ι a₁/κ] i = ι (![a₀,a₁] i)/κ := by fin_cases i <;> rfl
  apply height_from_local_hodge_inequalities H hYuan hdeg u v _ _ h0 hratio
  · intro w i
    rw [hpair]
    exact arch_from_isometry hSq e ψ H w (Pet w) (hisom w) _ _ (hPet w i)
  · intro w i
    rw [hpair]
    exact finite_from_image hSq e ψ H w (C w) (hKS w) _ (hC w i)

end MarkedSquaredKSFiberTransport318
