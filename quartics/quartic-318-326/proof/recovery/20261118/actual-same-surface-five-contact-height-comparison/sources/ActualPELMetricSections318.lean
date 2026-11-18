module
public import ActualPELPointSectionsHeight318
public import RefinedContactRealization318
public section
noncomputable section
namespace ActualPELMetricSections318
open NumberField SectionHeight318 DirectHodgeSectionHeight318 MarkedSquaredKSFiberTransport318
open ActualPELPointSectionsHeight318
set_option maxHeartbeats 1000000

/-- In the bicanonical frame ψ(h²), the scalar describing each marked
section is *exactly* its Hodge-square coefficient. C is the true integral
canonical-square lattice in that frame. The actual finite KS statement is an
equality of embedded sets/lattices, not a metric manufactured from a height.
The Pet norm and original sections are supplied on that SAME fiber. -/
structure Datum (L : Type*) [Field L] [NumberField L] (u v : ℤ) (hYuan : ℝ) where
  H : FrameNorms L
  degree : H.normalizedDegree=hYuan
  z₀ : L
  z₁ : L
  nz : z₀≠0
  ratio : z₁=((32*((u:ℚ)/(v:ℚ)):ℚ):L)*z₀
  C : FinitePlace L → Set L
  finite_image : ∀ w : FinitePlace L,
    {z : L | w z*(H.finiteNorm w)^2 ≤ 1} = (fun x : L => (210:L)*x) '' C w
  integral : ∀ (w : FinitePlace L) (i : Fin 2), ![z₀,z₁] i ∈ C w
  Pet : InfinitePlace L → L → ℝ
  isometry : ∀ (w : InfinitePlace L) (z : L), Pet w z=w z*(H.arch w)^2
  supremum : ∀ (w : InfinitePlace L) (i : Fin 2), Pet w (![z₀,z₁] i)≤ContactMetricSections318.sectionBound

variable {L : Type*} [Field L] [NumberField L] {u v : ℤ} {y : ℝ}

/-- In this induced common generic frame the comparison gauge is not just
an auxiliary numerical trick: its actual unit ball is exactly the provided
integral bicanonical lattice. This proof uses the reverse finite KS inclusion
as well as the forward one even at residue characteristics dividing 210. -/
theorem actual_ball (D : Datum L u v y) (w : FinitePlace L) (z : L) :
    z∈D.C w ↔ w z*(comparisonFrame D.H).finiteNorm w≤1 := by
  have he : w z*(comparisonFrame D.H).finiteNorm w=w ((210:L)*z)*(D.H.finiteNorm w)^2 := by
    rw [comparison_finite,map_mul];ring
  rw [he]
  change z∈D.C w ↔ (210:L)*z∈{a : L | w a*(D.H.finiteNorm w)^2≤1}
  rw [D.finite_image]
  constructor
  · intro h; exact ⟨z,h,rfl⟩
  · rintro ⟨x,hx,heq⟩
    exact (mul_left_cancel₀ (by norm_num : (210:L)≠0) heq) ▸ hx

/-- Genuine producer for the existing literal refined record, not merely a
numerical conclusion. The scalar alignment is ψ(h²), not a square root of ψ. -/
@[expose] def metricSections (D : Datum L u v y) : RefinedContactRealization318.MetricSections L u v y where
  a₀ := D.z₀
  a₁ := D.z₁
  a₀_ne := D.nz
  ratio := D.ratio
  canonical := comparisonFrame D.H
  hodge := D.H
  hodge_degree := D.degree
  ks_image := cancel D.H
  arch_bound w i := by rw [comparison_arch,←D.isometry]; exact D.supremum w i
  finite_integral w i := (actual_ball D w _).mp (D.integral w i)

section Vector
variable {U V : Type*} [AddCommGroup U] [Module L U] [AddCommGroup V] [Module L V]
variable (hSq : L ≃ₗ[L] U) (ψ : U ≃ₗ[L] V)
/-- Extract the scalar data from the actual two vectors of one PEL point and
the genuine map on its two square lines. No choice of root-coordinate frame
or square extension of the original point field is used. -/
@[expose] def fromVectors (H : FrameNorms L) (deg : H.normalizedDegree=y) (s₀ s₁ : V)
    (hs₀ : s₀≠0) (hr : s₁=((32*((u:ℚ)/(v:ℚ)):ℚ):L) • s₀)
    (C : FinitePlace L → Set V)
    (hKS : ∀ w : FinitePlace L, ψ '' squareBall hSq H w = (fun x : V => (210:L) • x) '' C w)
    (hmem : ∀ (w : FinitePlace L) (i : Fin 2), ![s₀,s₁] i∈C w)
    (Pet : InfinitePlace L → V → ℝ)
    (hisom : ∀ (w : InfinitePlace L) z, Pet w (ψ (hSq z))=w z*(H.arch w)^2)
    (hsup : ∀ (w : InfinitePlace L) (i : Fin 2),Pet w (![s₀,s₁] i)≤ContactMetricSections318.sectionBound) :
    Datum L u v y := by
  let z := coordinate hSq ψ
  let f := hSq.trans ψ
  have finv (x : V) : f (z x)=x := evaluates hSq ψ x
  have hpair (i : Fin 2) : ![z s₀,z s₁] i=z (![s₀,s₁] i) := by fin_cases i <;> rfl
  refine { H:=H,degree:=deg,z₀:=z s₀,z₁:=z s₁,
    nz:=fun he => hs₀ (z.injective (he.trans z.map_zero.symm)),
    ratio:=by rw [hr,map_smul,smul_eq_mul],
    C:=fun w => f ⁻¹' C w, finite_image:=?_,integral:=?_,
    Pet:=fun w x => Pet w (f x),isometry:=hisom,supremum:=?_ }
  · intro w
    ext x
    constructor
    · intro hx
      have hh : ψ (hSq x)∈ψ '' squareBall hSq H w := ⟨hSq x,⟨x,hx,rfl⟩,rfl⟩
      rw [hKS] at hh
      obtain ⟨b,hb,he⟩ := hh
      refine ⟨z b,?_,?_⟩
      · change f (z b)∈C w
        rwa [finv]
      · apply f.injective
        change f ((210:L) • z b)=f x
        rw [map_smul,finv]
        exact he
    · rintro ⟨b,hb,rfl⟩
      have hh : (210:L) • f b∈(fun a : V => (210:L) • a) '' C w := ⟨f b,hb,rfl⟩
      rw [←hKS] at hh
      obtain ⟨h,⟨q,hq,rfl⟩,he⟩ := hh
      have hq' : f q=f ((210:L)*b) := by
        change ψ (hSq q)=f ((210:L) • b)
        rw [map_smul]
        exact he
      exact (f.injective hq') ▸ hq
  · intro w i
    change f (![z s₀,z s₁] i)∈C w
    rw [hpair,finv]
    exact hmem w i
  · intro w i
    change Pet w (f (![z s₀,z s₁] i))≤_
    rw [hpair,finv]
    exact hsup w i
end Vector
end ActualPELMetricSections318
