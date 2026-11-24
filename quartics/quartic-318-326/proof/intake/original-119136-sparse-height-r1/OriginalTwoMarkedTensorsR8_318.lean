module
public import OriginalHodgeModuleOverlap318
public import OriginalGlobalHodgeIdealHeight318
public section
noncomputable section

namespace OriginalTwoMarkedTensorsR8_318
open NumberField OriginalGlobalHodgeIdealHeight318 SelectedSameADirectBicanonicalHeight318
open scoped TensorProduct nonZeroDivisors Pointwise
variable {E H2 D2 : Type*} [Field E] [NumberField E] [AddCommGroup H2] [Module E H2]
    [AddCommGroup D2] [Module E D2]

/-- Read an actual Hodge tensor on the original open, in its common generic wedge. -/
def square {S M : Type*} [CommRing S] [Algebra S E] [AddCommGroup M] [Module S M]
    (f : M→ₗ[S]E) : M⊗[S]M →ₗ[S] E := (LinearMap.mul' S E).comp (TensorProduct.map f f)

omit [NumberField E] in
theorem square_mem {S M : Type*} [CommRing S] [Algebra S E] [AddCommGroup M] [Module S M]
    (f : M→ₗ[S]E) (z : M⊗[S]M) : square f z∈f.range*f.range := by
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    rw [square,LinearMap.comp_apply,TensorProduct.map_tmul,LinearMap.mul'_apply]
    exact Submodule.mul_mem_mul ⟨a,rfl⟩ ⟨b,rfl⟩
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

omit [NumberField E] in
theorem localized_square (S : Type*) [CommRing S] [Algebra (𝓞 E) S] [Algebra S E]
    [IsScalarTower (𝓞 E) S E] (I : FractionalIdeal (𝓞 E)⁰ E) :
    Submodule.span S (((I:Submodule (𝓞 E) E)*(I:Submodule (𝓞 E) E):Submodule (𝓞 E) E):Set E)=
      Submodule.span S (I:Set E)*Submodule.span S (I:Set E) := by
  rw [Submodule.mul_def,Submodule.span_span_of_tower,Submodule.span_mul_span]
  rfl

/-- Construct I from the actual full-33 overlap; feed actual integral tensors
from each marked open and a *single shared* pair of ordinary D² vectors into
the published R8 height consumer. The raw Ψ commutes on vectors (not given
norms). Its scalar B and the coefficient c are determined by these lines.
No global integral Hodge module, no common 3/11 basis and no finite inequality
are inputs. -/
theorem height
    (S3 S11 C : Type*) [CommRing S3] [CommRing S11] [CommRing C]
    [Algebra (𝓞 E) S3] [Algebra (𝓞 E) S11] [Algebra (𝓞 E) C]
    [Algebra S3 E] [Algebra S11 E] [Algebra C E] [Algebra S3 C] [Algebra S11 C]
    [IsScalarTower (𝓞 E) S3 E] [IsScalarTower (𝓞 E) S11 E] [IsScalarTower (𝓞 E) C E]
    [IsScalarTower S3 C E] [IsScalarTower S11 C E]
    [IsLocalization.Away (3:𝓞 E) S3] [IsLocalization.Away (11:𝓞 E) S11]
    [IsLocalization.Away (33:𝓞 E) C]
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module S3 M] [Module S11 N]
    [Module.Finite S3 M] [Module.Finite S11 N] (f : M→ₗ[S3]E) (g : N→ₗ[S11]E)
    (nz : ∃m,f m≠0) (mark : C⊗[S3]M ≃ₗ[C] C⊗[S11]N)
    (wedge : (OriginalHodgeModuleOverlap318.read (C:=C) g).comp mark.toLinearMap=
      OriginalHodgeModuleOverlap318.read f) (z3 : Fin 2→M⊗[S3]M) (z11 : Fin 2→N⊗[S11]N)
    (η : H2≃ₗ[E]E) (dt : D2≃ₗ[E]E) (ψ : H2≃ₗ[E]D2) (y : Fin 2→D2)
    (at3 : ∀i,ψ (η.symm (square f (z3 i)))=(210:E) • y i)
    (at11 : ∀i,ψ (η.symm (square g (z11 i)))=(210:E) • y i)
    (q : ℚ) (P : E) (nP : P≠0) (coarse : ∀i,P*dt (y i)=coefficients (F:=E) q i)
    (arch : InfinitePlace E→ℝ) (pos : ∀w,0<arch w)
    (period : ∀w : InfinitePlace E,∃ U h : ℝ,2*max 32 (w (q:E))≤U ∧ 64≤h ∧
      w.val ((P*dt (ψ (η.symm 1)))⁻¹)*(arch w)^2=4/(U*h)) :
    ∃ (I : FractionalIdeal (𝓞 E)⁰ E) (hn : I≠0),
      (I:Submodule (𝓞 E) E)=f.range.restrictScalars (𝓞 E) ⊓ g.range.restrictScalars (𝓞 E) ∧
      Height.logHeight₁ (q/32)<2*(idealFrame I hn arch pos).normalizedDegree+11 := by
  obtain ⟨I,hn,cut,op3,op11⟩ :=
    OriginalHodgeModuleOverlap318.from_modules S3 S11 C f g nz mark wedge
  let B := dt (ψ (η.symm 1))
  have nB : B≠0 := by
    intro h
    have hz := dt.injective (h.trans (map_zero dt).symm)
    have hy := ψ.injective (hz.trans (map_zero ψ).symm)
    exact one_ne_zero (η.symm.injective (hy.trans (map_zero η.symm).symm))
  have force (i : Fin 2) (x : E) (eq : ψ (η.symm x)=(210:E) • y i) :
      x=hodgeCoefficient q ((P*B)⁻¹) i := by
    have hx : η.symm x=x • η.symm 1 := by rw [←map_smul,smul_eq_mul,mul_one]
    have he := congrArg dt eq
    rw [hx,map_smul,map_smul,map_smul,smul_eq_mul,smul_eq_mul] at he
    change x*B=210*dt (y i) at he
    rw [hodgeCoefficient,←coarse i]
    field_simp [nP,nB]
    linear_combination he
  refine ⟨I,hn,cut,height_of_open_sections (S₃:=S3) (S₁₁:=S11) I hn arch pos q
    ((P*B)⁻¹) (inv_ne_zero (mul_ne_zero nP nB)) ?_ ?_ period⟩
  · intro i
    rw [←force i _ (at3 i),localized_square,op3]
    exact square_mem f _
  · intro i
    rw [←force i _ (at11 i),localized_square,op11]
    exact square_mem g _

end OriginalTwoMarkedTensorsR8_318
