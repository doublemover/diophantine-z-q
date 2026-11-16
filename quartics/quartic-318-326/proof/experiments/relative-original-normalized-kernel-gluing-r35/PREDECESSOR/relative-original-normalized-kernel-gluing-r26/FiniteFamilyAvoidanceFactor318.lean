module
public import FiniteFamilyAvoidanceBaseChange318
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public section
noncomputable section
namespace FiniteFamilyAvoidanceFactor318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FiniteFamilyAvoidanceOpen318
universe u
variable {Z B X T : Scheme.{u}} (p : Z ⟶ B) [UniversallyClosed p]
  (q : Z ⟶ X) (U : X.Opens) (f : T ⟶ B)
/-- The support condition on the actual pulled-back whole family. -/
@[expose] def Supported : Prop := ∀ z : pullback p f, q (pullback.fst p f z)∈U
lemma supported_iff_range : Supported p q U f ↔ Set.range f ⊆ (locus p q U : Set B) := by
  constructor
  · intro h t ht
    obtain ⟨y,rfl⟩ := ht
    rw [mem_locus]
    intro z hz
    obtain ⟨w,hwz,-⟩ := Scheme.Pullback.exists_preimage_pullback (f:=p) (g:=f) z y hz
    simpa only [hwz] using h w
  · intro h z
    apply (mem_locus p q U (f (pullback.snd p f z))).mp (h ⟨_,rfl⟩) (pullback.fst p f z)
    exact congrArg (fun k : pullback p f ⟶ B => k z) (pullback.condition (f:=p) (g:=f))
@[expose] def factor (h : Supported p q U f) : T ⟶ (locus p q U).toScheme :=
  IsOpenImmersion.lift (locus p q U).ι f (by
    rw [Scheme.Opens.range_ι]
    exact (supported_iff_range p q U f).mp h)
@[reassoc] lemma factor_into (h : Supported p q U f) : factor p q U f h ≫ (locus p q U).ι=f :=
  IsOpenImmersion.lift_fac _ _ _
lemma supported_comp (g : T ⟶ (locus p q U).toScheme) : Supported p q U (g ≫ (locus p q U).ι) := by
  apply (supported_iff_range p q U _).mpr
  rintro _ ⟨t,rfl⟩
  exact (g t).property
end FiniteFamilyAvoidanceFactor318
