module
public import FiniteFamilyAvoidanceOpen318
public section
noncomputable section
namespace FiniteFamilyAvoidanceBaseChange318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FiniteFamilyAvoidanceOpen318
universe u
variable {Z B X T P : Scheme.{u}} (p : Z ⟶ B) [UniversallyClosed p]
  (q : Z ⟶ X) (U : X.Opens) (f : T ⟶ B)
  (r : P ⟶ Z) (s : P ⟶ T) [UniversallyClosed s] (h : IsPullback r s p f)
/-- Avoidance commutes with arbitrary base change, using the actual
surjectivity of the scheme pullback onto compatible pairs of points. -/
lemma locus_baseChange : locus s (r ≫ q) U=f ⁻¹ᵁ locus p q U := by
  ext t
  change t∈locus s (r ≫ q) U ↔ f t∈locus p q U
  rw [mem_locus,mem_locus]
  constructor
  · intro ht z hz
    obtain ⟨w,hwz,hwt⟩ := Scheme.exists_preimage_of_isPullback h z t hz
    have hw := ht w hwt
    simpa only [Scheme.Hom.comp_apply,hwz] using hw
  · intro ht w hw
    apply ht (r w)
    have hc := congrArg (fun k : P ⟶ B => k w) h.w
    change p (r w)=f (s w) at hc
    exact hc.trans (congrArg f hw)
end FiniteFamilyAvoidanceBaseChange318
