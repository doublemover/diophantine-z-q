module
public import PrincipalFrameZeroOverlaps318
public import ClosedSubschemeCoverGluing318
public section
noncomputable section
namespace PrincipalFrameZeroScheme318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
  (c : ∀ i,Γ(X,U i)) (t : ∀ i j,Γ(X,U i ⊓ U j)ˣ)
  (hc : ∀ i j,X.presheaf.map (homOfLE inf_le_left).op (c i)=
    (t i j).val*X.presheaf.map (homOfLE inf_le_right).op (c j))
  (hCover : (⊤ : X.Opens) ≤ ⨆ i,U i)
open PrincipalFrameZeroOverlaps318
def pairOpen (i j : ι) : IsOpenImmersion (pullback.fst (into U c i) (into U c j)) :=
  pullback_open U c t hc i j

/-- The scheme-theoretic zero locus of a compatible family of local
line coefficients. Actual principal quotients are glued without reducing
or replacing their ideals by radicals. -/
@[expose] def scheme : Scheme := by
  letI := pairOpen U c t hc
  exact ClosedSubschemeCoverGluing318.Glued U (Zero U c) (zeroInclusion U c)
@[expose] def inclusion : scheme U c t hc ⟶ X := by
  letI := pairOpen U c t hc
  exact ClosedSubschemeCoverGluing318.into U (Zero U c) (zeroInclusion U c)
@[expose] def chart (i : ι) : Zero U c i ⟶ scheme U c t hc := by
  letI := pairOpen U c t hc
  exact ClosedSubschemeCoverGluing318.inclusion U (Zero U c) (zeroInclusion U c) i
instance chart_open (i : ι) : IsOpenImmersion (chart U c t hc i) := by
  letI := pairOpen U c t hc
  dsimp [chart]
  infer_instance

include hCover in
lemma closed : IsClosedImmersion (inclusion U c t hc) := by
  letI := pairOpen U c t hc
  exact ClosedSubschemeCoverGluing318.closed U (Zero U c) (zeroInclusion U c)
    (pullback_range U c t hc) hCover

/-- Every original local principal quotient is the FULL Cartesian
restriction of the actual global zero scheme. -/
lemma cartesian (i : ι) : IsPullback (zeroInclusion U c i) (chart U c t hc i)
    (U i).ι (inclusion U c t hc) := by
  letI := pairOpen U c t hc
  exact ClosedSubschemeCoverGluing318.cartesian U (Zero U c) (zeroInclusion U c)
    (pullback_range U c t hc) i
@[reassoc] lemma chart_inclusion (i : ι) :
    chart U c t hc i≫inclusion U c t hc=zeroInclusion U c i≫(U i).ι :=
  (cartesian U c t hc i).w.symm

/-- The genuine quasi-coherent kernel ideal of the whole closed
immersion, with no reducedness hypothesis on the zero scheme. -/
@[expose] def kernel : X.IdealSheafData := (inclusion U c t hc).ker

include hCover in
lemma kernel_restriction (i : ι) : (kernel U c t hc).comap (U i).ι=ideal U c i := by
  letI : IsClosedImmersion (inclusion U c t hc) := closed U c t hc hCover
  let h := cartesian U c t hc i
  calc
    _ = (pullback.fst (U i).ι (inclusion U c t hc)).ker :=
      (Scheme.IdealSheafData.ker_fst_of_isClosedImmersion _ _).symm
    _ = (h.isoPullback.hom≫pullback.fst _ _).ker :=
      (Scheme.Hom.ker_comp_of_isIso _ _).symm
    _ = (zeroInclusion U c i).ker := by rw [h.isoPullback_hom_fst]
    _ = ideal U c i := Scheme.IdealSheafData.ker_subschemeι _
end PrincipalFrameZeroScheme318
