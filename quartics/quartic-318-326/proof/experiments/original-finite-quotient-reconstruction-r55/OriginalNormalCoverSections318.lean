module
public import OriginalIntegralBaseReconstruction318
public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
public section
noncomputable section
namespace OriginalNormalCoverSections318
open AlgebraicGeometry CategoryTheory TopologicalSpace
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {Y : Scheme} [IsIntegral Y]
  {ι : Type*} (V : ι → Y.affineOpens) (hcover : ⨆ i, (V i).1 = ⊤)
  (hnormal : ∀ i, IsIntegrallyClosed Γ(Y, (V i).1))

include hcover hnormal in
/-- Every original stalk is normal, by localization of an actual member
of the supplied normal affine cover containing the same point. -/
theorem stalk (x : Y) : IsIntegrallyClosed (Y.presheaf.stalk x) := by
  have hx : x ∈ (⨆ i, (V i).1 : Y.Opens) := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  letI : Nonempty (V i).1 := ⟨⟨x, hi⟩⟩
  letI : IsIntegrallyClosed Γ(Y, (V i).1) := hnormal i
  letI := Y.presheaf.algebra_section_stalk (⟨x, hi⟩ : (V i).1)
  letI := (V i).2.isLocalization_stalk ⟨x, hi⟩
  exact isIntegrallyClosed_of_isLocalization (Y.presheaf.stalk x)
    ((V i).2.primeIdealOf ⟨x, hi⟩).asIdeal.primeCompl
    ((V i).2.primeIdealOf ⟨x, hi⟩).asIdeal.primeCompl_le_nonZeroDivisors

/-- Affine normality is recovered from the actual maximal-ideal stalks,
with their original germ algebra, rather than a replacement fraction map. -/
theorem sections_of_stalks {X : Scheme} [IsIntegral X]
    (h : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] : IsIntegrallyClosed Γ(X,U) := by
  let (x : PrimeSpectrum Γ(X,U)) : Algebra Γ(X,U) (X.presheaf.stalk (hU.fromSpec x)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec x, (hU.isoSpec.inv x).2⟩
  letI (P : Ideal Γ(X,U)) [hP : P.IsPrime] :
      IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec ⟨P,hP⟩)) P :=
    hU.isLocalization_stalk' ⟨P,hP⟩ (hU.isoSpec.inv _).2
  exact IsIntegrallyClosed.of_isLocalization_maximal
    (fun (P : Ideal Γ(X,U)) [hP : P.IsMaximal] =>
      X.presheaf.stalk (hU.fromSpec ⟨P,hP.isPrime⟩))
    (fun P _ => h _)

include hcover hnormal in
/-- A normal affine cover controls every nonempty affine open of the
original curve, including the whole finite-coordinate inverse image. -/
theorem sections (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    IsIntegrallyClosed Γ(Y,U) :=
  sections_of_stalks (stalk V hcover hnormal) U hU

include hcover hnormal in
/-- Original open immersions preserve these actual normal stalks. -/
theorem open_stalk {X : Scheme} (j : X ⟶ Y) [IsOpenImmersion j] (x : X) :
    IsIntegrallyClosed (X.presheaf.stalk x) := by
  letI := stalk V hcover hnormal (j x)
  exact IsIntegrallyClosed.of_equiv
    (asIso (j.stalkMap x)).commRingCatIsoToRingEquiv
end OriginalNormalCoverSections318
