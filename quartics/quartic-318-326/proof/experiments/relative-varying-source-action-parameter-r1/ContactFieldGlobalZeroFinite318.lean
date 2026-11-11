module
public import ContactFieldZeroFinite318
public import ContactGlobalResidueFlat318
public import ContactGlobalZeroClosed318
public import ContactRelativeOriginalSmoothProper318
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public section
noncomputable section
namespace ContactFieldGlobalZeroFinite318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalSectionZeros318
open ContactGlobalSectionZero318
open scoped TensorProduct
variable (K : CommRingCat.{0}) [Field K] [Algebra ℚ K] (c : Fin 4 → ℚˣ)
  (L : Line (curve K c)) (s : Γ(L.object,⊤)) (hs : s≠0)

/-- The SAME global zero scheme has finitely many points. Its two actual
whole quotient charts are finite field algebras, and their actual gluing
maps are jointly surjective. No étaleness or reducedness is required. -/
lemma finite_points : Finite (scheme K c L s) := by
  letI : Module.Finite K ((K ⊗[ℚ] finiteRing c)⧸finiteIdeal K c L s) :=
    ContactFieldZeroFinite318.finite_chart K c L s hs
  letI : Module.Finite K ((K ⊗[ℚ] infinityRing c)⧸infinityIdeal K c L s) :=
    ContactFieldZeroFinite318.infinity_chart K c L s hs
  letI : IsArtinianRing ((K ⊗[ℚ] finiteRing c)⧸finiteIdeal K c L s) :=
    isArtinian_of_tower K inferInstance
  letI : IsArtinianRing ((K ⊗[ℚ] infinityRing c)⧸infinityIdeal K c L s) :=
    isArtinian_of_tower K inferInstance
  let f : (finiteZero K c L s) ⊕ (infinityZero K c L s) → scheme K c L s :=
    Sum.elim (finiteChart K c L s) (infinityChart K c L s)
  apply Finite.of_surjective f
  intro x
  rcases charts_cover K c L s x with ⟨a,ha⟩ | ⟨b,hb⟩
  · exact ⟨Sum.inl a,ha⟩
  · exact ⟨Sum.inr b,hb⟩

/-- Properness of the ACTUAL original global zero projection, combined
with the constructed finite points, gives a finite morphism over the
original field. All original zero multiplicities remain in the scheme. -/
theorem finite : IsFinite (ContactGlobalResidueFlat318.projection K c L s) := by
  letI := finite_points K c L s hs
  letI : IsProper (ContactGlobalResidueFlat318.projection K c L s) := by
    unfold ContactGlobalResidueFlat318.projection
    infer_instance
  letI : LocallyQuasiFinite (ContactGlobalResidueFlat318.projection K c L s) :=
    locallyQuasiFinite_iff_finite_preimage_singleton.mpr (fun _ => Set.toFinite _)
  exact IsFinite.of_isProper_of_locallyQuasiFinite _
end ContactFieldGlobalZeroFinite318
