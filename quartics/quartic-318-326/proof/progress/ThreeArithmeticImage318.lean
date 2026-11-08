module
public import ThreeArithmeticFiberSurjective318
public section
noncomputable section
namespace ThreeArithmeticImage318
open OpenJModel318 OpenJComplexEvaluation318
open ThreeArithmeticPoint318 ThreeArithmeticQuotient318 ThreeArithmeticFiberSurjective318
set_option maxHeartbeats 0

/-- A complex point of the literal localized arithmetic base is determined
by its actual j-coordinate, not by an additional chosen base identification. -/
theorem baseHom_eq_evaluation (N : ℕ) [NeZero N] (tau : UpperHalfPlane) (h : Admissible tau)
    (f : Base N →+* ℂ) (hj : f (jCoord N)=ActualQJ318.jInvariant tau) :
    f=evaluation N tau h := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (denominator N))
  apply Polynomial.ringHom_ext
  · intro n
    simp
  · change f (jCoord N)=evaluation N tau h (jCoord N)
    rw [evaluation_jCoord,hj]

/-- Every complex arithmetic point whose j-value is realized by the genuine
analytic invariant is actually in the image of the constructed modular map.
There is no remaining four-point fiber-surjectivity premise. -/
theorem exists_source_of_j (N : ℕ) [NeZero N] (tau : UpperHalfPlane) (h : Admissible tau)
    (f : LiteralThreeXComparison318.Fixed N →+* ℂ)
    (hj : f (algebraMap (Base N) (LiteralThreeXComparison318.Fixed N) (jCoord N))=
      ActualQJ318.jInvariant tau) :
    ∃q : ThreeArithmeticQuotient318.Source,
      complexPoint N q=f ∧ QuotientJ318.jMap 3 q.val=ActualQJ318.jInvariant tau := by
  letI : Algebra (Base N) ℂ := (evaluation N tau h).toAlgebra
  have hb : f.comp (algebraMap (Base N) (LiteralThreeXComparison318.Fixed N))=evaluation N tau h :=
    baseHom_eq_evaluation N tau h _ hj
  let fA : LiteralThreeXComparison318.Fixed N →ₐ[Base N] ℂ :=
    { __ := f
      commutes' := fun r => RingHom.congr_fun hb r }
  exact exists_source_preimage N tau h fA

/-- The excluded elliptic j-values are impossible for a complex point of
this actual localized arithmetic algebra. -/
lemma admissible_of_j (N : ℕ) [NeZero N] (tau : UpperHalfPlane)
    (f : LiteralThreeXComparison318.Fixed N →+* ℂ)
    (hj : f (algebraMap (Base N) (LiteralThreeXComparison318.Fixed N) (jCoord N))=
      ActualQJ318.jInvariant tau) : Admissible tau := by
  let b := f.comp (algebraMap (Base N) (LiteralThreeXComparison318.Fixed N))
  have h0 := ((base_units N).2.2.2.1.map b).ne_zero
  have h1 := ((base_units N).2.2.2.2.map b).ne_zero
  have he : b (jCoord N)=ActualQJ318.jInvariant tau := hj
  refine ⟨he ▸ h0,?_⟩
  simpa only [map_sub,map_ofNat,he,sub_ne_zero] using h1

/-- The only surjectivity condition left is the genuine analytic j-image.
This isolates a specific global problem rather than silently assuming it. -/
theorem in_image_iff_realized_j (N : ℕ) [NeZero N]
    (f : LiteralThreeXComparison318.Fixed N →+* ℂ) :
    (∃q : ThreeArithmeticQuotient318.Source, complexPoint N q=f) ↔
      ∃tau : UpperHalfPlane,
        f (algebraMap (Base N) (LiteralThreeXComparison318.Fixed N) (jCoord N))=
          ActualQJ318.jInvariant tau := by
  constructor
  · rintro ⟨q,rfl⟩
    exact ⟨representative q,
      ThreeArithmeticPoint318.fixedPoint_j N (representative q) (representative_admissible q)⟩
  · rintro ⟨tau,hj⟩
    obtain ⟨q,hq,_⟩ := exists_source_of_j N tau (admissible_of_j N tau f hj) f hj
    exact ⟨q,hq⟩

end ThreeArithmeticImage318
