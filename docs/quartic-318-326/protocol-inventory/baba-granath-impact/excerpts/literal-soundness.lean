module
public import SourceHeightComparisons318
public import Current326Final
import all Current318FinalPolynomial
public section
namespace LiteralSoundness318326

/-- The literal source projection has integral input, conditional only on
its explicitly named five-contact geometric height producer. -/
theorem source_soundness (hFive:ContactHeight318.FiveContact49Height) (q:ℚ)
    (h:CircuitReplay.HasSolution
      (Raw318FinalReplay.stage0 (Current318FinalPolynomial.scale:ℚ)) q) :
    ∃z:ℤ,(z:ℚ)=q := by
  obtain ⟨w,hw,hs⟩:=h
  have hscale : (Current318FinalPolynomial.scale:ℚ)=(3:ℚ)^65536 := by
    simp only [Current318FinalPolynomial.scale,Int.cast_pow,Int.cast_ofNat]
    rfl
  rw [hscale] at hs
  obtain ⟨z,hz⟩:=SourceHeightComparisons318.source_integer_input hFive w hs
  exact ⟨z,hz.trans hw⟩

/-- Soundness of the published 318-coordinate polynomial, with its sole
remaining geometric premise exposed. Completeness is not asserted here. -/
theorem polynomial318_soundness (hFive:ContactHeight318.FiveContact49Height) (q:ℚ)
    (h:∃w:Fin 317→ℚ, MvPolynomial.eval₂Hom (Int.castRingHom ℚ)
      (Fin.cons q w) Current318FinalPolynomial.P=0) :
    ∃z:ℤ,(z:ℚ)=q :=
  source_soundness hFive q ((Current318FinalBridge.polynomial_zero_iff_source q).mp h)

/-- Soundness of the actual stored 3157-term 326-coordinate coefficient table,
conditional only on FiveContact49Height. -/
theorem stored326_soundness (hFive:ContactHeight318.FiveContact49Height) (q:ℚ)
    (h:∃w:Fin 325→ℚ, MvPolynomial.eval₂Hom (Int.castRingHom ℚ)
      (Fin.cons q w) Current326CoefficientBinding.tablePolynomial=0) :
    ∃z:ℤ,(z:ℚ)=q :=
  source_soundness hFive q ((Current326Final.table_zero_iff_source q).mp h)

end LiteralSoundness318326
#print axioms LiteralSoundness318326.source_soundness
#print axioms LiteralSoundness318326.polynomial318_soundness
#print axioms LiteralSoundness318326.stored326_soundness
