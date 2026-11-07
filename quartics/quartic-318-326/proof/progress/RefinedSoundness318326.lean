module
public import LiteralSoundness318326
public import RefinedContactRealization318
public import Current326Final
import all Current318FinalPolynomial
public section
namespace RefinedSoundness318326

/-- The published source endpoint, conditional on the explicitly unconstructed
refined geometric producer data with actual section/Hodge norms. This is not an unconditional soundness claim. -/
theorem source_soundness (hGeo:RefinedContactRealization318.RefinedGeometricRealization) (q:ℚ)
    (h:CircuitReplay.HasSolution
      (Raw318FinalReplay.stage0 (Current318FinalPolynomial.scale:ℚ)) q) :
    ∃z:ℤ,(z:ℚ)=q :=
  LiteralSoundness318326.source_soundness
    (RefinedContactRealization318.five_contact_of_refined_realization hGeo) q h

/-- The literal 318-coordinate polynomial endpoint with actual geometric
realization still explicit. -/
theorem polynomial318_soundness (hGeo:RefinedContactRealization318.RefinedGeometricRealization) (q:ℚ)
    (h:∃w:Fin 317→ℚ, MvPolynomial.eval₂Hom (Int.castRingHom ℚ)
      (Fin.cons q w) Current318FinalPolynomial.P=0) :
    ∃z:ℤ,(z:ℚ)=q :=
  LiteralSoundness318326.polynomial318_soundness
    (RefinedContactRealization318.five_contact_of_refined_realization hGeo) q h

/-- The exact stored 326-coordinate coefficient table endpoint with actual
geometric realization still explicit. Completeness is separate. -/
theorem stored326_soundness (hGeo:RefinedContactRealization318.RefinedGeometricRealization) (q:ℚ)
    (h:∃w:Fin 325→ℚ, MvPolynomial.eval₂Hom (Int.castRingHom ℚ)
      (Fin.cons q w) Current326CoefficientBinding.tablePolynomial=0) :
    ∃z:ℤ,(z:ℚ)=q :=
  LiteralSoundness318326.stored326_soundness
    (RefinedContactRealization318.five_contact_of_refined_realization hGeo) q h

end RefinedSoundness318326
#print axioms RefinedSoundness318326.source_soundness
#print axioms RefinedSoundness318326.polynomial318_soundness
#print axioms RefinedSoundness318326.stored326_soundness
