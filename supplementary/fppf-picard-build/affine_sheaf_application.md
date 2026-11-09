# Original affine scheme overlaps and candidate coactions

Five new sources consume five unchanged affine-line/tensor-pushout producers.
The input rings and algebras are arbitrary commutative rings, including
nonreduced ones. The input line is an actual line sheaf on the original Spec.

1. **Original affine pushforward.** TildePushforward318.sectionsIso uses the
   original pushforward global-section comparison and the actual
   tilde-Gamma counit of the pushforward. Its invertibility follows from
   the pinned theorem preserving invertibility of that counit under an
   affine pushforward. The comparison is natural for every original
   coefficient sheaf map between the stated objects.
2. **Actual scheme fiber square.** AffineSheafBaseChange318.isPullback
   applies the actual ring tensor-pushout theorem and Spec pullback theorem
   to the unchanged include-left/include-right maps. The square is the
   entire affine scheme fiber square, not a generic or reduced subspace.
3. **Actual sheaf comparison.** AffineSheafBaseChange318.iso compares the
   original scheme pullback of the original affine pushforward with the
   original opposite-order pushforward of pullback, for every sheaf whose
   original tilde-Gamma counit is invertible. All six factors are actual
   canonical tilde, section, pullback or module-comparison maps.
4. **Canonical module factor.** module_factor binds the middle tensor
   comparison to the exact extension/restriction adjunction mate already
   proved in the unchanged affine-pushout-comparison producer. The whole
   scheme-sheaf isomorphism is not separately identified with the scheme
   adjunction mate in this packet.
5. **All overlap module morphisms.** AffineOverlapCoaction318.homEquiv
   is a true bijection from maps between the two original scalar-extended
   modules on the double overlap to maps from the original module to its
   original scalar-extension comonad object. It uses the original
   left-inclusion adjunction and exact tensor-pushout comparison. Its
   original unit-tensor formula is proved, and no coalgebra law is
   inferred from this bijection alone.
6. **Original geometric morphisms.** OriginalLineOverlapCoaction318
   composes the actual original line pullback/tilde comparison, the
   genuine tilde-Gamma adjunction, and the actual section comparison.
   moduleHomEquiv_apply proves that this is exactly original global
   sections of the given original sheaf morphism conjugated by the two
   canonical section maps. No substitute line object or chosen frame
   discards overlap information.
7. **Full bijection and unique recovery.** The resulting homEquiv covers
   every original double-overlap line-sheaf morphism and every candidate
   comonad map. unique_overlap proves unique recovery of the actual
   geometric morphism. This is a statement about all morphisms, not yet
   a claim that arbitrary candidate maps satisfy descent laws or arise
   from invertible overlap maps.
8. **Actual diagonal evaluation and counit.** AffineOverlapDiagonal318
   uses the original multiplication homomorphism from the double tensor
   ring to the original algebra. Both diagonal composites are proved to
   be the identity ring map. firstEvaluation and secondEvaluation are
   constructed through the original extension/restriction adjunctions
   and scalar-restriction composition maps. Full tensor induction proves
   that the original comonad counit after the original pushout comparison
   is exactly the second evaluation. The actual normalized equation
   a followed by secondEvaluation equals firstEvaluation implies the
   genuine comonad counit equation.
9. **Next consumer and boundary.** This binds original geometric overlap
   morphisms to candidate coactions and proves the diagonal evaluation
   implication. It does not yet transport the actual geometric diagonal
   normalization or triple-overlap cocycle through all scheme pullback
   coherence maps, prove coassociativity, or construct a coalgebra from
   full geometric descent data. Arbitrary-scheme gluing, effective fppf
   line-stack descent, degree zero, representability, Jacobians, duality,
   polarization and isogeny remain outside this packet.
