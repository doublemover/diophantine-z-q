# P-adic representative proof API repair

Fresh run43972786530 found two elaboration errors in LegendrePadicPrimitiveResidues318: a natural-to-integer-to-ZMod cast was not definitionally reduced, and a combined simp rewrote the whole polynomial through the representative lemma before distributing the ring hom.

The first proof explicitly normalizes the cast and native hom definitions. The second distributes the ring hom first, then substitutes coordinate representatives. Only these two proof sites change. All statements, assumptions, definitions, imports, options and resource limits remain unchanged.

All1331 other source bytes and1332-root order are retained, including checked modular-root73 and124 arithmetic sources. The repaired target still has one experiment-root closure. No new mathematical layer, auxiliary-prime compatibility or global witness is included. Source/API review is not Lean acceptance; strict hosted checking remains required.
