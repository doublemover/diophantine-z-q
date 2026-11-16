# Explicit point constructions, restricted scope

Three new modules; 1300 predecessor roots unchanged and one import-preserving record extraction. The byte-exact KummerPoint record remains in namespace ActualTwoDescentPointExtraction318, now defined in ActualTwoDescentKummerPointData318; the original PointExtraction still imports DiagonalExtension and reexports the record alongside unchanged converters. This permits genuine-type dependency-closure validation without removing transitive exports from old consumers.

OneTorsionPoleFamily318 constructs literal certificates on 51b+k^2=1156, including a nonsquare-complement example. ExplicitPositiveKummer318 constructs an actual KummerPoint beta n for every positive rational beta and a positive explicitly chosen n. Neither supplies the second point at n*theta or matches the existing prescribed prime-pattern twist. Nonzero ordinate is not claimed to imply infinite order. The source factors and common CRT index remain fixed and unsolved.

No local Lean run, no hosted acceptance, no complete arithmetic theorem claim. Independent source reviews are bound in SOURCE-REVIEW. Historical evidence remains at the immutable predecessor tree.
