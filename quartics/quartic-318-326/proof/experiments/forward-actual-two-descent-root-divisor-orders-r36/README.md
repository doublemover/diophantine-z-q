# Explicit square-complement pole producer

Independently source-reviewed construction, not Lean-checked. This thin successor replaces only the descent-r35 active slot; weighted-r35 remains unchanged for its pinned diagnostic.

The existing `TwoTwistPointRealization318.equalTwist` still takes an abstract SquareclassPoint. This file constructs it explicitly at the actual two-torsion root: beta=n, root=1, ordinate=0. The original interface permits zero ordinate and requires only nonzero root. This supplies both curve occurrences with the same n.

It then constructs the exact V-square witness d=17*b*r from 1-b/17=r^2 and derives the existing literal Certificate b. Finally b=17*(1-r^2), with r nonzero and r^2<1, gives an actual positive-pole family in (0,17), together with its certificate. The theorem does not assume either desired rational point.

This does not prove that the four detector/scalar poles can simultaneously be selected in this family, nor does it supply the arbitrary squareclass simultaneous-twist producer. The negative-three torsion class was deliberately excluded: it cannot occur in the required positive pole interval and would not advance the source route.

No local Lean/compiler execution. Strict source escape scan passed; all equations are explicit ring identities and the domain inequalities are nlinarith consequences. These tactics still require hosted acceptance. Exact dependency sources and hashes are recorded in intake.json; predecessor identity and independent review are retained in INHERITANCE.json and SOURCE-REVIEW/REVIEW.json.
