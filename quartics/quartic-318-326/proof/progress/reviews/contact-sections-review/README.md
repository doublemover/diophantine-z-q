# Actual integral sections to contact metric height

Strict-kernel PASS: four public theorems, eight exhaustively audited declarations. Standard axioms only.

`contact_metric_from_sections` uses actual NumberField frame norms, two coefficients a0,a1 with a0 nonzero and a1=(32*u/v)*a0, finite-place integrality and the literal archimedean section bound J²*(4Cmet). The exact normalized line degree is2*(hOriginal+log(pi))+log210. The theorem derives the strict actual source projective-height bound pointHeight(u,v)<2hOriginal+120. It uses the actual all-place section theorem and its proved rational base-field normalization, exact rational height loss log32, and the checked literal logarithmic budget. No contact-height bound is supplied.

`contact_metric_shifted` records the conservative bound with hShifted=hOriginal+log(pi). The coordinate ratio corresponds to the two actual global sections J²q0 and J²q1 of the maximal stack's bicanonical line; q1=tq0 and t=32u/v. At a finite nonbranch input q0 is nonzero, so the a0 premise is the actual chart condition.

The actual line bundle/frame realization, section extension and archimedean norm interpretation remain geometric inputs. They are constructed and independently source-checked in isogeny-height-transfer/METRIC-PRODUCER.md, fiber-field-bridge/FIBER-PRODUCER.md and maximal-ks-producer/MAXIMAL-KS-PRODUCER.md. The latter supplies the precise degree identity for the actual universal fiber, maximal n=1 stack and image210. No level-three dualizing bundle or ramification correction is substituted. Auxiliary integral evaluation extensions preserve normalized stable height and do not enter the isogeny field-degree bound.

This strengthens the contact_metric input in frozen five-contact-global-assembly without changing its hashes. It does not construct the whole GeometricRealization or assert FiveContact49Height unconditionally. Mapper independently reviewed the exact application and constants; a separate final assembly review is in progress.

Replay: bash build.sh, after the frozen section-height-bridge dependencies are built (its run.sh builds the exact Mathlib Projectivization module into its isolated mathlib-extra path). The remaining dependency paths match the global assembly. No repository/Git edits.
