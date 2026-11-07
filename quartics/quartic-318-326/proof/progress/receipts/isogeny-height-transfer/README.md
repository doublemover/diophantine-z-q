# Dimension-two image and isogeny height transfer

Status: one Lean module, 16 public theorems, full kernel audit with standard axioms only. This packet completes the finite real inequalities from the adopted Jacobian growth bound to the precise five-contact height cap. It does not prove that the geometric or modular objects supplying those inequalities exist.

## Exact proved consequences

With C=210^300 and R>=1:

- g<2^14*C*R^(97/32), h(J)<2^65*C²*R^(49/8), h(image)<=h(J)+3g/2 imply h(image)<2^66*C²*R^(49/8).
- [L':Q]<=2304R and that image bound imply the source's exact dimension-two half-log isogeny expression is less than 2^17*R^(49/8).
- Actual isogeny variation then yields h(A)<2^67*C²*R^(49/8), and the retained geometric inequality gives h(contact)<2^68*C²*R^(49/8)+128.
- The CM estimate h(contact)<=854R is dominated separately.
- The historical constant 2^110*C^6*B^19+128 still dominates the adopted exponent after R=B*M with B,M>=1.
- `source_nonCM_height` composes the actual log(6dN) and Jacobian bounds with all these estimates. Its hypotheses remain explicit producer inequalities; it is not a renamed whole-height axiom.

The primary GR2022 theorem states an original Faltings-height normalization. `half_log_expression_mono` and `surface_height_from_original` prove the exact monotonicity needed to insert the larger shifted normalization used downstream. Same-dimension isogeny variation is unchanged by this shift.

## Actual metric and normalization producer checks

`METRIC-PRODUCER.md` independently derives the actual metric on the literal contact curve: smooth positive extension at every finite branch and infinity, exact curvature, compact maximum-principle comparison, the factor-four Petersson norm, actual q0/q1 sections and finite extension, and the height sign/constant ledger. It retains the identified branch model, proper regular semistable stack, and Yuan isometry as named geometric inputs. It does not substitute a scalar curvature assumption for this calculation.

`NORMALIZATION.md` records a fresh original GR2014 section 2.3 check, including rendered printed pages 351–352 and the exact original/shifted definitions. Yuan, Javanpeykar, Rémond, and GR2022 originals were checked in the earlier frozen packets. The independent metric cross-review is at `../metric-producer-review/REVIEW.md` with a hash-bound receipt; it accepts this exact scope and retains the same geometric boundary.

## Remaining global boundary

The actual identified Shimura quotient and fiber, normal fiber field and ramification support, modularity/level/conductor control, actual Jacobian image, and the arithmetic realization of the input inequalities are not Lean proved here. The actual local Wronskian analytic input is separately owned by the analytic worker. Consequently ContactHeight318.FiveContact49Height remains unproved as a whole despite these discharged finite estimates and scoped mathematical producer checks.

Run `./build.sh` for a complete replay. All 16 public results are checked with `-Ddebug.skipKernelTC=false`; axiom roots are only propext, Classical.choice, Quot.sound. No repository or Git operation was performed. PDF/text/images are verification inputs and need not be vendored with the Lean checkpoint.
