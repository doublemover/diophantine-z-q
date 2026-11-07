# Literal detector scales, nondegeneracy and height comparison

Status: COMPLETE at declared interface. Three modules, 22 kernel-checked declarations; standard axioms only. No repository or live worker sources were edited.

## Exact compiled row identities

`SourceDetectorScales318` uses the current compiled assignment, not historical parameter indices:

- r106 identifies Norm(Kprod)=w145, where Kprod=pair(w143)(w144).
- r107 proves lambda=t0=w38 is nonzero by its explicit reciprocal w146.
- r157 and r107 identify t1=w194=(Re(Kprod)+Norm(Kprod))² lambda.
- r210 and r107 identify t2=w245=Norm(Kprod)² lambda.
- The actual weights A1 and A2 are exactly those two square scale factors.

The module composes these identities with `DetectorHeightTransfer318.actual_norm_49_over_8_height` and the previously checked actual lower bound. It obtains B²−6<7H|N|^(49/(8k)) from the three actual rational height bounds, with lambda nonzero proved rather than assumed. It leaves those three height bounds explicit; it does not claim to prove the global five-contact 49/8 theorem or its primewise divisibility inputs.

## Nondegeneracy without a positivity shortcut

`ActualDetectorNondegenerate318` proves both real embeddings of the actual Kprod have absolute value greater than1. It uses the exact squared-product identity and actual real abscissae of nonzero multiples of P. For arbitrary signs of two real conjugates a,b, their absolute sizes>1 give |ab|>|(a+b)/2|. Thus |Norm(Kprod)|>|Re(Kprod)|, so both Norm(Kprod) and Re(Kprod)+Norm(Kprod) are nonzero. This discharges all three A coefficients.

The exact fused identities eF=(A(t−1))^5 then exclude every zero of the five-factor contact polynomial. If F=0, nonzero A forces t=1; the polynomial is nonzero at1, a contradiction. No positivity or square hypothesis on lambda/t is used. The allowed t=1 case is not excluded and remains available for the separate zero-height branch.

`five_factors_nonzero` exposes the five actual rational factor nonvanishings for the contact-radical interface.

## Final wrappers

`SourceDetectorHeightComparison318.source_contacts_nonzero` assumes only the literal stage0(3^65536) source constraints and proves nonvanishing for all three contact polynomials, consuming the unconditional actual global labels.

`source_max_index_comparison` returns the actual labels, scalar anchor data, exact maximum B≥3 and the combined upper/lower height comparison. The only further supplied facts are H≥1, N nonzero and the three rational contact-height inequalities. It does not assert final source soundness.

## Replay

Run `bash converse-work/source-detector-scale-interface/verify.sh`. Paths to every sibling packet are explicit. Kernel checking is forced with debug.skipKernelTC=false; errors and sorryAx are rejected. The receipt binds all three sources, compiled outputs, logs and consumed interface sources.
