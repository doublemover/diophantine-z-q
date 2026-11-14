# Independent source review: public dependent-open frame helper

Reviewer /root/lean_review_resume; author /root/picard_repair_resume. Internal source review only, no local Lean/Lake, kernel pass or mathematical acceptance.

Baseline a2d615a4183174328321ea21d60879add229de3a; run43534276453; original-five-kernel-norm-equivalence-r9 artifact14089289356. OriginalTwoOpenReducedCocycle318 before SHA256 028ca790008a22b1d1ef695d97de039e94907894ddaffba4def3dc2a84be4704; r10 candidate f318957cb96a755fb7a5f1a7537ead47fe5608760cf34bbe6b0a4032a8dece23. Exact log SHA256 2f38e10c7c43d35c465facdc15547971543765808c63bab91ab4f60951591176. Own RESULT matches predecessor intake and records module failure2.019s.

I read the exact log, whole candidate, prior source and diff. The sole error is unknown frameAlongOpenEq at its use inside exposed frames, with an explicit diagnostic that the current-module private declaration must be public. Byte comparison confirms the entire source change is exactly `private def frameAlongOpenEq` to `@[expose] def frameAlongOpenEq` inside the existing public section. No body, type, import, option, map or theorem statement changes. The successor changes only this one root source of the213-file closure at this review.

I re-read the dependent helper and actual frames consumer. For every Scheme0, module M, opens W,Z and equality W=Z, it transports the entire unit-to-restricted-module isomorphism by substituting Z, then returns the original e. It does not replace either side of the dependent frame or choose an independent trivialization. The actual application uses OriginalThickenedOpen318.fullOpen_eq on the same Bool-indexed two affine opens and the actual OriginalThickenedFrameCocycle frame of L. The public/exposed status permits this exact unchanged construction in exposed frames.

The full original deformation, same thickened opens, stable reduction-preimage identity, normalized cocycle and original reconstruction remain byte-identical. Both Bool charts and the actual U join V=top cover are retained. No IsIntegral X assumption is added; no smaller open, altered unit, frame or normalization occurs. Later unchanged consumer failures remain outside scope.

Conclusion: no source-level blocker in this visibility-only repair. The historical source review is acknowledged only for unchanged bodies/types, not converted into kernel acceptance. Final metadata/ancillary/evidence binding needs propagation review after schema opt-in; hosted replay remains required.
