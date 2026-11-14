# Picard site profiler-control correction: independent addendum

## Verdict and accountability
The exact one-line diagnostic correction is supported by the pinned native API. It changes no mathematical proof, theorem type, import, kernel/trust setting, resource limit or asynchronous elaboration option. This candidate-only diagnostic review is not hosted acceptance or localization of the remaining timeout.

This addendum corrects a gap in my previous `PICARD-SITE-DIAGNOSTIC-REVIEW.md` for run 43578868567 (report SHA 6ff0561abb3adfef752af6849cbc6b9fd4b8bc47e1387212c85ad7d59718b381). I checked `profileitIO` and its output path, but failed to verify the concrete option setter used by the control. The previous review did not establish that the control elaborated or ran. Its immutable report should be retained with this explicit correction, not silently rewritten or interpreted as successful control execution.

Before: `092d5da60703ca1d93045263d49d3c2080fae34cca843da6c729193f9f3f36b6`.
After: `bea62a36a5337a16bb74294ced9cb67dfbfb9173eb7089b9d5aeda2a8aa921f6`.
File: `ActualAffineEffectiveComparison318.lean`.

## Evidence, without over-localization
I independently queried GitHub artifact 14109024226 for proof-only run 43582938856 at `6fe85071934d36d22cfdbd7c503f6b9a54e6ef18`. Its digest `bcb602bcf3f1fedaa17fac0c69bf74d3b81b883e366486d36e13c92229d83513` matches the retained ZIP; extracted RESULT and full log match its members. RESULT binds the published site-r82 intake.

The exact log contains command markers 00–04, native typeclass/compilation timings, BODY00_ENTER, an `exact` tactic timing of 4.68s, BODY01_EXIT, and the second runTac timing of 47.6ms. It then ends with the 180.131-second timeout. No explicit profiler-control BEGIN, timing label or END, and no command marker05, appears. The helper-scoped native profiler emitted real completed-region timings; that does not validate the separate absent control or establish that any surrounding declaration passed kernel checking.

A command action must elaborate before any of its IO body runs. An error in its option expression can therefore prevent even its earlier BEGIN write from executing, while later commands still run and ordinary error messages remain buffered. This is a source-grounded explanation consistent with the missing control, not an observed error-message diagnosis: the retained timeout log does not show the control elaboration error. The 4.68-second exact timing and body exit do not uniquely distinguish later synthetic-metavariable work, instantiation, lambda/closure processing, declaration finalization, kernel work, or waits for asynchronous work. No such phase is declared the cause here.

## Exact API and delta
The official Lean v4.35.0 `src/Lean/Data/Options.lean` blob `875b0607fba2d2e2be4d1c3cbd1a877442b6af71` defines structured `Lean.Options`, generic `Options.set {α} [KVMap.Value α]`, and `Options.setBool`. It does not define the `Options.setNat` method used by the control. `src/Lean/Data/KVMap.lean` blob `7753d6e20da1efda91120fe6f660712ea8427130` does define `KVMap.setNat`, but that is a different carrier; it also supplies the exact `KVMap.Value Nat` instance needed by the generic Options setter. The distinction matters, rather than asserting no `setNat` exists anywhere in Lean.

The only source replacement is:

```lean
.setNat `profiler.threshold 0
```

to:

```lean
.set `profiler.threshold (0 : Nat)
```

I verified the inverse replacement reconstructs all predecessor bytes. The fresh empty Options value still applies only to the same pure-unit `Lean.profileitIO (ε := IO.Error)` control action. Its threshold remains zero, profiler remains true, and the surrounding explicit stderr flushes and BEGIN/END labels remain exact. The actual helper still has only the same declaration-local profiler true/threshold1 settings. All body/command markers, original proof text and scopes remain unchanged.

## Next hosted interpretation
Run the corrected bounded diagnostic without changing proofs or limits. First check the literal control BEGIN/timing/END and exact RESULT together. Even a successful control validates only that output route at that point. Later native timing rows report completed regions and lack individual explicit flushes; absence remains ambiguous. If the control is still absent, retain the full log and investigate that control separately before interpreting timing absence as a declaration failure. Do not promote a proof rewrite or raise limits from these observations alone.

No local Lean, compiler, or user computer was used. No new successor APPLICATION/contract or propagation set is bound by this candidate-only report; those must disclose this correction and retain the missing-control evidence and previous-review limitation. No source/kernel/full-packet acceptance flags are changed.
