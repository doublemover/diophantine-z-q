# Exact original upper Jacobian: source and CI staging

This is the backward height route on the original signed-H modular cover X_H, normalized at χ=j/1728 with π=1/χ. The retained point is the whole original R106 residue map, continued in the same selected V and arithmetic section R67/R74. Nothing here identifies the lower quaternionic PEL abelian surface with J_H, assumes a different π cover, or proves either final diophantine endpoint.

## Read first

- [Field Picard and exact analytic Abel kernel](notes/SAME-J-FIELD-PIC-AND-EXACT-ANALYTIC-ABEL-KERNEL.md): applies the pointed Pic⁰ theorem to the actual curve after genuine normalization/compact recognition. Uses the kernel half of Abel's theorem and meromorphic rationalization on the same χ cover. Local inverse with g independent evaluation rows provides surjectivity, without a separate Jacobi inversion or general GAGA prerequisite.
- [Same-J periods and marked derivative](notes/SAME-J-ACTUAL-ABEL-PERIOD-AND-MARKED-JET-ATTACHMENT.md) and [all-order graph logarithm](notes/SAME-J-ACTUAL-ALL-ORDER-ABEL-LOG-AND-WRONSKIAN.md): the Abel, cycle and metric reads use one coframe of the same algebraic group. The ordinary χ chart is not asserted étale at the omitted branch/cusp points.
- [Recognizing the entire ordinary H open](notes/ACTUAL-FULL-H-ORDINARY-ANALYTIC-CUT-r15.md) and [compact continuation](notes/ACTUAL-COMPACT-H-NORMALIZATION-BY-INTEGRAL-EXTENSION.md): glue the actual normalized meromorphic functions rather than classes merely sharing χ(P).

## Exact, dependency-closed experiment packets

| Packet | State and intended CI use |
| :-- | :-- |
| `same-j-upper-verified-core-r1` | First hosted target. 11 exact sources strictly replayed in the isolated pinned environment with their embedded axiom roots ordinary. Hosted recursive audit of all declarations is still pending. |
| `same-j-upper-diagonal-probe-r1` | One stock-only actual affine product pullback, source-only. |
| `same-j-upper-relative-test-probe-r1` | One stock-only arbitrary parameter-ring base change, source-only. Test independently from the diagonal probe so one diagnostic does not mask the other. |
| `same-j-upper-field-pic-r1` | Connected diagonal/Cartier source continuation, after the probes. Local hypotheses are actual smooth coordinates; same-field pointed Picard representability itself is not included. |
| `same-j-upper-abel-jets-r1` | Connected ordinary χ jet, literal graph, residue, all-order and Abel affine chart steps. Source-only; no integral Néron comparison or global representation inferred. |
| `same-j-upper-haar-r1` | Exact period-basis/Haar source follow-on, with both historical pure-Mathlib donor sources. Source-only at this exact packet; broad official stock closure, so separate and optional after geometry. |

Exact sources were preserved except for one source-only identifier rename in the all-order positive graph: `constant` became `constantImage` to satisfy the existing CI source policy. The predecessor SHA and derivative are recorded. Each `intake.json` declares file SHA-256, exact imports and proper predecessor order. `SOURCE-PROVENANCE.json` separates exact passing local objects and root logs from uncompiled sources. No compiled objects or ZIP files are tracked in the packet. The first two verified strict determinant leaves assume the actual Riemann bilinear identities in the same period columns; they do not claim to have constructed the period lattice.

## Existing hosted checker

On the immutable Lean/Mathlib pins in the provenance, the existing checker accepts a complete packet explicitly even if it is not active:

```sh
python -B scripts/check_progress_experiment.py targets --packet same-j-upper-verified-core-r1
# Using the standard official pinned-dependency setup, a verified baseline receipt,
# and its cache, from quartics/quartic-318-326/proof/progress:
lake env python -B ../../../../scripts/check_progress_experiment.py check \
  --packet same-j-upper-verified-core-r1 --cache "$VERIFIED_BASELINE_CACHE" \
  --output "$NEW_ARTIFACT_DIRECTORY" --seconds 180
```

Current registry selection is restricted to active packets and capped at 16. Do not append to a full registry or silently evict another lane. Activate one bounded slot when available or use an explicitly targeted central dispatch. The checker still expects its existing verified baseline receipt even for a packet with zero project-baseline imports; it then restores zero predecessor modules. Treat official artifact acquisition separately from actual checking. This packet changes neither the registry nor workflows.

## Outside dependency boundary

The public [NYLL standalone Jacobian library](https://github.com/n-yamaguchi-0729/GeneralizedJacobianVarieties) has an exact-toolchain source candidate at `bb45f8288926fb121f81272caacc6ec6adcc00b2`, previously source-inspected but not admitted or locally import-checked. The [ordinary represented group sheaf documentation](https://n-yamaguchi-0729.github.io/NYLL/modules/Nyll.JacobianVarieties.Generalized.ExistingJacobianSheafRepresentation/) names the specialization `JacobianVarieties.Picard.Unpointed.groupSheafRepresentation K c`, using the saved carrier `toBase K c` and the full Picard-zero group sheaf. It needs the same actual `c : X_H ⟶ Spec K`, `IsProper c`, `SmoothOfRelativeDimension 1 c`, and `GeometricallyIrreducible c`; the normalized pointed map uses the actual R106-induced P, not the earlier chosen scalar only. Standalone source revision should be checked independently of current documentation. The large donor closure and recursive axiom audit are a separate experiment, not a package dependency of this handoff. Do not import a challenge/umbrella module or vendor unreviewed code into the original proof. The same algebraic Abel pullback/differentials, classical compact Abel/Riemann comparison, and integral semistable Néron Hodge comparison remain outside this source bundle at their indicated proof boundaries.
