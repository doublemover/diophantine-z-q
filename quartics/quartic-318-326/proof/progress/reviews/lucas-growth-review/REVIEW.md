# Independent Lucas growth review

## Result

PASS. The three new source files were copied without changes from `height-work` and rebuilt in this isolated directory with Lean 4.35.0 and `debug.skipKernelTC=false`. The recursive audit checked 27 declarations across the imported `LucasHeight318` residual interface and the three new modules; only `propext`, `Classical.choice`, and `Quot.sound` occur. The copied sources match the author's versions by SHA-256. The imported residual interface is hash-bound; it was not separately rebuilt in this replay.

## Mathematical checks

- `ordered_solution` is an integer Vieta descent, not a presumed unit-group classification. For ordered nonnegative coordinates, the new coordinate `a*x-y` is nonnegative and strictly smaller than `x`. The zero endpoint and equality exclusion are handled explicitly.
- The recurrence is `U(0)=0`, `U(1)=1`, `U(n+2)=a*U(n+1)-U(n)`. Its lower bound is `(a-1)^n <= U(n+1)`.
- The two congruences modulo `a-2` and `a+2` imply index divisibility. Both possible orderings of the two solution coordinates are treated; the first ordering loses two in the index, exactly reflected by the final lower bound `a-4`.
- The literal signed equation is normalized using `w=sign(s)*(s-2)*z`. This correctly handles negative `s`, with `abs(s-2)=abs(s)-2` or `abs(s)+2`. Neither positivity of `s` nor a hidden choice of a fundamental unit is assumed.
- For `abs(s)>=7` and nonzero `z`, the resulting exponent bound and `log 6 > 3/2` imply `abs(s)-3 < log(abs(t))`. Nonvanishing of `t` is proved before monotonicity of logarithms is used.
- The residual wrapper consumes the actual literal Lucas residual, and the actual anchor/orientation bound supplies the size threshold. The final integer-input theorem removes the former Lucas-growth premise.

## Boundary

This packet proves the Lucas-growth producer. Its final separation theorem still explicitly requires the three high/scalar/low height comparisons, the odd first label, the nonzero last label, actual label bounds, and scalar orientation/anchor bound. It does not itself prove those arithmetic or geometric inputs. The independent review does not cover the later Lucas witness-existence module.

## Replay

Run `./run.sh`. Exact output is retained in `replay.log` and per-module logs. `REVIEWED_SHA256SUMS` binds the reviewed source files, imported residual interface, audit, and replay script.
