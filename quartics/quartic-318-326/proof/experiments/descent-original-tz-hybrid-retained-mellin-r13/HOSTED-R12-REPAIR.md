# Exact source reaction to hosted r12

Run 44875015714, exact selection 39 (6697cf55…), with 37 passed and
620 audited. Sole directly failing module ActualTZHybridMeanCell318,
at line 86:37: unexpected token '|*'; expected '|' or '|ₘ'.
CanonicalWrap newly PASSED unchanged. Only MeanAverage blocked.

At the exact retained_error RHS add one ASCII space between the closing
absolute-value bar and multiplication. Lean no longer lexes the registered
single token '|*'. Statement, binder, constant, import and proof remain
exactly unchanged. No anticipatory diagnostic edit. All 129 other Lean source
files and ordered39 preserved. Not compiled locally. No remote actions.
