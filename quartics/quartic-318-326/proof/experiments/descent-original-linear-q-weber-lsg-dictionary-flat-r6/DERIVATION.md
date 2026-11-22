# Module visibility for the original LSG source cohort

The exact r3 four-root selector compiled all four stock-closure roots at the
production resource limits. The same run's strict audit failed before
declarations could be inspected: its ordinary `module` used `import all` on
r3's legacy non-module Lean files. Those four individual compilations are
**not** strict acceptance; the 13 unselected owners were not run.

In r4 each of the sixteen vendored files uses `module` at the head, makes its
existing imports `public import`, and declares `@[expose] public section`
before its unchanged original body. There is no import-graph change. The new
public/exported interface preserves prior visible definitions for existing
dependents. The original copyright and Apache license lines and the prior
r3 change notice are untouched; an adjacent new explicit change sentence
states the module/visibility update. The author surjectivity module was
already native and is byte-identical. No proof, theorem type, namespace,
tactic or option changed.

The r4 ledger records exact reversible insertions and the hash of each fully
unchanged raw file suffix (including every mathematical declaration). Reverse
it first to the physical r3 bytes, then apply its retained predecessor ledger
for the exact upstream recovery. `EXACT-SOURCE-DERIVATION.diff` is the original
through r3; the explicit adjacent diff is r3 through r4. The release lock,
license, source pin and stock dependency list have not moved.

The old exact production audit source is provided for verification, not as an
alternative audit. It imports all selected modules, checks the complete
`constNames` range for **each** matching module and fails if any selected
module is missing or any declaration depends on an unapproved axiom. This
covers private/declaration auxiliaries in addition to the named public source
sentinels inventory. No new workflow, reduced audit or limits are used. The
least expensive single-root r4 selector is the rectangle integral; the
four-root selector is the direct boundary-equivalent rerun. Wider selections
are recorded as source-only; choose these only after actual roots obtain a
strict result.
