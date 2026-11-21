# Exact TZ 39 follow-on after hosted r9

- Source: authenticated run 44865799864; raw inventory SHA256
  edd78524054e06f07a358bcc6683e4834fdb2a49678649a50e2f273890f5aa0c.
- Hosted: 36/39 compiled, 530 declarations audited; one direct root
  and two dependents blocked. All 130 prior sources were audited against
  the pinned incoming artifact by the root before repair.
- Sole changed owner `ActualTZHybridCanonicalWrap318`. The first error was
  a stuck type in the declaration of `Context` itself, invalidating most
  later projections. Replace the grouped anonymous field binders by
  individual named Nat fields in exactly the same order. Type the minimum
  projection and the actual Pair hit predicate at their original domains.
- Explicit direct proof-only visibility edge to the already-selected
  `ActualTZCanonicalWrapFibres318`: `size_le` unfolds the exact original
  cardinal of a finset filter. The canonical cell/decoding/weight are
  unchanged. The raw kept-cell simp site now derives the literal zero
  then rewrites the strict positive hypothesis.
- All 129 peers, including blocked owners and never selected terminal,
  are byte-for-byte identical. Same exact 39 selection and pin. This is a
  static corrected draft, not a Lean or hosted pass.
