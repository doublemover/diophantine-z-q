# P-adic unit norm coprimality API correction

Exact native API inspection identified two mismatches: norm_natCast_eq_one_iff returns p.Coprime n, not nondivisibility. Fresh strict run43993365837 then reported precisely these two errors and no others. Apply prime.coprime_iff_not_dvd explicitly in both directions. The original preventive source-review metadata is preserved; fresh runtime binding is supplemental evidence, not a different candidate.

Two proof expressions in PadicUnitSquareclass318 change. The same fresh run found one numeral-cast rewrite mismatch in LegendreGoodPrimeLocal318; its derived norm-two fact is explicitly typed and normalized by simpa. These are the only two changed sources. No public hypotheses, signatures, imports, options or resource limits change. All1341 other source bytes and1343-root order remain exact. In particular the fresh checked PadicSquareNormalization318 and AuxiliaryCommonValue318 sources are untouched.

Strict replay is still required for the repaired unit leaf. No finite-family approximation, selected prime or global witness is claimed. No local Lean was run.
