# Normality from principal opens

NormalitySpanDescent318.of_principal_cover proves that a domain is integrally closed when a family of principal-open denominators spans the unit ideal and every corresponding principal localization is integrally closed.

The proof chooses a denominator avoided by each maximal ideal, realizes the maximal localization as a localization of that principal chart, checks all denominators are nonzero divisors, and descends normality from maximal localizations. It does not assume normality of the original ring.

This is a generic descent result. The four-contact application additionally needs the actual span-one and branch-normality theorems supplied by source-global-smooth.

Run run.sh under the shared heavy.lock. The module and recursive axiom audit are kernel checked with debug.skipKernelTC=false and capped at 180 seconds each. Only propext, Classical.choice and Quot.sound are permitted.
