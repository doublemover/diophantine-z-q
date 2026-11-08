# Exact carry-forward of the frozen Pan review to Version 13

The active target is manuscripts/quartic_v13.tex, SHA256 9db71bbfcefb37db56eabcf40a5f9dd85de9ed58294635da3dbf6d4f5caa8fcd. The prior independent Pan review remains immutable at pan-v11-independent/receipt.json, SHA256 a50829ed683dfb0a69064c32af8a5a23127e7f6cbb69308c34d34699e2bf554b.

**The same bounded acceptance carries forward.** All 11 pinned passages from that review occur uniquely and byte-for-byte identically in V13, including the actual scalar-corrected representation, Pan application and two twist-removal routes, coefficient transfer, de Rham dependency, conductor and Jacobian consumers, the pending-review marker, publication qualification, and bibliography. COMPARISON.json gives the old and new line ranges and exact excerpt hashes. The body passages shift by seven lines; the bibliography shifts by the additional appended V12/V13 sections.

The complete V11-to-V13 byte comparison has only four changed regions: the version title, abstract polynomial counts, the introduction announcing V13, and the appended V12/V13 construction sections. No line of the 11 reviewed Pan passages changed. This is a direct check, not an assumption based on revision labels.

The new construction sections retain the prior restricted-converse and height dependencies. Their new polynomial reductions do not change the representation to which Pan is applied, introduce a new Pan application at 3, or remove the earlier source-version qualification. They are downstream users of the retained chain. Their soundness and completeness are not newly accepted by this carry-forward.

All nine obligations of the frozen Pan APPLICATION.json retain their exact meaning. In particular:

- The actual chosen prime is 5; the realization at 3 is obtained from the same compatible trace system, not by another invocation of Pan.
- Pan’s inspected author-v2 theorem gives modularity up to twist, conditional on the stated honest representation, oddness, ramification and p-adic Hodge inputs.
- The early Conrad character route and the companion determinant route remain distinct. The separately completed Brinon–Conrad and Conrad reviews can discharge their own upstream applications; they are not silently incorporated as new findings by a byte-comparison record.
- The primary JAMS final-text comparison remains **open**. The verified author version and published Calegari corroboration are not relabeled as the primary JAMS text.
- Global source production, PEL/contact identification, separate conductor and height results, and unconditional literal-318 sourceArithmetic remain outside the acceptance.

No old acceptance was edited, no shared repository file was changed, and no Lean compile was run for this carry-forward.
