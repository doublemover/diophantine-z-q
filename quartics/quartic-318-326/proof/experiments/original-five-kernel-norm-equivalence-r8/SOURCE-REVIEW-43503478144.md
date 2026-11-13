# Independent five-kernel notation repair review

Reviewer: lean_review_resume. Scope: original-five-kernel-norm-equivalence-r8, successor of r7 at head 56773da3e1a8045d885059ae17053fcbf0af6067. No local Lean/Lake execution or push. Source review only, not kernel acceptance.

## Exact sources
- OriginalOpenUnitLogarithm318.lean: before a2394cd1575a5dadbfc035ec842048d5f0e6bf0ea401688169a6a3b891316544; after dea1c2ebdea02f378f7b44de4bd5c5f26dbb8d663781ddc5ef5fb5fc0358534b.
- OriginalOpenDualCoordinates318.lean: before 2cbc0473db6d66d63b18ad57e88df275377c9102aa53b2dc9fa753cc15b3d813; after ab6d5945c95ad51f1d398c77460e7a0909552a786e9a72dfe16abfca65535737.
- Successor intake SHA256 27e02f3c031a73e8ccc57b18ec93d665069735f016710bfccc63d9faeb3aada3.
- Exact hosted Logarithm failure log SHA256 6dccbd5c80b2ad795764ae2e38f4913b410b57f5766a835b141ee64e5bad9a2f.

## Review
Read both full sources, before/after diffs and exact hosted errors. Logarithm notation declarations fail quotation prechecking on projection syntax, followed by unknown dotted identifiers such as E.symm and B.symm. The repair changes notation RHS projections into explicit CategoryTheory.Iso.commRingCatIsoToRingEquiv applications, and term references E./B. into (E)./(B). projections. No quotPrecheck or other option is relaxed. A deterministic textual transform independently reproduces each complete after file from before using only those two transformations.

Verified the qualified declaration in pinned Mathlib Algebra/Category/Ring/Basic.lean, commit 56a005855ea17e0b0958f73ec801ae140b0a1679, blob c9703b5aa37ad0354cec12982cdae6ae702398b3. It is in namespace CategoryTheory.Iso and constructs the ring equivalence from exactly e.hom.hom and e.inv.hom. Thus the notation names the identical actual sectionsIso and baseIso ring equivalences. Source URL: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Algebra/Category/Ring/Basic.lean

The exp/log maps and inverse laws, reduced-unit condition, complete top-open section types, original coefficient/epsilon compatibility, full dual-ring coordinates and all-unit restriction compatibility remain unchanged. No new carrier, scalar action, nonvanishing condition, theorem premise, or loss of index/open coverage. The later DualCoordinates file has exactly the same source-level notation defect; its repair is preventive propagation of the verified syntax form, not a claim that hosted r7 reached or failed that file.

The successor has the same 213 root Lean filenames and identical ordered intake list as r7, with exactly these two changed files and all other 211 byte-identical. All current APPLICATION source/artifact hashes recompute. Hosted RESULT.packet_sha256 equals actual predecessor intake SHA256 3619921b9d589a13eeb7e99692a981e694cbe318b53b1ff614e942f9b06196ad. This report binds source/intake rather than a recursively refreshed APPLICATION hash.

Conclusion: no source-level blocker for this exact two-file candidate. Hosted replay must still establish notation elaboration and the complete strict module closure. Previous successful modules and this source review do not establish packet or theorem acceptance.
