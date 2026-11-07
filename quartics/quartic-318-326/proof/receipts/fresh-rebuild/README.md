# Fresh Lean rebuild

`receipt.json` records the kernel-checked rebuild of commit `426ebc9e043bb49a8cb59d209855e4bce95005ed`, with logs and source/dependency checks. Its source paths are preserved through relative links to the unchanged Lean files. `318-manifest.json` and `components-manifest.json` preserve the manifests verified by `source-check.json`; later documentation corrections to the arithmetic-obligation map do not change the compiled Lean sources or retroactively change this receipt.

The full audits cover 1,968 declarations in the original 18 concrete modules and 881 declarations in the original 50 component modules. The additional constant-lift receipt covers seven theorems separately. Official Lean 4.35.0 and the pinned Mathlib cache are trusted inputs. The literal 326-polynomial replay and global source arithmetic are not proved.

From the contribution package root, unpack inputs, install the pinned dependencies, then run `bash proof/verify_all.sh` to rebuild and repeat all three checks.
