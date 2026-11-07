# Actual maximal-stack Kodaira–Spencer binding

`MAXIMAL-KS-PRODUCER.md` binds the actual full-level-three quaternionic fiber surface to the universal surface on Yuan's maximal moduli stack and proves the exact application identity

    h(ω_max² at y) = 2 h_Yuan(A) + log210
                     = 2 h_L2(A) + 2logπ + log210.

The level is maximal for this calculation, so n(U)=1. Forgetting the full marking leaves the surface unchanged. Pulling back the maximal canonical line is not replacement by a level-three dualizing line, so neither a cover degree nor a ramification term is introduced. The integral-section extension may be larger than the separately bounded isogeny field; stable normalized height is unchanged.

This is a classical moduli/theorem-application proof, not a Lean construction of stacks or Arakelov line bundles. It consumes the previously constructed actual fiber/model and the independently reviewed integral sections and smooth metric bound. It does not by itself close FiveContact49Height.

The author PDF was freshly downloaded from https://faculty.bicmr.pku.edu.cn/~yxy/preprints/explicit_KS.pdf. Printed pages 2, 3, 6 and 12 were independently visually inspected. Their images and text extraction are included. `receipt.json` records exact scope and hashes; `SHA256SUMS` verifies the frozen local files.
