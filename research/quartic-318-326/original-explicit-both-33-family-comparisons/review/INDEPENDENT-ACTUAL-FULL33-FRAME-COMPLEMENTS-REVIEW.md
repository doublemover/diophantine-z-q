# Independent review: both actual full-33 frame complements

**Verdict:** PASS (2026-11-21), for the classical same-family overlap on the full principal-frame loci.

## Exact binding

| Piece | Author checksum-list SHA-256 | Paper SHA-256 |
|---|---|---|
| Add an 11-frame to actual level 3 | `628435039ed25557849fe34e06f8f631ab42278902768f0e5ed5eaea4e30e1e0` | `00ea9fabc1452def9d1a44f69bffe5731036780733d04ebd060816fdc21c0d28` |
| Add a 3-frame to actual level 11 | `041ad627d5529413d4c0a4901d12a1af5d60034b9f9e2cdaf8479ad76fbc4216` | `fab11599ab0fb4ea23080f8e7da1220dae219195c2e588d08c1ba635beab43b8` |
| Full-frame clopen handoff | `2383afef8ed5acb2ea713035d56dbd5ff2d4f3ab211e54c2b60f426bd2a7f7c0` | `902cf324051655cce99fd447164e4feea91b7b459ea8ec593ff280d174363ce0` |

The author checksums passed in each packet. I independently replayed the two finite checks byte for byte. The output digests are `cf58c3890f91cb6aba613cc6f7b761257b4cbd5e418261a6afdd460d64792b11` and `657b7336c1b996449d36e1a479ce83140d70395f33171dd6af52e18ca89588c8` respectively.

## Mathematical checks

- **Tame torsion on the actual level-3 family.** The actual finite étale 11-torsion has rank 11⁴. The two matrix idempotents and inverse off-diagonal maps give the regular left M₂(F₁₁) module on each geometric fibre, even at 2, 5 and 7 on this base. A matrix fails to generate that regular left module if and only if a nonzero row annihilates its columns. The twelve listed row directions are exact; pairwise kernel intersections are zero and their complement has degree 13200. Evaluation at 1 identifies full O-linear frames with this clopen complement on every test base, not just over fields.
- **Ramified acting ring on the actual level-11 family.** The base inverts 3, although the acting quaternion algebra is division at 3. The genuine T₃, rationalized, is a rank-one left division-algebra module. Its stable lattice is O₃α for a least-valuation vector α: the quotient xα⁻¹ has nonnegative valuation. Thus reduction gives the regular left O₃/3O₃ module, not just its semisimplification. By [Voight, Theorem 13.3.11](https://link.springer.com/chapter/10.1007/978-3-030-56694-4_13), a nonzero radical reduction Π has valuation one half; its left-action kernel is exactly the size-nine radical. The clopen unit complement has degree 72 and represents one full 3-frame for each of its points.
- **Same family, same marks, two different forgetful maps.** The projectors [22] and [12] split level 33 into the exact retained 3- and 11-frames. Neither changes the sign of the retained frame. There is no further quotient by ±1 with a full old fine mark fixed. Yoneda yields the actual two Cartesian universal-family squares with the same chosen generic level-33 lift and the same polarization. An actual generic section of the finite algebra over O_L[1/33] lands in that same ring by integrality and normality, and uniqueness identifies the two extensions. The bundled Lean head with source digest `95c4c6ac0fdb270489833630593c3147c80a1fe5cd8a071dc57b1f825f15a173` is precisely this ring-theoretic step, not a compiled proof of either geometric square.
- **Published convention and scope.** [Yuan, §2.1 and Theorem 1.1](https://arxiv.org/html/2205.11334v2#S2.SS1) give the fine models and the canonical polarization and Kodaira–Spencer assertions. The displayed phrase “O-linear map” alone does not imply it is a full frame. The full-isomorphism locus of the descended finite étale map is clopen; the actual chosen full generic marks, integral proper extensions, and restricted families and line equalities stay on it. [Buzzard, Definition 1.1](https://www.ma.imperial.ac.uk/~buzzard/maths/research/papers/shimura.pdf#page=3) supplies the explicit isomorphism convention at tame 11, not a bad-prime representability theorem. The proof need not assert that the full locus exhausts any broader interpretation of the model.

No full frame is asserted at a noninvertible level prime. There is no native PEL model, Lean build, or new global period conclusion certified by this review.

*Signed: independent proof reviewer, 2026-11-21.*
