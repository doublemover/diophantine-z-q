# Actual finite Euler-product index bridge

Status: kernel-checked. One module, six public theorems and ten recursively audited declarations; only propext, Classical.choice and Quot.sound.

`eulerProduct N` is the actual product of1+1/p over the distinct prime factors of the natural integer N. For R>0 and every prime factor of N dividing R, `euler_product_bound` proves

    eulerProduct N < 3 R^(1/32).

R need not be squarefree. The proof splits the actual finite prime set at13. The small set is contained in{2,3,5,7,11}, whose product is1152/385<3. Each large factor satisfies(1+1/p)^32≤p. The distinct large primes have product dividing R, not merely individually bounded by R, so taking the thirty-second root is valid.

`index_bound` and `index_bound_of_le` prove

    d < 2^14 C R^(97/32)

from the actual Euler index equality or upper bound d≤N t eulerProduct N, N≤C R², t≤4608R, and prime support. `jacobian_growth_of_index` composes this with the actual logarithm log(6dN) and the earlier metric scalar budget, removing the free index-height premise from that consumer.

The actual modular cover, its index formula, conductor/support theorem and order bound for t remain separate inputs. This packet does not assume or prove the final FiveContact49Height theorem.

Replay: `bash run.sh`; complete recursive audit is in build.log.
