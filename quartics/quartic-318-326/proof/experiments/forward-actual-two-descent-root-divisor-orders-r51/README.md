# Dyadic residue subring zero/one closure repair

Fresh hosted run43863751165 passed DyadicPrueferCarrier318 but rejected the next residue source at its zero/one closure proofs: bare intros did not expose the membership predicate, and map_one had an unresolved hom receiver. The repair explicitly changes each goal to the coordinate closure equation, introduces m,n,h and supplies reduction m n h to map_zero/map_one.

Only two proof bodies change. All declarations, mathematical definitions, statements, other proofs and imports are unchanged; all1324 other predecessor sources remain byte-identical, including the freshly passed carrier. This successor revises frozen49 directly and excludes held50. No local Lean, acceptance promotion, kernel bypass or new arithmetic assumption.
