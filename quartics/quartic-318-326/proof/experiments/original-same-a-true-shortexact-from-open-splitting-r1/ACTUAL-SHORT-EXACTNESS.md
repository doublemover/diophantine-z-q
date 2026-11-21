# The actual additive row is short exact if its true restrictions split

This bridge uses the same concrete additive-site functor as the
strict green actual closed-fibre complex in 44951236848. Local data
are the splits of the true restrictions of that one module complex
on genuine open immersion charts covering the actual scheme.
No exactness of a nonflat inverse image or of an arbitrary cohomology
comparison is claimed.

At any actual point, use the natural stalk comparison for the chosen
cover chart. Additivity maps the local split complex to a split
complex of additive stalks. For the original additive sheaves,
stalkwise exactness proves middle exactness. Apply the same criterion
to the augmented (0,f) and (g,0) rows, yielding the genuine mono and
epi endpoints. This gives the true ShortExact input to the accepted
Ext boundary. Not construction of the charts or their splits; those
are supplied by the exact affine closed-fibre owner when green and
its subsequent local splitting proof.

This exact source-only revision installs the additive functor using
the concrete site rather than relying on reduction of the
semireducible TopCat.Sheaf name. The usual HasSheafify premise is
explicit for the stalk step, just as in the genuine boundary owner.
