# Independent same-contact p=67 check

For the exact square contact in singleton JSON SHA-256
`d6a1ea6db2d255d824dca7c371a37e5bcda0dcc95cc2aeafdc0355afc3b39d8c`,
I independently set (t=(767389608247987/204)^2) and computed the
five numerators after multiplying by (204^2):
((1396,4007,2611,3484,1037)pmod {67^2}).
The unique factor divisible by 67 is (2399t-1), with numerator
(3484=52cdot 67pmod {67^2}). The denominator is a unit,
the numerator of (t-1) is 47 modulo 67, and (2^{33}=-1\bmod67),
so 67 is an inert contact prime of exact depth one. Consequently the
independently reviewed early-eight theorem (note SHA-256
`63be7c0a74606050d13b362aa4f280f034f8cb531e3c8e04b006a7a112ca4b0a`)
rules out a literal slot-190 PointPair at this particular (t)
for every guarded (h) with the original Lucas labels, including
the singleton retune. This does not affect the separate local
(v_{3162001}(b_{190})=1), and is not a result for other (t)
on the same progression.

Independent reviewer: Vesper (high_review_ci), 2026-11-21 UTC.
