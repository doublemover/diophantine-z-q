# Actual Weber mixed kernel plus finite reduction

This packet is independent of the origin–origin Vieta and full specialization
drafts. Three exact hosted green parents are carried byte-for-byte (PointMap
selection run 44932054428, 3 checked and 33 audited); ValuedKernelChart from the
older point specialization packet remains source-only.

For the actual normalized kernel point P=(t/w,−1/w) and finite Q=(A,B), let
D=t−Aw and H=2B+(3A²−1)t−(A³+A)w. From w+t w²=t³ and B²=A³−A, the literal
cleared identity is

    w(1+Bw)² − (t+2Aw)(t−Aw)² = w² H.

In the valuation subring choose the actual units u=(1+tw)⁻¹ and
β=(1−A t²u)⁻¹, both of residue 1. Thus w=t³u and Dβ=t, with D nonzero on
the nonzero affine kernel branch. Over the ambient field the stock slope
is −(1+Bw)/D and the actual reflected coordinates are

    X=A+t u β² H,   Y=−B+(1+Bw)u β³ H.

These products are integral; reduction gives X↦A and Y↦−B+2B=B, including
the residual 2-torsion cases. The original nonintegral slope is not reduced.
The zero kernel input is stock O+Q=Q. For the nonzero branch, x(P)≠A follows
from x(P) outside and A inside the same valuation subring. No abstract
addHom (or equivariance / Frobenius hypothesis) is used.

Native pins: Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679, Affine.Formula
blob 4a3d102483d6d151630c06ab77c1f534b3ed6414 (slope_of_X_ne, addX, negAddY,
addY, nonsingular_add), Affine.Point blob cf286abce5445fc7b5572694c1e074ce7a859c23
(Point.add_of_X_ne, zero_def). The new files are only authored source;
no new hosted result claimed. The independent finite control is supplemental.
