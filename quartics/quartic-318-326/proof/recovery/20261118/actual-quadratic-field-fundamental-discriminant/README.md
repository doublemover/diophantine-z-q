# Fundamental discriminant of the actual quadratic CM subfield

These three research sources are independently checked mathematically and against the pinned Lean interfaces. They have not been replayed in Lean.

1. A primitive quadratic generator in the full ring of integers has fundamental quadratic-polynomial discriminant. A putative defect p², including p=2, would produce an integral element whose second coordinate is 1/p.
2. For every number field K of degree two, the signed field discriminant itself is fundamental. In an arbitrary rank-two integral basis B, the first coordinate of 1·B₀=B₀ supplies a Bézout identity for the two coordinates of 1. A unimodular basis change puts 1 first. Writing θ²=a+tθ in this basis gives the actual Gram determinant t²+4a.
3. For a quadratic subfield K of a number field F unramified outside the five-contact set together with the four bad primes, this yields |disc K|≤4·badProduct·radical(u,v), without assuming fundamentality.

The last module imports the separately reviewed actual-field support sources. Construction of the controlled field, its ramification from the marked surface, the CM Faltings height input, and overall theorem acceptance are not asserted here.
