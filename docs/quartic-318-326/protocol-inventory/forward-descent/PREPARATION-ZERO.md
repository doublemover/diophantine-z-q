# Direct preparation-zero locator, retained in active V13

This is a separate addendum; it does not amend the frozen completeness trace or its acceptance.

`manuscripts/quartic_v11.tex`, whole SHA-256 `1210d2e6f409e502fc9c95afc248fac16a9df48c760a396143780c20ec80b662`, lines 10556–10628, label `v5:preparation-zero-bridge`, already contains the complete theorem and its internal proof. Exact excerpt hash is in `APPLICATION.json`.

Its completeness input is b∈Q×, positive, square reduced denominator, square in Q_2,Q_3,Q_17, b<17, v_2(b)≥3, v_3(b)≥1, v_17(b)≥2. It produces p²=B(1−e)(1+3e), h=e(B−b²), and Bq²=(s²−B h)(s²+3B h), B=17b, without new guards on e,p,q,s,h.

The actual proof sets V=B²(1−b/17). The valuation thresholds make V a square at the three small primes and positivity makes it positive. The positive squarefree representatives μ of B and θ of V satisfy μ≡17 mod24, θ≡1 mod24, have disjoint supports, and are mutual local squares. At a prime dividing μ outside {2,3,17}, v(b) is positive odd because the reduced denominator is square. At a prime dividing θ, odd valuation of V rules out both v(b)>0 and v(b)<0, so v(b)=0 and B≡17² modulo that prime. The earlier simultaneous realization lemma then supplies both points.

The point-to-conic map is written in the theorem: V=θc²; scale the second point by c; normalize the first abscissa Ba² to B using a; write the second abscissa Bs²; set e=e0/B, p=y1/B, q=y2/(B²s). The relation e0V=B²h explains the required B h factors. Comparing with the existing component uses e_component=B·e_V11, not equality of the two e variables.

Thus the Brox v3 preparation-zero citation in arithmetic.md can be accompanied by this exact internal V11 locator. No unpublished external Brox theorem need be added to the trust base for this finite pole input. This does not discharge the RC/simultaneous-realization premises, supply the compatible common W, or assemble the final 288-row witness. A non-author must review any proposed manuscript citation change; no such edit is made here.

Active Version13 has the exact same theorem and proof at lines10563–10635, whole SHA-256 `9db71bbfcefb37db56eabcf40a5f9dd85de9ed58294635da3dbf6d4f5caa8fcd`. The excerpt is byte-identical; see `version-comparison.json`. This addendum retains the earlier V11 source location for history and does not change its prior acceptance.
