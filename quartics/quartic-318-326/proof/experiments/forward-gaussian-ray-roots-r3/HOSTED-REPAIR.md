# Exact replay repair and final root-family binder

Tested frozen213r1, intake98f390e6c4111ba103ad61b73550efaaddac59fc97b501fd8f8572c10213e6e1, replay42649103375 at e36a6803.221 verified predecessors reused and nine draft modules passed. The prior LocalPointDifference318 repair passes in2.018s. CompactLocalPointCoding318 fails in2.271s at63,124,141.

Line63: after metric simplification the product norm remained intact. Add the pinned exact Prod.norm_def to expose its maximum of coordinate norms.
Line124: by_contra! creates a real-order expression using Real.linearOrder.toLT, while the formal-subgroup comparison expects opaque Real.instLT. Scope backward.isDefEq.respectTransparency=false to finite_formal_quotient only, permitting the same definitional real-order and norm/absolute-value instances to align. No logical premise or expression is changed.
Line141: q and H are local lets; the original simp did not turn n•qP into the quotient class of n•P. Explicitly change the target to q(n•P)=0 and compose typed map_nsmul with the original hzero.

The same successor retains the217r2 source-preflight correction: reduce the final let-bound root family before introducing the following natural h. All statements, fields, points, signs, indices, moduli and the finite1M budget are unchanged.215 sources are exact217r1 copies and two have narrow proof-only changes. Hosted validation remains pending; no local Lean was run.
