# Exact r13 hosted diagnosis to r14 exceptional branch proof

Run 44867152804 on the immutable r13 RC62 selection has 59 passing,
1 compiler error, 2 import-blocked and 42 unselected; 952 audits.
The old parser and all r12 diagnostic sites passed. The sole direct
new error is CTActualDualConnecting318 line 84, column 8. The old
explicit hD already proves the exceptional scalar -3*n² and is
identical in sign; the elaborator leaves a dependent
"if h : True then classOf (-3*n^2) … else classOf 0 …" under the
unchanged native quadratic connecting map. On that sole proof line,
the successor uses both the exact literal (0:K)=0 guard and the
already-normalized True guard with dite_eq_left. The successful
nonexceptional branch and public statements remain untouched. The
True guard is the same normalization seam used in the independently
green OriginalCasselsActualLocalSystem318. The stage script verifies
104 raw ancestor source hashes, all source/build log hashes, one
exact owner edit, 103 unchanged and the original ordered RC62
selected scope (including an untouched unselected 104 terminal).
No Lean build, CI launch or remote writes.
