# Existing gluing34 failure: explicit mapped identity decomposition
Exact head 960090b9a5b895bc9350511ea373ed42bfeb475d, run43790660415, own gluing34 intake a9b26984a0bdb13e39bc63c9c29328f186fda16bb07643832ea262b8b945d644.
94 whole-module passes including OriginalAffineLineDualFrame318 (1.267 s); NonreducedAffineLineHOne318 fails3.774 s. The actual remaining goal is the image of the finite identity sum. Simp's total/map_id arguments were unused.
Only replace those ineffective simp arguments by explicit congrArg of the actual passing total theorem, followed by this functor's map_id on the literal L.object. All source maps, finite indices, hypotheses, imports, options and statements remain unchanged.
Source candidate only. No local Lean, no whole-module success, no current packet propagation or activation.
