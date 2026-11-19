# Public replay

The independent review in this directory is preserved as issued. The public copy of its inverse checker differs from the reviewed checker (SHA-256 cd498942fac8944a10ee7ef4a0cce8ac328bb0cb88cd2867017ac285d129e2d5) on one line only: if it cannot find the input next to the script or in the current directory, it now asks for an explicit packet directory. No fallback to a development checkout is used. The public inverse checker is f8ae580ea7279f31a86bcf94f31501216ea595eeb3fbf2805ebe3f6bc310112e (SHA-256). No arithmetic, proof or coefficient was changed. Check the complete public file set against SHA256SUMS.json.

Run `python -B verify.py` for the standard-library table replay, `python -B inverse.py .` for the independent inverse checker (SymPy), and `python -B proofcheck.py` for the arithmetic audit.
