# Two-open dependent empty branch review

PASS for source/current application review, not Lean acceptance.

Candidate859e549be1f11ca4de8944dcfca4b56bee633bfb9db4a5f62af5d47587214d9c; immediate predecessor0b1e7a25e3a4154b7cb2dedc3028a34d34bce06c74b759b14f05662dabb22eea. Manifest a8c16bed1ed5c9283517b55a502113405ff54cfd3f3a9775b74f996b96975a8d; all8 bindings independently verified. Application5a0288b53a9f89c0f82d317459100f7ce1ebb4d6d61bfb00279171e7967dd5be.

The exact one-expression change eta-expands the nested Fin.cases empty branch from Fin.elim0 to fun i => Fin.elim0 i. The actual error reports a nondependent Fin0→?m where dependent (i:Fin0)→Γ(M,![U,V] i.succ.succ) is required. Lambda binding exposes that expected dependent result before applying the native empty eliminator. No new datum or proposition is assumed. The genuine binary cover, ULift universe preservation, both actual pieces, overlap compatibility, thin-category normalization and native gluedTop remain unchanged. All public signatures/options/imports unchanged; read all nine current obligations.

Own positive83 RESULT174737c3fc02372b9a2b229a36056f095051de0b692dcb95d32a1b54414f1530 matches intake181a9fd44cfcacb046c0a82ddcaaa43091d444d17e509d0f4eb98e372969617f. It has75 full module successes then this sole error after1.771s. The earlier canonical0b1e7a25 is therefore not a whole-module pass. Proposed gluing23 propagation of that older canonical must be separately amended to the current source and current evidence, while retaining its own unreached/preventive classification. No local Lean was run; source inspection cannot certify elaboration or downstream gluing.
