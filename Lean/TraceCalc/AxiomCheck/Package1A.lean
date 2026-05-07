import TraceCalc.LayerB.RealObjects.CompletedRecord
import TraceCalc.LayerB.RealObjects.CanonicalNormalForm

/-!
# Axiom check for Package 1A declarations

Run with:
  lake env lean Lean/TraceCalc/AxiomCheck/Package1A.lean 2>&1 | tee /tmp/package1a_axioms.txt

This file captures literal `#print axioms` output for the four theorem rows in Package 1A.
-/

namespace AxiomCheckP1A

open TraceCalc.LayerB.RealObjects.RewriteCalculusSetup

-- Row 1.13: semantic_dependency_graph_acyclic_invariant
#print axioms semantic_dependency_graph_acyclic_invariant

-- Row 1.15: canonical_key_total_injective
#print axioms canonical_key_total_injective

-- Row 1.20: CanNF.CanNF_sound
#print axioms CanNF.CanNF_sound

-- Row 1.21: CanNF.CanNF_complete
#print axioms CanNF.CanNF_complete

end AxiomCheckP1A
