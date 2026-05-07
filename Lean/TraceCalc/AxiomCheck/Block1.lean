import TraceCalc.MotivicRecognition.ManuscriptSpineTargets
import TraceCalc.LayerB.RealObjects.InternalManuscriptTargets
import TraceCalc.LayerB.RealObjects.SourceHolographyToLayerD

/-!
# Block 1 Axiom Check

Run with:
  lake env lean Lean/TraceCalc/AxiomCheck/Block1.lean 2>&1 | tee /tmp/block1_axioms.txt
-/

namespace AxiomCheckBlock1

open TraceCalc.MotivicRecognition
open TraceCalc.LayerB.RealObjects

#print axioms RewriteCalculusSetup.semantic_dependency_graph_acyclic_invariant
#print axioms RewriteCalculusSetup.canonical_key_total_injective
#print axioms RewriteCalculusSetup.CanNF.CanNF_sound
#print axioms RewriteCalculusSetup.CanNF.CanNF_complete
#print axioms NormalizationPackageData.ofCanNF
#print axioms NormalizationPackageData.ofCanNFFromHolography
#print axioms NormalizationPackageTarget.ofData
#print axioms NormalizationPackageTarget.ofCanNFFromHolography
#print axioms RewriteCalculusSetup.InternalComparisonFaithfulnessTarget.ofIff
#print axioms TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.FoundationsBoundaryBridgeAuxiliaryData.concretePreferredInternalHolographyInterface_realizes_InternalComparisonFaithfulnessTarget
#print axioms NormalizationPackageData.ofConcretePreferredHolography
#print axioms NormalizationPackageTarget.ofConcretePreferredHolography

end AxiomCheckBlock1
