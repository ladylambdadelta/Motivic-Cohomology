import TraceCalc.MotivicRecognition.ManuscriptSpineTargets
import TraceCalc.LayerB.RealObjects.InternalManuscriptTargets

/-!
# Axiom check for Package 1B declarations

Run with:
  lake env lean Lean/TraceCalc/AxiomCheck/Package1B.lean 2>&1 | tee /tmp/package1b_axioms.txt

This file captures literal `#print axioms` output for Package 1B noncomputable defs.
-/

namespace AxiomCheckP1B

open TraceCalc.MotivicRecognition
open TraceCalc.LayerB.RealObjects

-- Row 2.3: ofCanNF
#print axioms NormalizationPackageData.ofCanNF

-- Row 2.4: ofCanNFFromHolography
#print axioms NormalizationPackageData.ofCanNFFromHolography

-- Row 2.5: ofData
#print axioms NormalizationPackageTarget.ofData

-- Row 2.6: ofCanNFFromHolography (target version)
#print axioms NormalizationPackageTarget.ofCanNFFromHolography

-- Row 2.8: ofIff (from LayerB)
#print axioms RewriteCalculusSetup.InternalComparisonFaithfulnessTarget.ofIff

end AxiomCheckP1B
