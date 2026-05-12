import TraceCalc.MotivicRecognition.ManuscriptSpineTargets
import TraceCalc.LayerB.RealObjects.CanonicalReconstructionEngine
import TraceCalc.LayerB.RealObjects.TraceDifferential
import TraceCalc.LayerD.ConcretePeriodFaithfulness

/-!
# Status

Audit/support only.

This file is not part of the public period-conjecture proof route. It is a
standalone importability/readiness seal used to check that key production
surfaces coexist without pulling them into the exported theorem boundary.

# Production Seal

Cross-cutting seal for production readiness. This file intentionally checks
that key production surfaces are present and importable together.

Classification notes:
- Computational CanNF is the intended production path:
  `CanonicalReconstructionEngine.ofComputationalCanNF`.
- Semantic quotient CanNF is reference/spec only:
  `semanticQuotientFrontierWordCompleteNormalizer` and
  `CanonicalReconstructionEngine.ofClosedCanNF`.
- LayerG mock period modules are non-production and intentionally not imported.
- `PeriodFaithfulnessContext` is an abstract framework, not the classical
  production period gate.
- `AdminRelation := Eq` remains the production safety baseline.
- Sink deletion obligations route through typed geometric rewrite data
  (`sinkDeletionGeometricRule`), not arbitrary admin rewriting.
-/

namespace TraceCalc

section ProductionSealChecks

-- Canonical reconstruction engine constructors.
#check LayerB.RealObjects.RewriteCalculusSetup.CanonicalReconstructionEngine.ofClosedCanNF
#check LayerB.RealObjects.RewriteCalculusSetup.CanonicalReconstructionEngine.ofComputationalCanNF

-- Reference/spec semantic quotient normalizer (non-production runtime path).
#check LayerB.RealObjects.RewriteCalculusSetup.semanticQuotientFrontierWordCompleteNormalizer
#check LayerB.RealObjects.RewriteCalculusSetup.quotientFrontierWordCompleteNormalizer

-- Trace differential production constructors from boundary-gluing witness data.
#check LayerB.RealObjects.RewriteCalculusSetup.SinkDeletionProducesTraceEquivZero.ofBoundaryGluingWitnessData
#check LayerB.RealObjects.RewriteCalculusSetup.BoundaryTraceEquivZeroData.ofBoundaryGluingWitnessData

-- Concrete classical period-faithfulness bridge theorems.
#check LayerD.overScalarRealization_eq_of_basisFreePeriodMap_eq
#check LayerD.full_morphism_eq_of_betti_deRham_basisFreePeriodMap_eq

-- Final manuscript spine target artifacts.
#check MotivicRecognition.InternalManuscriptSpineTarget
#check MotivicRecognition.TraceCategoryEquivalentToDMgmQTarget
#check MotivicRecognition.CanonicalDMgmEquivalenceTarget
#check MotivicRecognition.PeriodConjectureSpineTarget

end ProductionSealChecks

end TraceCalc
