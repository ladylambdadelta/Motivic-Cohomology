import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Compact.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Payload.TraceCalculus.Identity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Payload.TraceCalculus.LedgerCounts.Owner

/-!
# Compact-generator unstable identity trace-calculus payload

This file records trace-bookkeeping, rewrite-step, and certificate-ledger
payload for the unstable identity attached to a compact geometric analytic
generator.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Source endpoint bookkeeping of the unstable identity is the generator's bookkeeping payload. -/
theorem TraceAnalyticGeometricGenerator.unstableIdentity_sourceTraceBookkeepingCount
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableIdentity.sourceTraceBookkeepingCount =
      generator.traceBookkeepingCount :=
  TraceUnstableAnalyticMotiveHom.id_sourceTraceBookkeepingCount
    generator.unstableMotive

/-- Target endpoint bookkeeping of the unstable identity is the generator's bookkeeping payload. -/
theorem TraceAnalyticGeometricGenerator.unstableIdentity_targetTraceBookkeepingCount
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableIdentity.targetTraceBookkeepingCount =
      generator.traceBookkeepingCount :=
  TraceUnstableAnalyticMotiveHom.id_targetTraceBookkeepingCount
    generator.unstableMotive

/-- Source endpoint rewrite-step count of the unstable identity is the generator's rewrite payload. -/
theorem TraceAnalyticGeometricGenerator.unstableIdentity_sourceRewriteStepCount
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableIdentity.sourceRewriteStepCount =
      generator.rewriteStepCount :=
  TraceUnstableAnalyticMotiveHom.id_sourceRewriteStepCount
    generator.unstableMotive

/-- Target endpoint rewrite-step count of the unstable identity is the generator's rewrite payload. -/
theorem TraceAnalyticGeometricGenerator.unstableIdentity_targetRewriteStepCount
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableIdentity.targetRewriteStepCount =
      generator.rewriteStepCount :=
  TraceUnstableAnalyticMotiveHom.id_targetRewriteStepCount
    generator.unstableMotive

/-- Source endpoint ledger of the unstable identity is the generator's certificate ledger. -/
theorem TraceAnalyticGeometricGenerator.unstableIdentity_sourceCertificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableIdentity.sourceCertificateLedger =
      generator.certificateLedger :=
  TraceUnstableAnalyticMotiveHom.id_sourceCertificateLedger
    generator.unstableMotive

/-- Target endpoint ledger of the unstable identity is the generator's certificate ledger. -/
theorem TraceAnalyticGeometricGenerator.unstableIdentity_targetCertificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableIdentity.targetCertificateLedger =
      generator.certificateLedger :=
  TraceUnstableAnalyticMotiveHom.id_targetCertificateLedger
    generator.unstableMotive

/-- Source endpoint bookkeeping of the unstable identity is counted by the generator ledger. -/
theorem TraceAnalyticGeometricGenerator.unstableIdentity_sourceTraceBookkeepingCount_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableIdentity.sourceTraceBookkeepingCount =
      generator.certificateLedger.traceBookkeepingCount :=
  Eq.trans
    (TraceAnalyticGeometricGenerator.unstableIdentity_sourceTraceBookkeepingCount generator)
    (TraceAnalyticGeometricGenerator.traceBookkeepingCount_eq_certificateLedger generator)

/-- Target endpoint bookkeeping of the unstable identity is counted by the generator ledger. -/
theorem TraceAnalyticGeometricGenerator.unstableIdentity_targetTraceBookkeepingCount_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableIdentity.targetTraceBookkeepingCount =
      generator.certificateLedger.traceBookkeepingCount :=
  Eq.trans
    (TraceAnalyticGeometricGenerator.unstableIdentity_targetTraceBookkeepingCount generator)
    (TraceAnalyticGeometricGenerator.traceBookkeepingCount_eq_certificateLedger generator)

/-- Source endpoint rewrite-step count of the unstable identity is counted by the generator ledger. -/
theorem TraceAnalyticGeometricGenerator.unstableIdentity_sourceRewriteStepCount_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableIdentity.sourceRewriteStepCount =
      generator.certificateLedger.rewriteStepCount :=
  Eq.trans
    (TraceAnalyticGeometricGenerator.unstableIdentity_sourceRewriteStepCount generator)
    (TraceAnalyticGeometricGenerator.rewriteStepCount_eq_certificateLedger generator)

/-- Target endpoint rewrite-step count of the unstable identity is counted by the generator ledger. -/
theorem TraceAnalyticGeometricGenerator.unstableIdentity_targetRewriteStepCount_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableIdentity.targetRewriteStepCount =
      generator.certificateLedger.rewriteStepCount :=
  Eq.trans
    (TraceAnalyticGeometricGenerator.unstableIdentity_targetRewriteStepCount generator)
    (TraceAnalyticGeometricGenerator.rewriteStepCount_eq_certificateLedger generator)

end AnalyticMotives
end LFunctions
end Boundary
