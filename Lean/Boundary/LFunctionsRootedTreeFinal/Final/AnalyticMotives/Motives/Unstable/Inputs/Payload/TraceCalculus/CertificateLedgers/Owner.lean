import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.Payload.TraceCalculus.Owner

/-!
# Certificate ledgers for unstable localization-input arrows

This file exposes the endpoint certificate-ledger identities for localization
input arrows after they are viewed as morphisms in the unstable
analytic-motive envelope.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The unstable forward morphism source ledger is the input source ledger. -/
theorem TraceLocalizationInput.unstableForward_sourceCertificateLedger
    (input : TraceLocalizationInput) :
    input.unstableForward.sourceCertificateLedger =
      input.sourceObject.certificateLedger :=
  TraceLocalizationInput.localizedForwardArrow_sourceCertificateLedger
    input

/-- The unstable forward morphism target ledger is the input target ledger. -/
theorem TraceLocalizationInput.unstableForward_targetCertificateLedger
    (input : TraceLocalizationInput) :
    input.unstableForward.targetCertificateLedger =
      input.targetObject.certificateLedger :=
  TraceLocalizationInput.localizedForwardArrow_targetCertificateLedger
    input

/-- The unstable inverse morphism source ledger is the input target ledger. -/
theorem TraceLocalizationInput.unstableInverse_sourceCertificateLedger
    (input : TraceLocalizationInput) :
    input.unstableInverse.sourceCertificateLedger =
      input.targetObject.certificateLedger :=
  TraceLocalizationInput.localizedInverseArrow_sourceCertificateLedger
    input

/-- The unstable inverse morphism target ledger is the input source ledger. -/
theorem TraceLocalizationInput.unstableInverse_targetCertificateLedger
    (input : TraceLocalizationInput) :
    input.unstableInverse.targetCertificateLedger =
      input.sourceObject.certificateLedger :=
  TraceLocalizationInput.localizedInverseArrow_targetCertificateLedger
    input

/-- The unstable forward morphism endpoint ledger is source followed by target. -/
theorem TraceLocalizationInput.unstableForward_endpointCertificateLedger
    (input : TraceLocalizationInput) :
    input.unstableForward.endpointCertificateLedger =
      ResidueChannelCertificateLedger.append
        input.sourceObject.certificateLedger
        input.targetObject.certificateLedger :=
  TraceLocalizationInput.localizedForwardArrow_endpointCertificateLedger
    input

/-- The unstable inverse morphism endpoint ledger is target followed by source. -/
theorem TraceLocalizationInput.unstableInverse_endpointCertificateLedger
    (input : TraceLocalizationInput) :
    input.unstableInverse.endpointCertificateLedger =
      ResidueChannelCertificateLedger.append
        input.targetObject.certificateLedger
        input.sourceObject.certificateLedger :=
  TraceLocalizationInput.localizedInverseArrow_endpointCertificateLedger
    input

end AnalyticMotives
end LFunctions
end Boundary
