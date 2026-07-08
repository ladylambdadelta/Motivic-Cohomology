import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.InvertedInputs.Payload.TraceCalculus.Owner

/-!
# Certificate ledgers for unstable localization-input isomorphisms

This file exposes source, target, and endpoint certificate ledgers for the hom
and inverse of each localization-input isomorphism after passage to the
unstable analytic-motive envelope.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The unstable isomorphism hom source ledger is the input source ledger. -/
theorem TraceLocalizationInput.unstableIso_hom_sourceCertificateLedger
    (input : TraceLocalizationInput) :
    input.unstableIso.hom.sourceCertificateLedger =
      input.sourceObject.certificateLedger :=
  TraceLocalizationInput.localizedWordIso_hom_sourceCertificateLedger
    input

/-- The unstable isomorphism hom target ledger is the input target ledger. -/
theorem TraceLocalizationInput.unstableIso_hom_targetCertificateLedger
    (input : TraceLocalizationInput) :
    input.unstableIso.hom.targetCertificateLedger =
      input.targetObject.certificateLedger :=
  TraceLocalizationInput.localizedWordIso_hom_targetCertificateLedger
    input

/-- The unstable isomorphism inverse source ledger is the input target ledger. -/
theorem TraceLocalizationInput.unstableIso_inv_sourceCertificateLedger
    (input : TraceLocalizationInput) :
    input.unstableIso.inv.sourceCertificateLedger =
      input.targetObject.certificateLedger :=
  TraceLocalizationInput.localizedWordIso_inv_sourceCertificateLedger
    input

/-- The unstable isomorphism inverse target ledger is the input source ledger. -/
theorem TraceLocalizationInput.unstableIso_inv_targetCertificateLedger
    (input : TraceLocalizationInput) :
    input.unstableIso.inv.targetCertificateLedger =
      input.sourceObject.certificateLedger :=
  TraceLocalizationInput.localizedWordIso_inv_targetCertificateLedger
    input

/-- The unstable isomorphism hom endpoint ledger is source followed by target. -/
theorem TraceLocalizationInput.unstableIso_hom_endpointCertificateLedger
    (input : TraceLocalizationInput) :
    input.unstableIso.hom.endpointCertificateLedger =
      ResidueChannelCertificateLedger.append
        input.sourceObject.certificateLedger
        input.targetObject.certificateLedger :=
  TraceLocalizationInput.localizedWordIso_hom_endpointCertificateLedger
    input

/-- The unstable isomorphism inverse endpoint ledger is target followed by source. -/
theorem TraceLocalizationInput.unstableIso_inv_endpointCertificateLedger
    (input : TraceLocalizationInput) :
    input.unstableIso.inv.endpointCertificateLedger =
      ResidueChannelCertificateLedger.append
        input.targetObject.certificateLedger
        input.sourceObject.certificateLedger :=
  TraceLocalizationInput.localizedWordIso_inv_endpointCertificateLedger
    input

end AnalyticMotives
end LFunctions
end Boundary
