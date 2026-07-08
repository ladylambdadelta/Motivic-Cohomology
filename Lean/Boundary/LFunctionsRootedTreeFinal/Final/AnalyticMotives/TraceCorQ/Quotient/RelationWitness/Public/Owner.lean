import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Public.Certificates.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Public.Core.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Public.Generators.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Public.Ledgers.Owner

/-!
# Public relation-witness surfaces

This file aggregates public concrete, ledger, certificate, and generated
relation-witness facades under the `TraceCorQ` namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public relation-witness aggregate: witness certificate ledgers are relation-ledger certificates. -/
theorem TraceCorQ.relationWitness_publicSummary_certificateLedger_eq_relationLedger
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    TraceCorQ.relationWitness_certificateLedger witness =
      witness.ledger.certificateLedger :=
  TraceCorQ.relationWitness_certificateLedger_eq_relationLedger
    witness

/-- Public relation-witness aggregate: imported rectangle counts are payload lengths. -/
theorem TraceCorQ.relationWitness_publicSummary_importedRectangleCount_eq_length
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    TraceCorQ.relationWitness_importedRectangleCount witness =
      (TraceCorQ.relationWitness_importedRectangles witness).length :=
  TraceCorQ.relationWitness_importedRectangleCount_eq_length_importedRectangles
    witness

/-- Public relation-witness aggregate: reflexive witnesses carry the empty ledger. -/
theorem TraceCorQ.relationWitness_publicSummary_refl_ledger
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQ.relationWitness_refl candidate).ledger =
      TraceCorQRelationLedger.empty :=
  TraceCorQ.relationWitness_refl_ledger
    candidate

/-- Public relation-witness aggregate: symmetric witnesses preserve the ledger. -/
theorem TraceCorQ.relationWitness_publicSummary_symm_ledger
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    (TraceCorQ.relationWitness_symm witness).ledger =
      witness.ledger :=
  TraceCorQ.relationWitness_symm_ledger
    witness

/-- Public relation-witness aggregate: transitive witnesses append ledgers. -/
theorem TraceCorQ.relationWitness_publicSummary_trans_ledger
    {left middle right : TraceCorQQuotientCandidate}
    (first : TraceCorQRelationWitness left middle)
    (second : TraceCorQRelationWitness middle right) :
    (TraceCorQ.relationWitness_trans first second).ledger =
      TraceCorQRelationLedger.append first.ledger second.ledger :=
  TraceCorQ.relationWitness_trans_ledger
    first
    second

/-- Public relation-witness aggregate: relation-generator support witnesses use singleton ledgers. -/
theorem TraceCorQ.relationWitness_publicSummary_generator_supportWitness_ledger
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).ledger =
      TraceCorQRelationLedger.singleton relation :=
  TraceCorQ.relationGenerator_supportWitness_ledger
    relation

end AnalyticMotives
end LFunctions
end Boundary
