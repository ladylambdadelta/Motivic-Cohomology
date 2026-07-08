import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.FormalSums.Owner

/-!
# Public typed trace-correspondence formal sums

This file exposes certificate and payload formulas for typed finite formal
sums of trace-correspondence terms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes raw zero typed formal sums. -/
theorem AnalyticMotivesRoot.traceCorQHomFormalSum_zero_raw
    (source target : TraceCorQObject) :
    (TraceCorQHomFormalSum.zero source target).raw =
      TraceCorQFormalSum.zero :=
  TraceCorQHomFormalSum.zero_raw
    source
    target

/-- The top root exposes zero typed formal-sum certificate ledgers. -/
theorem AnalyticMotivesRoot.traceCorQHomFormalSum_zero_certificateLedger
    (source target : TraceCorQObject) :
    (TraceCorQHomFormalSum.zero source target).certificateLedger =
      ResidueChannelCertificateLedger.empty :=
  TraceCorQHomFormalSum.zero_certificateLedger
    source
    target

/-- The top root exposes zero typed formal-sum imported counts. -/
theorem AnalyticMotivesRoot.traceCorQHomFormalSum_zero_importedRectangleCount
    (source target : TraceCorQObject) :
    (TraceCorQHomFormalSum.zero source target).importedRectangleCount =
      0 :=
  TraceCorQHomFormalSum.zero_importedRectangleCount
    source
    target

/-- The top root exposes zero typed formal-sum imported rectangles. -/
theorem AnalyticMotivesRoot.traceCorQHomFormalSum_zero_importedRectangles
    (source target : TraceCorQObject) :
    (TraceCorQHomFormalSum.zero source target).importedRectangles =
      [] :=
  TraceCorQHomFormalSum.zero_importedRectangles
    source
    target

/-- The top root exposes zero typed formal-sum bookkeeping counts. -/
theorem AnalyticMotivesRoot.traceCorQHomFormalSum_zero_traceBookkeepingCount
    (source target : TraceCorQObject) :
    (TraceCorQHomFormalSum.zero source target).traceBookkeepingCount =
      0 :=
  TraceCorQHomFormalSum.zero_traceBookkeepingCount
    source
    target

/-- The top root exposes zero typed formal-sum rewrite-step counts. -/
theorem AnalyticMotivesRoot.traceCorQHomFormalSum_zero_rewriteStepCount
    (source target : TraceCorQObject) :
    (TraceCorQHomFormalSum.zero source target).rewriteStepCount =
      0 :=
  TraceCorQHomFormalSum.zero_rewriteStepCount
    source
    target

/-- The top root exposes raw singleton typed formal sums. -/
theorem AnalyticMotivesRoot.traceCorQHomFormalSum_singleton_raw
    (source target : TraceCorQObject)
    (coefficient : Rat)
    (generator : TraceCorQGenerator)
    (source_eq : generator.source = source)
    (target_eq : generator.target = target) :
    (TraceCorQHomFormalSum.singleton
      source
      target
      coefficient
      generator
      source_eq
      target_eq).raw =
      TraceCorQFormalSum.singleton coefficient generator :=
  TraceCorQHomFormalSum.singleton_raw
    source
    target
    coefficient
    generator
    source_eq
    target_eq

/-- The top root exposes singleton typed formal-sum certificate ledgers. -/
theorem AnalyticMotivesRoot.traceCorQHomFormalSum_singleton_certificateLedger
    (source target : TraceCorQObject)
    (coefficient : Rat)
    (generator : TraceCorQGenerator)
    (source_eq : generator.source = source)
    (target_eq : generator.target = target) :
    (TraceCorQHomFormalSum.singleton
      source
      target
      coefficient
      generator
      source_eq
      target_eq).certificateLedger =
      ResidueChannelCertificateLedger.append
        generator.certificateLedger
        ResidueChannelCertificateLedger.empty :=
  TraceCorQHomFormalSum.singleton_certificateLedger
    source
    target
    coefficient
    generator
    source_eq
    target_eq

/-- The top root exposes singleton typed formal-sum imported counts. -/
theorem AnalyticMotivesRoot.traceCorQHomFormalSum_singleton_importedRectangleCount
    (source target : TraceCorQObject)
    (coefficient : Rat)
    (generator : TraceCorQGenerator)
    (source_eq : generator.source = source)
    (target_eq : generator.target = target) :
    (TraceCorQHomFormalSum.singleton
      source
      target
      coefficient
      generator
      source_eq
      target_eq).importedRectangleCount =
      generator.importedRectangleCount +
        ResidueChannelCertificateLedger.empty.importedRectangleCount :=
  TraceCorQHomFormalSum.singleton_importedRectangleCount
    source
    target
    coefficient
    generator
    source_eq
    target_eq

/-- The top root exposes singleton typed formal-sum imported rectangles. -/
theorem AnalyticMotivesRoot.traceCorQHomFormalSum_singleton_importedRectangles
    (source target : TraceCorQObject)
    (coefficient : Rat)
    (generator : TraceCorQGenerator)
    (source_eq : generator.source = source)
    (target_eq : generator.target = target) :
    (TraceCorQHomFormalSum.singleton
      source
      target
      coefficient
      generator
      source_eq
      target_eq).importedRectangles =
      generator.importedRectangles ++
        ResidueChannelCertificateLedger.empty.importedRectangles :=
  TraceCorQHomFormalSum.singleton_importedRectangles
    source
    target
    coefficient
    generator
    source_eq
    target_eq

/-- The top root exposes singleton typed formal-sum bookkeeping counts. -/
theorem AnalyticMotivesRoot.traceCorQHomFormalSum_singleton_traceBookkeepingCount
    (source target : TraceCorQObject)
    (coefficient : Rat)
    (generator : TraceCorQGenerator)
    (source_eq : generator.source = source)
    (target_eq : generator.target = target) :
    (TraceCorQHomFormalSum.singleton
      source
      target
      coefficient
      generator
      source_eq
      target_eq).traceBookkeepingCount =
      generator.traceBookkeepingCount +
        ResidueChannelCertificateLedger.empty.traceBookkeepingCount :=
  TraceCorQHomFormalSum.singleton_traceBookkeepingCount
    source
    target
    coefficient
    generator
    source_eq
    target_eq

/-- The top root exposes singleton typed formal-sum rewrite-step counts. -/
theorem AnalyticMotivesRoot.traceCorQHomFormalSum_singleton_rewriteStepCount
    (source target : TraceCorQObject)
    (coefficient : Rat)
    (generator : TraceCorQGenerator)
    (source_eq : generator.source = source)
    (target_eq : generator.target = target) :
    (TraceCorQHomFormalSum.singleton
      source
      target
      coefficient
      generator
      source_eq
      target_eq).rewriteStepCount =
      generator.rewriteStepCount +
        ResidueChannelCertificateLedger.empty.rewriteStepCount :=
  TraceCorQHomFormalSum.singleton_rewriteStepCount
    source
    target
    coefficient
    generator
    source_eq
    target_eq

/-- The top root exposes raw addition for typed formal sums. -/
theorem AnalyticMotivesRoot.traceCorQHomFormalSum_add_raw
    {source target : TraceCorQObject}
    (left right : TraceCorQHomFormalSum source target) :
    (TraceCorQHomFormalSum.add left right).raw =
      TraceCorQFormalSum.add left.raw right.raw :=
  TraceCorQHomFormalSum.add_raw
    left
    right

/-- The top root exposes certificate-ledger addition for typed formal sums. -/
theorem AnalyticMotivesRoot.traceCorQHomFormalSum_add_certificateLedger
    {source target : TraceCorQObject}
    (left right : TraceCorQHomFormalSum source target) :
    (TraceCorQHomFormalSum.add left right).certificateLedger =
      ResidueChannelCertificateLedger.append
        left.certificateLedger
        right.certificateLedger :=
  TraceCorQHomFormalSum.add_certificateLedger
    left
    right

/-- The top root exposes imported-count addition for typed formal sums. -/
theorem AnalyticMotivesRoot.traceCorQHomFormalSum_add_importedRectangleCount
    {source target : TraceCorQObject}
    (left right : TraceCorQHomFormalSum source target) :
    (TraceCorQHomFormalSum.add left right).importedRectangleCount =
      left.importedRectangleCount +
        right.importedRectangleCount :=
  TraceCorQHomFormalSum.add_importedRectangleCount
    left
    right

/-- The top root exposes imported-rectangle concatenation for typed formal sums. -/
theorem AnalyticMotivesRoot.traceCorQHomFormalSum_add_importedRectangles
    {source target : TraceCorQObject}
    (left right : TraceCorQHomFormalSum source target) :
    (TraceCorQHomFormalSum.add left right).importedRectangles =
      left.importedRectangles ++
        right.importedRectangles :=
  TraceCorQHomFormalSum.add_importedRectangles
    left
    right

/-- The top root exposes typed formal-sum imported counts as list lengths. -/
theorem AnalyticMotivesRoot.traceCorQHomFormalSum_importedRectangleCount_eq_length_importedRectangles
    {source target : TraceCorQObject}
    (formalSum : TraceCorQHomFormalSum source target) :
    formalSum.importedRectangleCount =
      formalSum.importedRectangles.length :=
  TraceCorQHomFormalSum.importedRectangleCount_eq_length_importedRectangles
    formalSum

/-- The top root exposes bookkeeping-count addition for typed formal sums. -/
theorem AnalyticMotivesRoot.traceCorQHomFormalSum_add_traceBookkeepingCount
    {source target : TraceCorQObject}
    (left right : TraceCorQHomFormalSum source target) :
    (TraceCorQHomFormalSum.add left right).traceBookkeepingCount =
      left.traceBookkeepingCount +
        right.traceBookkeepingCount :=
  TraceCorQHomFormalSum.add_traceBookkeepingCount
    left
    right

/-- The top root exposes rewrite-step count addition for typed formal sums. -/
theorem AnalyticMotivesRoot.traceCorQHomFormalSum_add_rewriteStepCount
    {source target : TraceCorQObject}
    (left right : TraceCorQHomFormalSum source target) :
    (TraceCorQHomFormalSum.add left right).rewriteStepCount =
      left.rewriteStepCount +
        right.rewriteStepCount :=
  TraceCorQHomFormalSum.add_rewriteStepCount
    left
    right

end AnalyticMotives
end LFunctions
end Boundary
