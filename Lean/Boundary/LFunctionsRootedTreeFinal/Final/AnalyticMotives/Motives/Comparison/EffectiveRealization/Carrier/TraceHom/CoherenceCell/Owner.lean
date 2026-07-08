import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Coherence.Owner

/-!
# Coherence-cell carriers for analytic effective realization

This file exposes the concrete higher rewrite coherence cell that supports a
trace-correspondence relation generator.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The comparison boundary keeps the actual trace coherence cell. -/
def TraceAnalyticEffectiveRealization.traceHomCoherenceCellCarrier
    (cell : TraceCoherenceCell) :
    TraceCoherenceCell :=
  cell

/-- The coherence kind carried by a trace coherence cell. -/
def TraceAnalyticEffectiveRealization.traceHomCoherenceCellKind
    (cell : TraceCoherenceCell) :
    TraceCoherenceKind :=
  cell.kind

/-- The source rewrite path carried by a trace coherence cell. -/
def TraceAnalyticEffectiveRealization.traceHomCoherenceCellSource
    (cell : TraceCoherenceCell) :
    TraceRewritePath :=
  cell.source

/-- The target rewrite path carried by a trace coherence cell. -/
def TraceAnalyticEffectiveRealization.traceHomCoherenceCellTarget
    (cell : TraceCoherenceCell) :
    TraceRewritePath :=
  cell.target

/-- The coherence-cell carrier is definitionally the supplied cell. -/
theorem TraceAnalyticEffectiveRealization.traceHomCoherenceCellCarrier_eq
    (cell : TraceCoherenceCell) :
    TraceAnalyticEffectiveRealization.traceHomCoherenceCellCarrier cell =
      cell :=
  rfl

/-- The coherence-cell kind carrier is definitionally the cell kind. -/
theorem TraceAnalyticEffectiveRealization.traceHomCoherenceCellKind_eq
    (cell : TraceCoherenceCell) :
    TraceAnalyticEffectiveRealization.traceHomCoherenceCellKind cell =
      cell.kind :=
  rfl

/-- The coherence-cell source carrier is definitionally the cell source. -/
theorem TraceAnalyticEffectiveRealization.traceHomCoherenceCellSource_eq
    (cell : TraceCoherenceCell) :
    TraceAnalyticEffectiveRealization.traceHomCoherenceCellSource cell =
      cell.source :=
  rfl

/-- The coherence-cell target carrier is definitionally the cell target. -/
theorem TraceAnalyticEffectiveRealization.traceHomCoherenceCellTarget_eq
    (cell : TraceCoherenceCell) :
    TraceAnalyticEffectiveRealization.traceHomCoherenceCellTarget cell =
      cell.target :=
  rfl

/-- A Fubini coherence cell has Fubini kind at the comparison boundary. -/
theorem TraceAnalyticEffectiveRealization.traceHomCoherenceCellFubini_kind
    (source target : TraceRewritePath) :
    TraceAnalyticEffectiveRealization.traceHomCoherenceCellKind
      (TraceCoherenceCell.fubini source target) =
      TraceCoherenceKind.fubini :=
  TraceCoherenceCell.fubini_kind
    source
    target

/-- A residue-channel coherence cell has residue-channel kind at the comparison boundary. -/
theorem TraceAnalyticEffectiveRealization.traceHomCoherenceCellResidueChannel_kind
    (source target : TraceRewritePath) :
    TraceAnalyticEffectiveRealization.traceHomCoherenceCellKind
      (TraceCoherenceCell.residueChannel source target) =
      TraceCoherenceKind.residueChannel :=
  TraceCoherenceCell.residueChannel_kind
    source
    target

/-- An associativity coherence cell has associativity kind at the comparison boundary. -/
theorem TraceAnalyticEffectiveRealization.traceHomCoherenceCellAssociativity_kind
    (source target : TraceRewritePath) :
    TraceAnalyticEffectiveRealization.traceHomCoherenceCellKind
      (TraceCoherenceCell.associativity source target) =
      TraceCoherenceKind.associativity :=
  TraceCoherenceCell.associativity_kind
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
