import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.Stage.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.Kernels.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.SingularSupport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.ResidueLedger.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.Channels.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.Schedules.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.Certificates.Owner

/-!
# Residue-channel presentations

This directory owns the concrete analytic presentations whose traces generate
the analytic motive category.

A presentation is intended to package kernels, singular support, contour and
residue bookkeeping, channels, schedules, and analytic certificates.  It is the
main object-level input to the later trace-correspondence category.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
The raw finite spine of a residue-channel presentation.

The components are source expression, residue ledger, channel expressions, and
schedule.  Kernel data, singular support, and analytic certificates are owned
by their separate files and will interpret this finite spine.
-/
abbrev ResidueChannelPresentationSpine :=
  QTraceExpression × ResidueLedger × ResidueChannelExpressionList × TraceSchedule

/-- The source expression of a raw residue-channel presentation spine. -/
def ResidueChannelPresentationSpine.source
    (presentation : ResidueChannelPresentationSpine) : QTraceExpression :=
  presentation.1

/-- The residue ledger of a raw residue-channel presentation spine. -/
def ResidueChannelPresentationSpine.ledger
    (presentation : ResidueChannelPresentationSpine) : ResidueLedger :=
  presentation.2.1

/-- The channel expressions of a raw residue-channel presentation spine. -/
def ResidueChannelPresentationSpine.channels
    (presentation : ResidueChannelPresentationSpine) :
    ResidueChannelExpressionList :=
  presentation.2.2.1

/-- The schedule of a raw residue-channel presentation spine. -/
def ResidueChannelPresentationSpine.schedule
    (presentation : ResidueChannelPresentationSpine) : TraceSchedule :=
  presentation.2.2.2

end AnalyticMotives
end LFunctions
end Boundary
