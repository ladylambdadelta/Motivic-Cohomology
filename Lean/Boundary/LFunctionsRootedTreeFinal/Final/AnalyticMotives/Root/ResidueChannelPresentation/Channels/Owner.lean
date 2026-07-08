import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.Channels.Owner

/-!
# Top-root residue channels

This file exposes finite channel-expression lists for residue-channel
presentations.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes residue channels as trace-channel indices. -/
def AnalyticMotivesRoot.residueChannel
    (channel : ResidueChannel) :
    TraceChannelIndex :=
  channel

/-- The top root exposes the empty channel-expression list. -/
def AnalyticMotivesRoot.residueChannelExpressionList_empty :
    ResidueChannelExpressionList :=
  ResidueChannelExpressionList.empty

/-- The top root exposes channel-expression construction. -/
def AnalyticMotivesRoot.residueChannelExpression_mk
    (channel : ResidueChannel)
    (expression : QTraceExpression) :
    ResidueChannelExpression :=
  ResidueChannelExpression.mk channel expression

/-- The top root exposes channel-expression list cons. -/
def AnalyticMotivesRoot.residueChannelExpressionList_cons
    (entry : ResidueChannelExpression)
    (channels : ResidueChannelExpressionList) :
    ResidueChannelExpressionList :=
  ResidueChannelExpressionList.cons entry channels

/-- The top root exposes channel-expression construction as pair construction. -/
theorem AnalyticMotivesRoot.residueChannelExpression_mk_eq_pair
    (channel : ResidueChannel)
    (expression : QTraceExpression) :
    ResidueChannelExpression.mk channel expression =
      (channel, expression) :=
  ResidueChannelExpression.mk_eq_pair channel expression

/-- The top root exposes the empty channel-expression list as the empty list. -/
theorem AnalyticMotivesRoot.residueChannelExpressionList_empty_eq_nil :
    ResidueChannelExpressionList.empty = [] :=
  ResidueChannelExpressionList.empty_eq_nil

/-- The top root exposes channel-expression list cons as list cons. -/
theorem AnalyticMotivesRoot.residueChannelExpressionList_cons_eq_cons
    (entry : ResidueChannelExpression)
    (channels : ResidueChannelExpressionList) :
    ResidueChannelExpressionList.cons entry channels =
      entry :: channels :=
  ResidueChannelExpressionList.cons_eq_cons entry channels

end AnalyticMotives
end LFunctions
end Boundary
