import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceExpression.QLinear.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.Stage.Owner

/-!
# Channels

This file owns channels: the visible output components of a trace computation.

Channels are how a residue-channel presentation distinguishes boundary
contributions, spectral terms, geometric terms, tail terms, and defects without
overfitting the theory to zeta.  They are trace-expression structure, not
localized motive subcategories.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A named channel in a residue-channel presentation. -/
abbrev ResidueChannel :=
  TraceChannelIndex

/-- A channel expression assigns a Q-linear trace expression to one channel. -/
abbrev ResidueChannelExpression :=
  ResidueChannel × QTraceExpression

/-- A finite list of channel expressions. -/
abbrev ResidueChannelExpressionList :=
  List ResidueChannelExpression

/-- Build one channel expression from its channel and Q-linear trace expression. -/
def ResidueChannelExpression.mk
    (channel : ResidueChannel)
    (expression : QTraceExpression) :
    ResidueChannelExpression :=
  (channel, expression)

/-- The empty channel-expression list. -/
def ResidueChannelExpressionList.empty : ResidueChannelExpressionList :=
  []

/-- Add one channel expression at the front of a channel-expression list. -/
def ResidueChannelExpressionList.cons
    (entry : ResidueChannelExpression)
    (channels : ResidueChannelExpressionList) :
    ResidueChannelExpressionList :=
  entry :: channels

/-- A channel expression built from a channel and expression is their pair. -/
theorem ResidueChannelExpression.mk_eq_pair
    (channel : ResidueChannel)
    (expression : QTraceExpression) :
    ResidueChannelExpression.mk channel expression =
      (channel, expression) :=
  rfl

/-- The empty channel-expression list is the empty list. -/
theorem ResidueChannelExpressionList.empty_eq_nil :
    ResidueChannelExpressionList.empty = [] :=
  rfl

/-- Channel-expression list cons is list cons. -/
theorem ResidueChannelExpressionList.cons_eq_cons
    (entry : ResidueChannelExpression)
    (channels : ResidueChannelExpressionList) :
    ResidueChannelExpressionList.cons entry channels =
      entry :: channels :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
