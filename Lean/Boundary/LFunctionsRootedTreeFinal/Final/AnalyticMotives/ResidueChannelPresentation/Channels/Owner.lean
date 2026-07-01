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

/-- The empty channel-expression list. -/
def ResidueChannelExpressionList.empty : ResidueChannelExpressionList :=
  []

end AnalyticMotives
end LFunctions
end Boundary
