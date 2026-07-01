import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Generators.Stokes.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Generators.Residue.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Generators.Channel.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Generators.Refinement.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Generators.Schedule.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Generators.WeightDrop.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Generators.Fubini.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceExpression.QLinear.Owner

/-!
# Analytic rewrite generators

This owner collects the named analytic rewrite generators that present the
higher computadic trace calculus.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The concrete kind of a one-step analytic trace rewrite. -/
inductive TraceRewriteKind where
  | stokes
  | residue
  | channel
  | refinement
  | schedule
  | weightDrop
  | fubini
  deriving DecidableEq, Repr

/--
A one-step generator in the higher-computadic trace calculus.

This is concrete syntax: a generator has a kind, a source Q-linear trace
expression, and a target Q-linear trace expression.  Analytic certificates that
justify such generators live in the residue-channel presentation layer.
-/
abbrev TraceRewriteGenerator :=
  TraceRewriteKind × QTraceExpression × QTraceExpression

/-- The kind of a rewrite generator. -/
def TraceRewriteGenerator.kind (generator : TraceRewriteGenerator) :
    TraceRewriteKind :=
  generator.1

/-- The source expression of a rewrite generator. -/
def TraceRewriteGenerator.source (generator : TraceRewriteGenerator) :
    QTraceExpression :=
  generator.2.1

/-- The target expression of a rewrite generator. -/
def TraceRewriteGenerator.target (generator : TraceRewriteGenerator) :
    QTraceExpression :=
  generator.2.2

/-- A Stokes cancellation rewrite generator. -/
def TraceRewriteGenerator.stokes
    (source target : QTraceExpression) : TraceRewriteGenerator :=
  (TraceRewriteKind.stokes, source, target)

/-- A residue-extraction rewrite generator. -/
def TraceRewriteGenerator.residue
    (source target : QTraceExpression) : TraceRewriteGenerator :=
  (TraceRewriteKind.residue, source, target)

/-- A channel-decomposition rewrite generator. -/
def TraceRewriteGenerator.channel
    (source target : QTraceExpression) : TraceRewriteGenerator :=
  (TraceRewriteKind.channel, source, target)

/-- A refinement-invariance rewrite generator. -/
def TraceRewriteGenerator.refinement
    (source target : QTraceExpression) : TraceRewriteGenerator :=
  (TraceRewriteKind.refinement, source, target)

/-- A schedule-exchange rewrite generator. -/
def TraceRewriteGenerator.schedule
    (source target : QTraceExpression) : TraceRewriteGenerator :=
  (TraceRewriteKind.schedule, source, target)

/-- A weight-drop rewrite generator. -/
def TraceRewriteGenerator.weightDrop
    (source target : QTraceExpression) : TraceRewriteGenerator :=
  (TraceRewriteKind.weightDrop, source, target)

/-- A Fubini coherence rewrite generator. -/
def TraceRewriteGenerator.fubini
    (source target : QTraceExpression) : TraceRewriteGenerator :=
  (TraceRewriteKind.fubini, source, target)

end AnalyticMotives
end LFunctions
end Boundary
