import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceExpression.QLinear.Owner

/-!
# Core analytic rewrite generators

This file owns the concrete syntax for one-step higher-computadic trace
rewrites.
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

/-- A Stokes rewrite generator has Stokes kind. -/
theorem TraceRewriteGenerator.stokes_kind
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.stokes source target).kind =
      TraceRewriteKind.stokes :=
  rfl

/-- A Stokes rewrite generator has the supplied source. -/
theorem TraceRewriteGenerator.stokes_source
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.stokes source target).source =
      source :=
  rfl

/-- A Stokes rewrite generator has the supplied target. -/
theorem TraceRewriteGenerator.stokes_target
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.stokes source target).target =
      target :=
  rfl

/-- A residue rewrite generator has residue kind. -/
theorem TraceRewriteGenerator.residue_kind
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.residue source target).kind =
      TraceRewriteKind.residue :=
  rfl

/-- A residue rewrite generator has the supplied source. -/
theorem TraceRewriteGenerator.residue_source
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.residue source target).source =
      source :=
  rfl

/-- A residue rewrite generator has the supplied target. -/
theorem TraceRewriteGenerator.residue_target
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.residue source target).target =
      target :=
  rfl

/-- A channel rewrite generator has channel kind. -/
theorem TraceRewriteGenerator.channel_kind
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.channel source target).kind =
      TraceRewriteKind.channel :=
  rfl

/-- A channel rewrite generator has the supplied source. -/
theorem TraceRewriteGenerator.channel_source
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.channel source target).source =
      source :=
  rfl

/-- A channel rewrite generator has the supplied target. -/
theorem TraceRewriteGenerator.channel_target
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.channel source target).target =
      target :=
  rfl

/-- A refinement rewrite generator has refinement kind. -/
theorem TraceRewriteGenerator.refinement_kind
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.refinement source target).kind =
      TraceRewriteKind.refinement :=
  rfl

/-- A refinement rewrite generator has the supplied source. -/
theorem TraceRewriteGenerator.refinement_source
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.refinement source target).source =
      source :=
  rfl

/-- A refinement rewrite generator has the supplied target. -/
theorem TraceRewriteGenerator.refinement_target
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.refinement source target).target =
      target :=
  rfl

/-- A schedule rewrite generator has schedule kind. -/
theorem TraceRewriteGenerator.schedule_kind
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.schedule source target).kind =
      TraceRewriteKind.schedule :=
  rfl

/-- A schedule rewrite generator has the supplied source. -/
theorem TraceRewriteGenerator.schedule_source
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.schedule source target).source =
      source :=
  rfl

/-- A schedule rewrite generator has the supplied target. -/
theorem TraceRewriteGenerator.schedule_target
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.schedule source target).target =
      target :=
  rfl

/-- A weight-drop rewrite generator has weight-drop kind. -/
theorem TraceRewriteGenerator.weightDrop_kind
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.weightDrop source target).kind =
      TraceRewriteKind.weightDrop :=
  rfl

/-- A weight-drop rewrite generator has the supplied source. -/
theorem TraceRewriteGenerator.weightDrop_source
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.weightDrop source target).source =
      source :=
  rfl

/-- A weight-drop rewrite generator has the supplied target. -/
theorem TraceRewriteGenerator.weightDrop_target
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.weightDrop source target).target =
      target :=
  rfl

/-- A Fubini rewrite generator has Fubini kind. -/
theorem TraceRewriteGenerator.fubini_kind
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.fubini source target).kind =
      TraceRewriteKind.fubini :=
  rfl

/-- A Fubini rewrite generator has the supplied source. -/
theorem TraceRewriteGenerator.fubini_source
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.fubini source target).source =
      source :=
  rfl

/-- A Fubini rewrite generator has the supplied target. -/
theorem TraceRewriteGenerator.fubini_target
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.fubini source target).target =
      target :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
