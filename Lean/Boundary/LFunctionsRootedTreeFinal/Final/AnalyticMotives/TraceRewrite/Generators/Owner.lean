import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Generators.Core.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Generators.Stokes.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Generators.Residue.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Generators.Channel.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Generators.Refinement.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Generators.Schedule.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Generators.WeightDrop.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Generators.Fubini.Owner

/-!
# Analytic rewrite generators

This owner collects the named analytic rewrite generators that present the
higher computadic trace calculus.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The generator root exposes Stokes generator kind. -/
theorem TraceRewriteGenerators.stokes_kind
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.stokes source target).kind =
      TraceRewriteKind.stokes :=
  TraceRewriteGenerator.stokes_kind
    source
    target

/-- The generator root exposes residue generator kind. -/
theorem TraceRewriteGenerators.residue_kind
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.residue source target).kind =
      TraceRewriteKind.residue :=
  TraceRewriteGenerator.residue_kind
    source
    target

/-- The generator root exposes channel generator kind. -/
theorem TraceRewriteGenerators.channel_kind
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.channel source target).kind =
      TraceRewriteKind.channel :=
  TraceRewriteGenerator.channel_kind
    source
    target

/-- The generator root exposes refinement generator kind. -/
theorem TraceRewriteGenerators.refinement_kind
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.refinement source target).kind =
      TraceRewriteKind.refinement :=
  TraceRewriteGenerator.refinement_kind
    source
    target

/-- The generator root exposes schedule generator kind. -/
theorem TraceRewriteGenerators.schedule_kind
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.schedule source target).kind =
      TraceRewriteKind.schedule :=
  TraceRewriteGenerator.schedule_kind
    source
    target

/-- The generator root exposes weight-drop generator kind. -/
theorem TraceRewriteGenerators.weightDrop_kind
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.weightDrop source target).kind =
      TraceRewriteKind.weightDrop :=
  TraceRewriteGenerator.weightDrop_kind
    source
    target

/-- The generator root exposes Fubini generator kind. -/
theorem TraceRewriteGenerators.fubini_kind
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.fubini source target).kind =
      TraceRewriteKind.fubini :=
  TraceRewriteGenerator.fubini_kind
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
