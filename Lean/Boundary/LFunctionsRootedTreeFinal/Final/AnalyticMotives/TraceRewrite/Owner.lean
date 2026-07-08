import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Generators.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Paths.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Paths.Certificates.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Paths.Certificates.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Paths.Certificates.Shape.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Relations.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Coherence.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Coherence.Certificates.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Coherence.Certificates.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Coherence.Certificates.Shape.Owner

/-!
# Trace rewriting

This directory is the higher-computad layer of analytic motives.  It presents
analytic trace identities as directed rewrites between Q-linear trace
expressions, together with relations and higher coherences.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace-rewrite root exposes Stokes generator kind. -/
theorem TraceRewrite.stokesGenerator_kind
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.stokes source target).kind =
      TraceRewriteKind.stokes :=
  TraceRewriteGenerator.stokes_kind
    source
    target

/-- The trace-rewrite root exposes residue generator kind. -/
theorem TraceRewrite.residueGenerator_kind
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.residue source target).kind =
      TraceRewriteKind.residue :=
  TraceRewriteGenerator.residue_kind
    source
    target

/-- The trace-rewrite root exposes channel generator kind. -/
theorem TraceRewrite.channelGenerator_kind
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.channel source target).kind =
      TraceRewriteKind.channel :=
  TraceRewriteGenerator.channel_kind
    source
    target

/-- The trace-rewrite root exposes residue one-step paths. -/
theorem TraceRewrite.residuePath_stepCount
    (source target : QTraceExpression) :
    (TraceRewritePath.residue source target).stepCount =
      1 :=
  TraceRewritePath.residue_stepCount
    source
    target

/-- The trace-rewrite root exposes channel one-step paths. -/
theorem TraceRewrite.channelPath_stepCount
    (source target : QTraceExpression) :
    (TraceRewritePath.channel source target).stepCount =
      1 :=
  TraceRewritePath.channel_stepCount
    source
    target

/-- The trace-rewrite root exposes path concatenation step counts. -/
theorem TraceRewrite.pathComp_stepCount
    (first second : TraceRewritePath) :
    (TraceRewritePath.comp first second).stepCount =
      first.stepCount + second.stepCount :=
  TraceRewritePath.comp_stepCount
    first
    second

/-- The trace-rewrite root exposes residue-channel coherence cells. -/
theorem TraceRewrite.residueChannelCoherence_kind
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.residueChannel source target).kind =
      TraceCoherenceKind.residueChannel :=
  TraceCoherenceCell.residueChannel_kind
    source
    target

/-- The trace-rewrite root exposes Fubini coherence cells. -/
theorem TraceRewrite.fubiniCoherence_kind
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.fubini source target).kind =
      TraceCoherenceKind.fubini :=
  TraceCoherenceCell.fubini_kind
    source
    target

/-- The trace-rewrite root exposes associativity coherence cells. -/
theorem TraceRewrite.associativityCoherence_kind
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.associativity source target).kind =
      TraceCoherenceKind.associativity :=
  TraceCoherenceCell.associativity_kind
    source
    target

/-- The trace-rewrite root exposes Fubini rewrite relations. -/
theorem TraceRewrite.fubiniRelation_kind
    (source target : TraceRewritePath) :
    (TraceRewriteRelation.fubini source target).kind =
      TraceCoherenceKind.fubini :=
  TraceRewriteRelation.fubini_kind
    source
    target

/-- The trace-rewrite root exposes residue-channel rewrite relations. -/
theorem TraceRewrite.residueChannelRelation_kind
    (source target : TraceRewritePath) :
    (TraceRewriteRelation.residueChannel source target).kind =
      TraceCoherenceKind.residueChannel :=
  TraceRewriteRelation.residueChannel_kind
    source
    target

/-- The trace-rewrite root exposes associativity rewrite relations. -/
theorem TraceRewrite.associativityRelation_kind
    (source target : TraceRewritePath) :
    (TraceRewriteRelation.associativity source target).kind =
      TraceCoherenceKind.associativity :=
  TraceRewriteRelation.associativity_kind
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
