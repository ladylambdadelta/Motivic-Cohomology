import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.RewriteMaps.ByKind.Endpoints.Owner

/-!
# Top-root by-kind rewrite endpoints

This file exposes certified endpoint presentations and trace morphisms for the
seven one-step analytic trace rewrite kinds under `AnalyticMotivesRoot`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes the Stokes source presentation. -/
def AnalyticMotivesRoot.stokesSourcePresentation
    (source target : QTraceExpression) :
    CertifiedResidueChannelPresentation :=
  TraceAnalyticMotive.stokesSourcePresentation source target

/-- The top root exposes the Stokes target presentation. -/
def AnalyticMotivesRoot.stokesTargetPresentation
    (source target : QTraceExpression) :
    CertifiedResidueChannelPresentation :=
  TraceAnalyticMotive.stokesTargetPresentation source target

/-- The top root exposes the residue source presentation. -/
def AnalyticMotivesRoot.residueSourcePresentation
    (source target : QTraceExpression) :
    CertifiedResidueChannelPresentation :=
  TraceAnalyticMotive.residueSourcePresentation source target

/-- The top root exposes the residue target presentation. -/
def AnalyticMotivesRoot.residueTargetPresentation
    (source target : QTraceExpression) :
    CertifiedResidueChannelPresentation :=
  TraceAnalyticMotive.residueTargetPresentation source target

/-- The top root exposes the channel source presentation. -/
def AnalyticMotivesRoot.channelSourcePresentation
    (source target : QTraceExpression) :
    CertifiedResidueChannelPresentation :=
  TraceAnalyticMotive.channelSourcePresentation source target

/-- The top root exposes the channel target presentation. -/
def AnalyticMotivesRoot.channelTargetPresentation
    (source target : QTraceExpression) :
    CertifiedResidueChannelPresentation :=
  TraceAnalyticMotive.channelTargetPresentation source target

/-- The top root exposes the refinement source presentation. -/
def AnalyticMotivesRoot.refinementSourcePresentation
    (source target : QTraceExpression) :
    CertifiedResidueChannelPresentation :=
  TraceAnalyticMotive.refinementSourcePresentation source target

/-- The top root exposes the refinement target presentation. -/
def AnalyticMotivesRoot.refinementTargetPresentation
    (source target : QTraceExpression) :
    CertifiedResidueChannelPresentation :=
  TraceAnalyticMotive.refinementTargetPresentation source target

/-- The top root exposes the schedule source presentation. -/
def AnalyticMotivesRoot.scheduleSourcePresentation
    (source target : QTraceExpression) :
    CertifiedResidueChannelPresentation :=
  TraceAnalyticMotive.scheduleSourcePresentation source target

/-- The top root exposes the schedule target presentation. -/
def AnalyticMotivesRoot.scheduleTargetPresentation
    (source target : QTraceExpression) :
    CertifiedResidueChannelPresentation :=
  TraceAnalyticMotive.scheduleTargetPresentation source target

/-- The top root exposes the weight-drop source presentation. -/
def AnalyticMotivesRoot.weightDropSourcePresentation
    (source target : QTraceExpression) :
    CertifiedResidueChannelPresentation :=
  TraceAnalyticMotive.weightDropSourcePresentation source target

/-- The top root exposes the weight-drop target presentation. -/
def AnalyticMotivesRoot.weightDropTargetPresentation
    (source target : QTraceExpression) :
    CertifiedResidueChannelPresentation :=
  TraceAnalyticMotive.weightDropTargetPresentation source target

/-- The top root exposes the Fubini source presentation. -/
def AnalyticMotivesRoot.fubiniSourcePresentation
    (source target : QTraceExpression) :
    CertifiedResidueChannelPresentation :=
  TraceAnalyticMotive.fubiniSourcePresentation source target

/-- The top root exposes the Fubini target presentation. -/
def AnalyticMotivesRoot.fubiniTargetPresentation
    (source target : QTraceExpression) :
    CertifiedResidueChannelPresentation :=
  TraceAnalyticMotive.fubiniTargetPresentation source target

/-- The top root exposes the Stokes trace morphism. -/
def AnalyticMotivesRoot.stokesTraceHom
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.stokes source target).sourceObject ⟶
      (TraceRewriteGenerator.stokes source target).targetObject :=
  TraceAnalyticMotive.stokesTraceHom source target

/-- The top root exposes the residue trace morphism. -/
def AnalyticMotivesRoot.residueTraceHom
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.residue source target).sourceObject ⟶
      (TraceRewriteGenerator.residue source target).targetObject :=
  TraceAnalyticMotive.residueTraceHom source target

/-- The top root exposes the channel trace morphism. -/
def AnalyticMotivesRoot.channelTraceHom
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.channel source target).sourceObject ⟶
      (TraceRewriteGenerator.channel source target).targetObject :=
  TraceAnalyticMotive.channelTraceHom source target

/-- The top root exposes the refinement trace morphism. -/
def AnalyticMotivesRoot.refinementTraceHom
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.refinement source target).sourceObject ⟶
      (TraceRewriteGenerator.refinement source target).targetObject :=
  TraceAnalyticMotive.refinementTraceHom source target

/-- The top root exposes the schedule trace morphism. -/
def AnalyticMotivesRoot.scheduleTraceHom
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.schedule source target).sourceObject ⟶
      (TraceRewriteGenerator.schedule source target).targetObject :=
  TraceAnalyticMotive.scheduleTraceHom source target

/-- The top root exposes the weight-drop trace morphism. -/
def AnalyticMotivesRoot.weightDropTraceHom
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.weightDrop source target).sourceObject ⟶
      (TraceRewriteGenerator.weightDrop source target).targetObject :=
  TraceAnalyticMotive.weightDropTraceHom source target

/-- The top root exposes the Fubini trace morphism. -/
def AnalyticMotivesRoot.fubiniTraceHom
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.fubini source target).sourceObject ⟶
      (TraceRewriteGenerator.fubini source target).targetObject :=
  TraceAnalyticMotive.fubiniTraceHom source target

end AnalyticMotives
end LFunctions
end Boundary
