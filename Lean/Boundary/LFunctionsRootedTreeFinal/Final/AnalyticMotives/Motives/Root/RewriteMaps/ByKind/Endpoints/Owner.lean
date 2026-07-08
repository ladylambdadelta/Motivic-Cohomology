import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Presheaves.RewriteMaps.ByKind.Endpoints.Owner

/-!
# Motive-root by-kind rewrite endpoints

This file exposes the certified endpoint presentations and trace morphisms of
the primitive analytic rewrite kinds at the motive root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The motive root exposes the Stokes source presentation. -/
def TraceAnalyticMotive.stokesSourcePresentation
    (source target : QTraceExpression) :
    CertifiedResidueChannelPresentation :=
  TraceRewriteGenerator.stokesSourcePresentation source target

/-- The motive root exposes the Stokes target presentation. -/
def TraceAnalyticMotive.stokesTargetPresentation
    (source target : QTraceExpression) :
    CertifiedResidueChannelPresentation :=
  TraceRewriteGenerator.stokesTargetPresentation source target

/-- The motive root exposes the residue source presentation. -/
def TraceAnalyticMotive.residueSourcePresentation
    (source target : QTraceExpression) :
    CertifiedResidueChannelPresentation :=
  TraceRewriteGenerator.residueSourcePresentation source target

/-- The motive root exposes the residue target presentation. -/
def TraceAnalyticMotive.residueTargetPresentation
    (source target : QTraceExpression) :
    CertifiedResidueChannelPresentation :=
  TraceRewriteGenerator.residueTargetPresentation source target

/-- The motive root exposes the channel source presentation. -/
def TraceAnalyticMotive.channelSourcePresentation
    (source target : QTraceExpression) :
    CertifiedResidueChannelPresentation :=
  TraceRewriteGenerator.channelSourcePresentation source target

/-- The motive root exposes the channel target presentation. -/
def TraceAnalyticMotive.channelTargetPresentation
    (source target : QTraceExpression) :
    CertifiedResidueChannelPresentation :=
  TraceRewriteGenerator.channelTargetPresentation source target

/-- The motive root exposes the refinement source presentation. -/
def TraceAnalyticMotive.refinementSourcePresentation
    (source target : QTraceExpression) :
    CertifiedResidueChannelPresentation :=
  TraceRewriteGenerator.refinementSourcePresentation source target

/-- The motive root exposes the refinement target presentation. -/
def TraceAnalyticMotive.refinementTargetPresentation
    (source target : QTraceExpression) :
    CertifiedResidueChannelPresentation :=
  TraceRewriteGenerator.refinementTargetPresentation source target

/-- The motive root exposes the schedule source presentation. -/
def TraceAnalyticMotive.scheduleSourcePresentation
    (source target : QTraceExpression) :
    CertifiedResidueChannelPresentation :=
  TraceRewriteGenerator.scheduleSourcePresentation source target

/-- The motive root exposes the schedule target presentation. -/
def TraceAnalyticMotive.scheduleTargetPresentation
    (source target : QTraceExpression) :
    CertifiedResidueChannelPresentation :=
  TraceRewriteGenerator.scheduleTargetPresentation source target

/-- The motive root exposes the weight-drop source presentation. -/
def TraceAnalyticMotive.weightDropSourcePresentation
    (source target : QTraceExpression) :
    CertifiedResidueChannelPresentation :=
  TraceRewriteGenerator.weightDropSourcePresentation source target

/-- The motive root exposes the weight-drop target presentation. -/
def TraceAnalyticMotive.weightDropTargetPresentation
    (source target : QTraceExpression) :
    CertifiedResidueChannelPresentation :=
  TraceRewriteGenerator.weightDropTargetPresentation source target

/-- The motive root exposes the Fubini source presentation. -/
def TraceAnalyticMotive.fubiniSourcePresentation
    (source target : QTraceExpression) :
    CertifiedResidueChannelPresentation :=
  TraceRewriteGenerator.fubiniSourcePresentation source target

/-- The motive root exposes the Fubini target presentation. -/
def TraceAnalyticMotive.fubiniTargetPresentation
    (source target : QTraceExpression) :
    CertifiedResidueChannelPresentation :=
  TraceRewriteGenerator.fubiniTargetPresentation source target

/-- The motive root exposes the Stokes trace morphism. -/
def TraceAnalyticMotive.stokesTraceHom
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.stokes source target).sourceObject ⟶
      (TraceRewriteGenerator.stokes source target).targetObject :=
  TraceRewriteGenerator.stokesTraceHom source target

/-- The motive root exposes the residue trace morphism. -/
def TraceAnalyticMotive.residueTraceHom
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.residue source target).sourceObject ⟶
      (TraceRewriteGenerator.residue source target).targetObject :=
  TraceRewriteGenerator.residueTraceHom source target

/-- The motive root exposes the channel trace morphism. -/
def TraceAnalyticMotive.channelTraceHom
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.channel source target).sourceObject ⟶
      (TraceRewriteGenerator.channel source target).targetObject :=
  TraceRewriteGenerator.channelTraceHom source target

/-- The motive root exposes the refinement trace morphism. -/
def TraceAnalyticMotive.refinementTraceHom
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.refinement source target).sourceObject ⟶
      (TraceRewriteGenerator.refinement source target).targetObject :=
  TraceRewriteGenerator.refinementTraceHom source target

/-- The motive root exposes the schedule trace morphism. -/
def TraceAnalyticMotive.scheduleTraceHom
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.schedule source target).sourceObject ⟶
      (TraceRewriteGenerator.schedule source target).targetObject :=
  TraceRewriteGenerator.scheduleTraceHom source target

/-- The motive root exposes the weight-drop trace morphism. -/
def TraceAnalyticMotive.weightDropTraceHom
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.weightDrop source target).sourceObject ⟶
      (TraceRewriteGenerator.weightDrop source target).targetObject :=
  TraceRewriteGenerator.weightDropTraceHom source target

/-- The motive root exposes the Fubini trace morphism. -/
def TraceAnalyticMotive.fubiniTraceHom
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.fubini source target).sourceObject ⟶
      (TraceRewriteGenerator.fubini source target).targetObject :=
  TraceRewriteGenerator.fubiniTraceHom source target

end AnalyticMotives
end LFunctions
end Boundary
