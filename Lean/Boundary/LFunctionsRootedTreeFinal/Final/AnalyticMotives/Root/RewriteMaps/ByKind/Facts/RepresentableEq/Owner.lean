import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.RewriteMaps.ByKind.Facts.TraceHom.Owner

/-!
# Top-root by-kind representable-map equality facts
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top-root Stokes map is the generic map of the Stokes generator. -/
theorem AnalyticMotivesRoot.stokesRepresentableMap_eq
    (source target : QTraceExpression) :
    AnalyticMotivesRoot.stokesRepresentableMap source target =
      (TraceRewriteGenerator.stokes source target).representableMap :=
  TraceAnalyticMotive.stokesRepresentableMap_eq
    source
    target

/-- The top-root residue map is the generic map of the residue generator. -/
theorem AnalyticMotivesRoot.residueRepresentableMap_eq
    (source target : QTraceExpression) :
    AnalyticMotivesRoot.residueRepresentableMap source target =
      (TraceRewriteGenerator.residue source target).representableMap :=
  TraceAnalyticMotive.residueRepresentableMap_eq
    source
    target

/-- The top-root channel map is the generic map of the channel generator. -/
theorem AnalyticMotivesRoot.channelRepresentableMap_eq
    (source target : QTraceExpression) :
    AnalyticMotivesRoot.channelRepresentableMap source target =
      (TraceRewriteGenerator.channel source target).representableMap :=
  TraceAnalyticMotive.channelRepresentableMap_eq
    source
    target

/-- The top-root refinement map is the generic map of the refinement generator. -/
theorem AnalyticMotivesRoot.refinementRepresentableMap_eq
    (source target : QTraceExpression) :
    AnalyticMotivesRoot.refinementRepresentableMap source target =
      (TraceRewriteGenerator.refinement source target).representableMap :=
  TraceAnalyticMotive.refinementRepresentableMap_eq
    source
    target

/-- The top-root schedule map is the generic map of the schedule generator. -/
theorem AnalyticMotivesRoot.scheduleRepresentableMap_eq
    (source target : QTraceExpression) :
    AnalyticMotivesRoot.scheduleRepresentableMap source target =
      (TraceRewriteGenerator.schedule source target).representableMap :=
  TraceAnalyticMotive.scheduleRepresentableMap_eq
    source
    target

/-- The top-root weight-drop map is the generic map of the weight-drop generator. -/
theorem AnalyticMotivesRoot.weightDropRepresentableMap_eq
    (source target : QTraceExpression) :
    AnalyticMotivesRoot.weightDropRepresentableMap source target =
      (TraceRewriteGenerator.weightDrop source target).representableMap :=
  TraceAnalyticMotive.weightDropRepresentableMap_eq
    source
    target

/-- The top-root Fubini map is the generic map of the Fubini generator. -/
theorem AnalyticMotivesRoot.fubiniRepresentableMap_eq
    (source target : QTraceExpression) :
    AnalyticMotivesRoot.fubiniRepresentableMap source target =
      (TraceRewriteGenerator.fubini source target).representableMap :=
  TraceAnalyticMotive.fubiniRepresentableMap_eq
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
