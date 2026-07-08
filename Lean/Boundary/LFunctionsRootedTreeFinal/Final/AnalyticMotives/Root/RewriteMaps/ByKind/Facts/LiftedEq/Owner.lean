import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.RewriteMaps.ByKind.Facts.RepresentableEq.Owner

/-!
# Top-root by-kind lifted-map equality facts
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top-root lifted Stokes map is the generic lifted map of the Stokes generator. -/
theorem AnalyticMotivesRoot.stokesRepresentableSubcategoryMap_eq
    (source target : QTraceExpression) :
    AnalyticMotivesRoot.stokesRepresentableSubcategoryMap source target =
      (TraceRewriteGenerator.stokes source target).representableSubcategoryMap :=
  TraceAnalyticMotive.stokesRepresentableSubcategoryMap_eq
    source
    target

/-- The top-root lifted residue map is the generic lifted map of the residue generator. -/
theorem AnalyticMotivesRoot.residueRepresentableSubcategoryMap_eq
    (source target : QTraceExpression) :
    AnalyticMotivesRoot.residueRepresentableSubcategoryMap source target =
      (TraceRewriteGenerator.residue source target).representableSubcategoryMap :=
  TraceAnalyticMotive.residueRepresentableSubcategoryMap_eq
    source
    target

/-- The top-root lifted channel map is the generic lifted map of the channel generator. -/
theorem AnalyticMotivesRoot.channelRepresentableSubcategoryMap_eq
    (source target : QTraceExpression) :
    AnalyticMotivesRoot.channelRepresentableSubcategoryMap source target =
      (TraceRewriteGenerator.channel source target).representableSubcategoryMap :=
  TraceAnalyticMotive.channelRepresentableSubcategoryMap_eq
    source
    target

/-- The top-root lifted refinement map is the generic lifted map of the refinement generator. -/
theorem AnalyticMotivesRoot.refinementRepresentableSubcategoryMap_eq
    (source target : QTraceExpression) :
    AnalyticMotivesRoot.refinementRepresentableSubcategoryMap source target =
      (TraceRewriteGenerator.refinement source target).representableSubcategoryMap :=
  TraceAnalyticMotive.refinementRepresentableSubcategoryMap_eq
    source
    target

/-- The top-root lifted schedule map is the generic lifted map of the schedule generator. -/
theorem AnalyticMotivesRoot.scheduleRepresentableSubcategoryMap_eq
    (source target : QTraceExpression) :
    AnalyticMotivesRoot.scheduleRepresentableSubcategoryMap source target =
      (TraceRewriteGenerator.schedule source target).representableSubcategoryMap :=
  TraceAnalyticMotive.scheduleRepresentableSubcategoryMap_eq
    source
    target

/-- The top-root lifted weight-drop map is the generic lifted map of the weight-drop generator. -/
theorem AnalyticMotivesRoot.weightDropRepresentableSubcategoryMap_eq
    (source target : QTraceExpression) :
    AnalyticMotivesRoot.weightDropRepresentableSubcategoryMap source target =
      (TraceRewriteGenerator.weightDrop source target).representableSubcategoryMap :=
  TraceAnalyticMotive.weightDropRepresentableSubcategoryMap_eq
    source
    target

/-- The top-root lifted Fubini map is the generic lifted map of the Fubini generator. -/
theorem AnalyticMotivesRoot.fubiniRepresentableSubcategoryMap_eq
    (source target : QTraceExpression) :
    AnalyticMotivesRoot.fubiniRepresentableSubcategoryMap source target =
      (TraceRewriteGenerator.fubini source target).representableSubcategoryMap :=
  TraceAnalyticMotive.fubiniRepresentableSubcategoryMap_eq
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
