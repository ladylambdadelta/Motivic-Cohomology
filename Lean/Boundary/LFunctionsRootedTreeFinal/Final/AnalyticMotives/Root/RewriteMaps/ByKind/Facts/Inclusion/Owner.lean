import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.RewriteMaps.ByKind.Facts.RepresentablePreimage.Owner

/-!
# Top-root by-kind lifted-map inclusion facts
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Forgetting the top-root lifted Stokes map gives the Stokes representable map. -/
theorem AnalyticMotivesRoot.stokesRepresentableSubcategoryMap_inclusion
    (source target : QTraceExpression) :
    TraceCorQRepresentablePresheaf.inclusion.map
        (AnalyticMotivesRoot.stokesRepresentableSubcategoryMap source target) =
      AnalyticMotivesRoot.stokesRepresentableMap source target :=
  TraceAnalyticMotive.stokesRepresentableSubcategoryMap_inclusion
    source
    target

/-- Forgetting the top-root lifted residue map gives the residue representable map. -/
theorem AnalyticMotivesRoot.residueRepresentableSubcategoryMap_inclusion
    (source target : QTraceExpression) :
    TraceCorQRepresentablePresheaf.inclusion.map
        (AnalyticMotivesRoot.residueRepresentableSubcategoryMap source target) =
      AnalyticMotivesRoot.residueRepresentableMap source target :=
  TraceAnalyticMotive.residueRepresentableSubcategoryMap_inclusion
    source
    target

/-- Forgetting the top-root lifted channel map gives the channel representable map. -/
theorem AnalyticMotivesRoot.channelRepresentableSubcategoryMap_inclusion
    (source target : QTraceExpression) :
    TraceCorQRepresentablePresheaf.inclusion.map
        (AnalyticMotivesRoot.channelRepresentableSubcategoryMap source target) =
      AnalyticMotivesRoot.channelRepresentableMap source target :=
  TraceAnalyticMotive.channelRepresentableSubcategoryMap_inclusion
    source
    target

/-- Forgetting the top-root lifted refinement map gives the refinement representable map. -/
theorem AnalyticMotivesRoot.refinementRepresentableSubcategoryMap_inclusion
    (source target : QTraceExpression) :
    TraceCorQRepresentablePresheaf.inclusion.map
        (AnalyticMotivesRoot.refinementRepresentableSubcategoryMap source target) =
      AnalyticMotivesRoot.refinementRepresentableMap source target :=
  TraceAnalyticMotive.refinementRepresentableSubcategoryMap_inclusion
    source
    target

/-- Forgetting the top-root lifted schedule map gives the schedule representable map. -/
theorem AnalyticMotivesRoot.scheduleRepresentableSubcategoryMap_inclusion
    (source target : QTraceExpression) :
    TraceCorQRepresentablePresheaf.inclusion.map
        (AnalyticMotivesRoot.scheduleRepresentableSubcategoryMap source target) =
      AnalyticMotivesRoot.scheduleRepresentableMap source target :=
  TraceAnalyticMotive.scheduleRepresentableSubcategoryMap_inclusion
    source
    target

/-- Forgetting the top-root lifted weight-drop map gives the weight-drop representable map. -/
theorem AnalyticMotivesRoot.weightDropRepresentableSubcategoryMap_inclusion
    (source target : QTraceExpression) :
    TraceCorQRepresentablePresheaf.inclusion.map
        (AnalyticMotivesRoot.weightDropRepresentableSubcategoryMap source target) =
      AnalyticMotivesRoot.weightDropRepresentableMap source target :=
  TraceAnalyticMotive.weightDropRepresentableSubcategoryMap_inclusion
    source
    target

/-- Forgetting the top-root lifted Fubini map gives the Fubini representable map. -/
theorem AnalyticMotivesRoot.fubiniRepresentableSubcategoryMap_inclusion
    (source target : QTraceExpression) :
    TraceCorQRepresentablePresheaf.inclusion.map
        (AnalyticMotivesRoot.fubiniRepresentableSubcategoryMap source target) =
      AnalyticMotivesRoot.fubiniRepresentableMap source target :=
  TraceAnalyticMotive.fubiniRepresentableSubcategoryMap_inclusion
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
