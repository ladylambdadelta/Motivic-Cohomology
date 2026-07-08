import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.RewriteMaps.ByKind.Facts.Inclusion.Owner

/-!
# Top-root by-kind lifted-Yoneda preimage facts
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top-root lifted Stokes map has Stokes trace morphism as Yoneda preimage. -/
theorem AnalyticMotivesRoot.stokesRepresentableSubcategoryMap_preimage
    (source target : QTraceExpression) :
    TraceCorQRepresentablePresheaf.yonedaPreimage
        (AnalyticMotivesRoot.stokesRepresentableSubcategoryMap source target) =
      AnalyticMotivesRoot.stokesTraceHom source target :=
  TraceAnalyticMotive.stokesRepresentableSubcategoryMap_preimage
    source
    target

/-- The top-root lifted residue map has residue trace morphism as Yoneda preimage. -/
theorem AnalyticMotivesRoot.residueRepresentableSubcategoryMap_preimage
    (source target : QTraceExpression) :
    TraceCorQRepresentablePresheaf.yonedaPreimage
        (AnalyticMotivesRoot.residueRepresentableSubcategoryMap source target) =
      AnalyticMotivesRoot.residueTraceHom source target :=
  TraceAnalyticMotive.residueRepresentableSubcategoryMap_preimage
    source
    target

/-- The top-root lifted channel map has channel trace morphism as Yoneda preimage. -/
theorem AnalyticMotivesRoot.channelRepresentableSubcategoryMap_preimage
    (source target : QTraceExpression) :
    TraceCorQRepresentablePresheaf.yonedaPreimage
        (AnalyticMotivesRoot.channelRepresentableSubcategoryMap source target) =
      AnalyticMotivesRoot.channelTraceHom source target :=
  TraceAnalyticMotive.channelRepresentableSubcategoryMap_preimage
    source
    target

/-- The top-root lifted refinement map has refinement trace morphism as Yoneda preimage. -/
theorem AnalyticMotivesRoot.refinementRepresentableSubcategoryMap_preimage
    (source target : QTraceExpression) :
    TraceCorQRepresentablePresheaf.yonedaPreimage
        (AnalyticMotivesRoot.refinementRepresentableSubcategoryMap source target) =
      AnalyticMotivesRoot.refinementTraceHom source target :=
  TraceAnalyticMotive.refinementRepresentableSubcategoryMap_preimage
    source
    target

/-- The top-root lifted schedule map has schedule trace morphism as Yoneda preimage. -/
theorem AnalyticMotivesRoot.scheduleRepresentableSubcategoryMap_preimage
    (source target : QTraceExpression) :
    TraceCorQRepresentablePresheaf.yonedaPreimage
        (AnalyticMotivesRoot.scheduleRepresentableSubcategoryMap source target) =
      AnalyticMotivesRoot.scheduleTraceHom source target :=
  TraceAnalyticMotive.scheduleRepresentableSubcategoryMap_preimage
    source
    target

/-- The top-root lifted weight-drop map has weight-drop trace morphism as Yoneda preimage. -/
theorem AnalyticMotivesRoot.weightDropRepresentableSubcategoryMap_preimage
    (source target : QTraceExpression) :
    TraceCorQRepresentablePresheaf.yonedaPreimage
        (AnalyticMotivesRoot.weightDropRepresentableSubcategoryMap source target) =
      AnalyticMotivesRoot.weightDropTraceHom source target :=
  TraceAnalyticMotive.weightDropRepresentableSubcategoryMap_preimage
    source
    target

/-- The top-root lifted Fubini map has Fubini trace morphism as Yoneda preimage. -/
theorem AnalyticMotivesRoot.fubiniRepresentableSubcategoryMap_preimage
    (source target : QTraceExpression) :
    TraceCorQRepresentablePresheaf.yonedaPreimage
        (AnalyticMotivesRoot.fubiniRepresentableSubcategoryMap source target) =
      AnalyticMotivesRoot.fubiniTraceHom source target :=
  TraceAnalyticMotive.fubiniRepresentableSubcategoryMap_preimage
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
