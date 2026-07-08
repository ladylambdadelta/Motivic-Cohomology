import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.RewriteMaps.ByKind.Facts.LiftedEq.Owner

/-!
# Top-root by-kind representable-map preimage facts
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The preimage of the top-root Stokes representable map is the Stokes trace morphism. -/
theorem AnalyticMotivesRoot.stokesRepresentableMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (AnalyticMotivesRoot.stokesRepresentableMap source target) =
      AnalyticMotivesRoot.stokesTraceHom source target :=
  TraceAnalyticMotive.stokesRepresentableMap_preimage
    source
    target

/-- The preimage of the top-root residue representable map is the residue trace morphism. -/
theorem AnalyticMotivesRoot.residueRepresentableMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (AnalyticMotivesRoot.residueRepresentableMap source target) =
      AnalyticMotivesRoot.residueTraceHom source target :=
  TraceAnalyticMotive.residueRepresentableMap_preimage
    source
    target

/-- The preimage of the top-root channel representable map is the channel trace morphism. -/
theorem AnalyticMotivesRoot.channelRepresentableMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (AnalyticMotivesRoot.channelRepresentableMap source target) =
      AnalyticMotivesRoot.channelTraceHom source target :=
  TraceAnalyticMotive.channelRepresentableMap_preimage
    source
    target

/-- The preimage of the top-root refinement representable map is the refinement trace morphism. -/
theorem AnalyticMotivesRoot.refinementRepresentableMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (AnalyticMotivesRoot.refinementRepresentableMap source target) =
      AnalyticMotivesRoot.refinementTraceHom source target :=
  TraceAnalyticMotive.refinementRepresentableMap_preimage
    source
    target

/-- The preimage of the top-root schedule representable map is the schedule trace morphism. -/
theorem AnalyticMotivesRoot.scheduleRepresentableMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (AnalyticMotivesRoot.scheduleRepresentableMap source target) =
      AnalyticMotivesRoot.scheduleTraceHom source target :=
  TraceAnalyticMotive.scheduleRepresentableMap_preimage
    source
    target

/-- The preimage of the top-root weight-drop representable map is the weight-drop trace morphism. -/
theorem AnalyticMotivesRoot.weightDropRepresentableMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (AnalyticMotivesRoot.weightDropRepresentableMap source target) =
      AnalyticMotivesRoot.weightDropTraceHom source target :=
  TraceAnalyticMotive.weightDropRepresentableMap_preimage
    source
    target

/-- The preimage of the top-root Fubini representable map is the Fubini trace morphism. -/
theorem AnalyticMotivesRoot.fubiniRepresentableMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (AnalyticMotivesRoot.fubiniRepresentableMap source target) =
      AnalyticMotivesRoot.fubiniTraceHom source target :=
  TraceAnalyticMotive.fubiniRepresentableMap_preimage
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
