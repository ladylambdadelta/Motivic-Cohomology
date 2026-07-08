import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.RewriteMaps.ByKind.Endpoints.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.RewriteMaps.ByKind.Maps.Owner

/-!
# Top-root by-kind rewrite maps

This file exposes representable presheaf maps and lifted representable-
subcategory maps for the seven one-step analytic trace rewrite kinds under
`AnalyticMotivesRoot`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes the Stokes representable map. -/
def AnalyticMotivesRoot.stokesRepresentableMap
    (source target : QTraceExpression) :
    TraceCorQPresheafHom
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.stokes source target).sourceObject)
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.stokes source target).targetObject) :=
  TraceAnalyticMotive.stokesRepresentableMap source target

/-- The top root exposes the residue representable map. -/
def AnalyticMotivesRoot.residueRepresentableMap
    (source target : QTraceExpression) :
    TraceCorQPresheafHom
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.residue source target).sourceObject)
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.residue source target).targetObject) :=
  TraceAnalyticMotive.residueRepresentableMap source target

/-- The top root exposes the channel representable map. -/
def AnalyticMotivesRoot.channelRepresentableMap
    (source target : QTraceExpression) :
    TraceCorQPresheafHom
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.channel source target).sourceObject)
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.channel source target).targetObject) :=
  TraceAnalyticMotive.channelRepresentableMap source target

/-- The top root exposes the refinement representable map. -/
def AnalyticMotivesRoot.refinementRepresentableMap
    (source target : QTraceExpression) :
    TraceCorQPresheafHom
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.refinement source target).sourceObject)
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.refinement source target).targetObject) :=
  TraceAnalyticMotive.refinementRepresentableMap source target

/-- The top root exposes the schedule representable map. -/
def AnalyticMotivesRoot.scheduleRepresentableMap
    (source target : QTraceExpression) :
    TraceCorQPresheafHom
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.schedule source target).sourceObject)
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.schedule source target).targetObject) :=
  TraceAnalyticMotive.scheduleRepresentableMap source target

/-- The top root exposes the weight-drop representable map. -/
def AnalyticMotivesRoot.weightDropRepresentableMap
    (source target : QTraceExpression) :
    TraceCorQPresheafHom
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.weightDrop source target).sourceObject)
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.weightDrop source target).targetObject) :=
  TraceAnalyticMotive.weightDropRepresentableMap source target

/-- The top root exposes the Fubini representable map. -/
def AnalyticMotivesRoot.fubiniRepresentableMap
    (source target : QTraceExpression) :
    TraceCorQPresheafHom
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.fubini source target).sourceObject)
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.fubini source target).targetObject) :=
  TraceAnalyticMotive.fubiniRepresentableMap source target

/-- The top root exposes the lifted Stokes representable-subcategory map. -/
def AnalyticMotivesRoot.stokesRepresentableSubcategoryMap
    (source target : QTraceExpression) :
    (TraceCorQRepresentablePresheaf.yoneda).obj
        (TraceRewriteGenerator.stokes source target).sourceObject ⟶
      (TraceCorQRepresentablePresheaf.yoneda).obj
        (TraceRewriteGenerator.stokes source target).targetObject :=
  TraceAnalyticMotive.stokesRepresentableSubcategoryMap source target

/-- The top root exposes the lifted residue representable-subcategory map. -/
def AnalyticMotivesRoot.residueRepresentableSubcategoryMap
    (source target : QTraceExpression) :
    (TraceCorQRepresentablePresheaf.yoneda).obj
        (TraceRewriteGenerator.residue source target).sourceObject ⟶
      (TraceCorQRepresentablePresheaf.yoneda).obj
        (TraceRewriteGenerator.residue source target).targetObject :=
  TraceAnalyticMotive.residueRepresentableSubcategoryMap source target

/-- The top root exposes the lifted channel representable-subcategory map. -/
def AnalyticMotivesRoot.channelRepresentableSubcategoryMap
    (source target : QTraceExpression) :
    (TraceCorQRepresentablePresheaf.yoneda).obj
        (TraceRewriteGenerator.channel source target).sourceObject ⟶
      (TraceCorQRepresentablePresheaf.yoneda).obj
        (TraceRewriteGenerator.channel source target).targetObject :=
  TraceAnalyticMotive.channelRepresentableSubcategoryMap source target

/-- The top root exposes the lifted refinement representable-subcategory map. -/
def AnalyticMotivesRoot.refinementRepresentableSubcategoryMap
    (source target : QTraceExpression) :
    (TraceCorQRepresentablePresheaf.yoneda).obj
        (TraceRewriteGenerator.refinement source target).sourceObject ⟶
      (TraceCorQRepresentablePresheaf.yoneda).obj
        (TraceRewriteGenerator.refinement source target).targetObject :=
  TraceAnalyticMotive.refinementRepresentableSubcategoryMap source target

/-- The top root exposes the lifted schedule representable-subcategory map. -/
def AnalyticMotivesRoot.scheduleRepresentableSubcategoryMap
    (source target : QTraceExpression) :
    (TraceCorQRepresentablePresheaf.yoneda).obj
        (TraceRewriteGenerator.schedule source target).sourceObject ⟶
      (TraceCorQRepresentablePresheaf.yoneda).obj
        (TraceRewriteGenerator.schedule source target).targetObject :=
  TraceAnalyticMotive.scheduleRepresentableSubcategoryMap source target

/-- The top root exposes the lifted weight-drop representable-subcategory map. -/
def AnalyticMotivesRoot.weightDropRepresentableSubcategoryMap
    (source target : QTraceExpression) :
    (TraceCorQRepresentablePresheaf.yoneda).obj
        (TraceRewriteGenerator.weightDrop source target).sourceObject ⟶
      (TraceCorQRepresentablePresheaf.yoneda).obj
        (TraceRewriteGenerator.weightDrop source target).targetObject :=
  TraceAnalyticMotive.weightDropRepresentableSubcategoryMap source target

/-- The top root exposes the lifted Fubini representable-subcategory map. -/
def AnalyticMotivesRoot.fubiniRepresentableSubcategoryMap
    (source target : QTraceExpression) :
    (TraceCorQRepresentablePresheaf.yoneda).obj
        (TraceRewriteGenerator.fubini source target).sourceObject ⟶
      (TraceCorQRepresentablePresheaf.yoneda).obj
        (TraceRewriteGenerator.fubini source target).targetObject :=
  TraceAnalyticMotive.fubiniRepresentableSubcategoryMap source target

end AnalyticMotives
end LFunctions
end Boundary
