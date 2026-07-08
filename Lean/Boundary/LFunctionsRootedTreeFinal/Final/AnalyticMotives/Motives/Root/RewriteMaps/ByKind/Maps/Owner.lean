import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.RewriteMaps.ByKind.Endpoints.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Presheaves.RewriteMaps.ByKind.Maps.Owner

/-!
# Motive-root by-kind rewrite maps

This file exposes the representable and lifted representable-subcategory maps
of the primitive analytic rewrite kinds at the motive root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The motive root exposes the Stokes representable map. -/
def TraceAnalyticMotive.stokesRepresentableMap
    (source target : QTraceExpression) :
    TraceCorQPresheafHom
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.stokes source target).sourceObject)
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.stokes source target).targetObject) :=
  TraceRewriteGenerator.stokesRepresentableMap source target

/-- The motive root exposes the residue representable map. -/
def TraceAnalyticMotive.residueRepresentableMap
    (source target : QTraceExpression) :
    TraceCorQPresheafHom
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.residue source target).sourceObject)
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.residue source target).targetObject) :=
  TraceRewriteGenerator.residueRepresentableMap source target

/-- The motive root exposes the channel representable map. -/
def TraceAnalyticMotive.channelRepresentableMap
    (source target : QTraceExpression) :
    TraceCorQPresheafHom
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.channel source target).sourceObject)
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.channel source target).targetObject) :=
  TraceRewriteGenerator.channelRepresentableMap source target

/-- The motive root exposes the refinement representable map. -/
def TraceAnalyticMotive.refinementRepresentableMap
    (source target : QTraceExpression) :
    TraceCorQPresheafHom
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.refinement source target).sourceObject)
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.refinement source target).targetObject) :=
  TraceRewriteGenerator.refinementRepresentableMap source target

/-- The motive root exposes the schedule representable map. -/
def TraceAnalyticMotive.scheduleRepresentableMap
    (source target : QTraceExpression) :
    TraceCorQPresheafHom
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.schedule source target).sourceObject)
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.schedule source target).targetObject) :=
  TraceRewriteGenerator.scheduleRepresentableMap source target

/-- The motive root exposes the weight-drop representable map. -/
def TraceAnalyticMotive.weightDropRepresentableMap
    (source target : QTraceExpression) :
    TraceCorQPresheafHom
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.weightDrop source target).sourceObject)
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.weightDrop source target).targetObject) :=
  TraceRewriteGenerator.weightDropRepresentableMap source target

/-- The motive root exposes the Fubini representable map. -/
def TraceAnalyticMotive.fubiniRepresentableMap
    (source target : QTraceExpression) :
    TraceCorQPresheafHom
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.fubini source target).sourceObject)
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.fubini source target).targetObject) :=
  TraceRewriteGenerator.fubiniRepresentableMap source target

/-- The motive root exposes the lifted Stokes representable-subcategory map. -/
def TraceAnalyticMotive.stokesRepresentableSubcategoryMap
    (source target : QTraceExpression) :
    (TraceCorQRepresentablePresheaf.yoneda).obj
        (TraceRewriteGenerator.stokes source target).sourceObject ⟶
      (TraceCorQRepresentablePresheaf.yoneda).obj
        (TraceRewriteGenerator.stokes source target).targetObject :=
  TraceRewriteGenerator.stokesRepresentableSubcategoryMap source target

/-- The motive root exposes the lifted residue representable-subcategory map. -/
def TraceAnalyticMotive.residueRepresentableSubcategoryMap
    (source target : QTraceExpression) :
    (TraceCorQRepresentablePresheaf.yoneda).obj
        (TraceRewriteGenerator.residue source target).sourceObject ⟶
      (TraceCorQRepresentablePresheaf.yoneda).obj
        (TraceRewriteGenerator.residue source target).targetObject :=
  TraceRewriteGenerator.residueRepresentableSubcategoryMap source target

/-- The motive root exposes the lifted channel representable-subcategory map. -/
def TraceAnalyticMotive.channelRepresentableSubcategoryMap
    (source target : QTraceExpression) :
    (TraceCorQRepresentablePresheaf.yoneda).obj
        (TraceRewriteGenerator.channel source target).sourceObject ⟶
      (TraceCorQRepresentablePresheaf.yoneda).obj
        (TraceRewriteGenerator.channel source target).targetObject :=
  TraceRewriteGenerator.channelRepresentableSubcategoryMap source target

/-- The motive root exposes the lifted refinement representable-subcategory map. -/
def TraceAnalyticMotive.refinementRepresentableSubcategoryMap
    (source target : QTraceExpression) :
    (TraceCorQRepresentablePresheaf.yoneda).obj
        (TraceRewriteGenerator.refinement source target).sourceObject ⟶
      (TraceCorQRepresentablePresheaf.yoneda).obj
        (TraceRewriteGenerator.refinement source target).targetObject :=
  TraceRewriteGenerator.refinementRepresentableSubcategoryMap source target

/-- The motive root exposes the lifted schedule representable-subcategory map. -/
def TraceAnalyticMotive.scheduleRepresentableSubcategoryMap
    (source target : QTraceExpression) :
    (TraceCorQRepresentablePresheaf.yoneda).obj
        (TraceRewriteGenerator.schedule source target).sourceObject ⟶
      (TraceCorQRepresentablePresheaf.yoneda).obj
        (TraceRewriteGenerator.schedule source target).targetObject :=
  TraceRewriteGenerator.scheduleRepresentableSubcategoryMap source target

/-- The motive root exposes the lifted weight-drop representable-subcategory map. -/
def TraceAnalyticMotive.weightDropRepresentableSubcategoryMap
    (source target : QTraceExpression) :
    (TraceCorQRepresentablePresheaf.yoneda).obj
        (TraceRewriteGenerator.weightDrop source target).sourceObject ⟶
      (TraceCorQRepresentablePresheaf.yoneda).obj
        (TraceRewriteGenerator.weightDrop source target).targetObject :=
  TraceRewriteGenerator.weightDropRepresentableSubcategoryMap source target

/-- The motive root exposes the lifted Fubini representable-subcategory map. -/
def TraceAnalyticMotive.fubiniRepresentableSubcategoryMap
    (source target : QTraceExpression) :
    (TraceCorQRepresentablePresheaf.yoneda).obj
        (TraceRewriteGenerator.fubini source target).sourceObject ⟶
      (TraceCorQRepresentablePresheaf.yoneda).obj
        (TraceRewriteGenerator.fubini source target).targetObject :=
  TraceRewriteGenerator.fubiniRepresentableSubcategoryMap source target

end AnalyticMotives
end LFunctions
end Boundary
