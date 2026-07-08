import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homs.Ext.Owner

/-!
# Transport of additive-envelope matrix entries

Projection and inclusion matrices for direct sums use trace-correspondence
identities transported across component equalities.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Transport a trace correspondence across equalities of its source and target objects. -/
def TraceAnalyticAdditiveHom.transportEntry
    {source source' target target' : TraceCorQObject}
    (source_eq : source = source')
    (target_eq : target = target')
    (hom : TraceCorQHom source target) :
    TraceCorQHom source' target' :=
  Eq.ndrec
    (Eq.ndrec hom target_eq)
    source_eq

/-- Transport with reflexive source and target equalities is the original entry. -/
theorem TraceAnalyticAdditiveHom.transportEntry_rfl
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    TraceAnalyticAdditiveHom.transportEntry rfl rfl hom =
      hom :=
  rfl

/-- Transport an identity trace correspondence across an object equality. -/
def TraceAnalyticAdditiveHom.transportedId
    {source target : TraceCorQObject}
    (object_eq : source = target) :
    TraceCorQHom source target :=
  TraceAnalyticAdditiveHom.transportEntry
    rfl
    object_eq
    (TraceCorQHom.id source)

/-- Transporting an identity along reflexive equality is the identity. -/
theorem TraceAnalyticAdditiveHom.transportedId_rfl
    (object : TraceCorQObject) :
    TraceAnalyticAdditiveHom.transportedId (source := object) (target := object) rfl =
      TraceCorQHom.id object :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
