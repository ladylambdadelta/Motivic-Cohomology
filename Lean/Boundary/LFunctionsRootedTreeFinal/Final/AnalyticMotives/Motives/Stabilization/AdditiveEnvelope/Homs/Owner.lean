import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Objects.Owner

/-!
# Matrix homs in the additive envelope

Morphisms between finite analytic trace families are matrices of Q-linear trace
correspondences.  This is the concrete additive hull needed before invoking the
homotopy-category triangulated construction.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A matrix-valued analytic trace correspondence between finite trace families. -/
abbrev TraceAnalyticAdditiveHom
    (source target : TraceAnalyticAdditiveObject) :=
  (sourceIndex : Fin source.length) →
    (targetIndex : Fin target.length) →
      TraceCorQHom
        (source.component sourceIndex)
        (target.component targetIndex)

/-- The source component of a matrix-valued analytic trace correspondence. -/
def TraceAnalyticAdditiveHom.sourceComponent
    {source target : TraceAnalyticAdditiveObject}
    (hom : TraceAnalyticAdditiveHom source target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    TraceCorQObject :=
  source.component sourceIndex

/-- The target component of a matrix-valued analytic trace correspondence. -/
def TraceAnalyticAdditiveHom.targetComponent
    {source target : TraceAnalyticAdditiveObject}
    (hom : TraceAnalyticAdditiveHom source target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    TraceCorQObject :=
  target.component targetIndex

/-- Evaluation of a matrix-valued analytic trace correspondence at one entry. -/
def TraceAnalyticAdditiveHom.entry
    {source target : TraceAnalyticAdditiveObject}
    (hom : TraceAnalyticAdditiveHom source target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    TraceCorQHom
      (source.component sourceIndex)
      (target.component targetIndex) :=
  hom sourceIndex targetIndex

/-- Entry evaluation is ordinary function application. -/
theorem TraceAnalyticAdditiveHom.entry_eq
    {source target : TraceAnalyticAdditiveObject}
    (hom : TraceAnalyticAdditiveHom source target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    hom.entry sourceIndex targetIndex =
      hom sourceIndex targetIndex :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
