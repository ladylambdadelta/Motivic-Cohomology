import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Category.Operations.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homs.Transport.Owner

/-!
# Entry formulas for additive-envelope category operations

The finite-family category operations are the identity matrix and matrix
composition.  This file exposes their entry formulas.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Entry formula for analytic additive-envelope category identity. -/
theorem TraceAnalyticAdditiveCategory.id_entry
    (object : TraceAnalyticAdditiveCategoryObject)
    (sourceIndex targetIndex : Fin object.length) :
    (TraceAnalyticAdditiveCategory.id object).entry sourceIndex targetIndex =
      (TraceAnalyticAdditiveHom.id object).entry sourceIndex targetIndex :=
  rfl

/-- Entry formula for analytic additive-envelope category composition. -/
theorem TraceAnalyticAdditiveCategory.comp_entry
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom source middle)
    (right : TraceAnalyticAdditiveCategoryHom middle target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    (TraceAnalyticAdditiveCategory.comp left right).entry sourceIndex targetIndex =
      Finset.univ.sum
        (fun middleIndex =>
          TraceCorQHom.comp
            (left.entry sourceIndex middleIndex)
            (right.entry middleIndex targetIndex)) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
