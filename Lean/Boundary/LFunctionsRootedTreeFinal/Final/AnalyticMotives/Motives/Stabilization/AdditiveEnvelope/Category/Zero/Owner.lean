import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Category.Entries.Owner

/-!
# The zero object in the analytic additive envelope

The empty finite trace family is initial and terminal at the level of concrete
matrix homs, because every matrix from or to it has an impossible row or column
index.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The zero object of the analytic additive-envelope category. -/
def TraceAnalyticAdditiveCategory.zeroObject :
    TraceAnalyticAdditiveCategoryObject :=
  TraceAnalyticAdditiveObject.zero

/-- The zero category object has no components. -/
theorem TraceAnalyticAdditiveCategory.zeroObject_length :
    TraceAnalyticAdditiveCategory.zeroObject.length =
      0 :=
  TraceAnalyticAdditiveObject.zero_length

/-- There is at most one matrix hom from the empty trace family. -/
theorem TraceAnalyticAdditiveCategory.hom_from_zero_ext
    (target : TraceAnalyticAdditiveCategoryObject)
    (left right :
      TraceAnalyticAdditiveCategoryHom
        TraceAnalyticAdditiveCategory.zeroObject
        target) :
    left = right :=
  funext
    (fun sourceIndex =>
      Fin.elim0 sourceIndex)

/-- There is at most one matrix hom to the empty trace family. -/
theorem TraceAnalyticAdditiveCategory.hom_to_zero_ext
    (source : TraceAnalyticAdditiveCategoryObject)
    (left right :
      TraceAnalyticAdditiveCategoryHom
        source
        TraceAnalyticAdditiveCategory.zeroObject) :
    left = right :=
  funext
    (fun sourceIndex =>
      funext
        (fun targetIndex =>
          Fin.elim0 targetIndex))

end AnalyticMotives
end LFunctions
end Boundary
