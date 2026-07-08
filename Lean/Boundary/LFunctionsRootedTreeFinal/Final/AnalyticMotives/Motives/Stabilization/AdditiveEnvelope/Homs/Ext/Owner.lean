import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homs.Algebra.Owner

/-!
# Extensionality for additive-envelope matrix homs

Matrix-valued analytic trace correspondences are equal when all entries are
equal.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Matrix homs are determined by their entries. -/
theorem TraceAnalyticAdditiveHom.ext
    {source target : TraceAnalyticAdditiveObject}
    {left right : TraceAnalyticAdditiveHom source target}
    (entries_eq :
      (sourceIndex : Fin source.length) →
        (targetIndex : Fin target.length) →
          left.entry sourceIndex targetIndex =
            right.entry sourceIndex targetIndex) :
    left = right :=
  funext
    (fun sourceIndex =>
      funext
        (fun targetIndex =>
          entries_eq sourceIndex targetIndex))

/-- Matrix hom equality is entrywise equality, forward direction. -/
theorem TraceAnalyticAdditiveHom.entry_eq_of_eq
    {source target : TraceAnalyticAdditiveObject}
    {left right : TraceAnalyticAdditiveHom source target}
    (hom_eq : left = right)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    left.entry sourceIndex targetIndex =
      right.entry sourceIndex targetIndex :=
  congrFun
    (congrFun hom_eq sourceIndex)
    targetIndex

end AnalyticMotives
end LFunctions
end Boundary
