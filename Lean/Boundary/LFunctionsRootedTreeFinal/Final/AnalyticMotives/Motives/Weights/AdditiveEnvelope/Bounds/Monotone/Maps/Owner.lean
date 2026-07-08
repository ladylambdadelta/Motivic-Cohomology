import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Maps.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Monotone.Complexes.Owner

/-!
# Monotonicity of bounded-complex chain maps

A chain map between complexes bounded by `lower` is also a chain map between
the same underlying complexes regarded as bounded by any larger `upper`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Rebound a bounded-complex chain map along an inequality of bounds. -/
def TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom.rebound
    {lower upper : Nat}
    (bound_le : lower ≤ upper)
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy lower}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom
      (source.rebound bound_le)
      (target.rebound bound_le) :=
  hom

/-- Rebounding a bounded-complex chain map preserves the underlying chain map. -/
theorem TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom.rebound_eq
    {lower upper : Nat}
    (bound_le : lower ≤ upper)
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy lower}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    hom.rebound bound_le =
      hom :=
  rfl

/-- Rebounding preserves identity chain maps. -/
theorem TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom.rebound_id
    {lower upper : Nat}
    (bound_le : lower ≤ upper)
    (complex :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy lower) :
    (TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.id complex).rebound
        bound_le =
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.id
        (complex.rebound bound_le) :=
  rfl

/-- Rebounding preserves composition of bounded-complex chain maps. -/
theorem TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom.rebound_comp
    {lower upper : Nat}
    (bound_le : lower ≤ upper)
    {first second third :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy lower}
    (left :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom first second)
    (right :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom second third) :
    (TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.comp
        left
        right).rebound bound_le =
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.comp
        (left.rebound bound_le)
        (right.rebound bound_le) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
