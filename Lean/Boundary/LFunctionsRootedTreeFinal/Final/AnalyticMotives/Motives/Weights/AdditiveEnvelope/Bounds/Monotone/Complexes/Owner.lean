import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Complexes.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Monotone.Objects.Owner

/-!
# Monotonicity of bounded additive analytic complexes

Increasing the numeric weight bound gives an inclusion of degreewise bounded
additive analytic complexes.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Rebound a bounded additive analytic complex along an inequality of bounds. -/
def TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.rebound
    {lower upper : Nat}
    (bound_le : lower ≤ upper)
    (complex : TraceAnalyticAdditiveCochainComplex.WeightBoundedBy lower) :
    TraceAnalyticAdditiveCochainComplex.WeightBoundedBy upper :=
  ⟨complex.complex,
    fun degree =>
      Nat.le_trans
        (complex.degreeWeight_le degree)
        bound_le⟩

/-- Rebounding preserves the underlying additive analytic complex. -/
theorem TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.rebound_complex
    {lower upper : Nat}
    (bound_le : lower ≤ upper)
    (complex : TraceAnalyticAdditiveCochainComplex.WeightBoundedBy lower) :
    (complex.rebound bound_le).complex =
      complex.complex :=
  rfl

/-- Rebounding commutes with extracting bounded degree objects. -/
theorem TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.rebound_degreeObject_object
    {lower upper : Nat}
    (bound_le : lower ≤ upper)
    (complex : TraceAnalyticAdditiveCochainComplex.WeightBoundedBy lower)
    (degree : ℤ) :
    ((complex.rebound bound_le).degreeObject degree).object =
      (complex.degreeObject degree).object :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
