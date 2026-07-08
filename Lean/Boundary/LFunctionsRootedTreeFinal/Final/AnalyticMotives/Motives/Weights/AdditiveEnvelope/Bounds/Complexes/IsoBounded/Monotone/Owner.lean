import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Complexes.IsoBounded.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Objects.IsoBounded.Monotone.Owner

/-!
# Monotonicity of degreewise iso-bounded complexes

Increasing the numeric weight bound preserves degreewise iso-boundedness by
rebounding every bounded degree representative.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Rebound degreewise iso-bounded complex data along an inequality of bounds. -/
def TraceAnalyticAdditiveCochainComplex.DegreewiseIsoBoundedBy.rebound
    {complex : TraceAnalyticAdditiveCochainComplex}
    {lower upper : Nat}
    (bound_le : lower ≤ upper)
    (isoBounded :
      TraceAnalyticAdditiveCochainComplex.DegreewiseIsoBoundedBy
        complex
        lower) :
    TraceAnalyticAdditiveCochainComplex.DegreewiseIsoBoundedBy
      complex
      upper where
  degreeIsoBounded :=
    fun degree =>
      (isoBounded.degreeObject degree).rebound bound_le

/-- Rebounding degreewise iso-bounded data preserves the representative object in each degree. -/
theorem TraceAnalyticAdditiveCochainComplex.DegreewiseIsoBoundedBy.rebound_degreeObject_representative_object
    {complex : TraceAnalyticAdditiveCochainComplex}
    {lower upper : Nat}
    (bound_le : lower ≤ upper)
    (isoBounded :
      TraceAnalyticAdditiveCochainComplex.DegreewiseIsoBoundedBy
        complex
        lower)
    (degree : ℤ) :
    ((isoBounded.rebound bound_le).degreeObject degree).boundedRepresentative.object =
      (isoBounded.degreeObject degree).boundedRepresentative.object :=
  rfl

/-- Rebounded degree representatives satisfy the larger ambient bound. -/
theorem TraceAnalyticAdditiveCochainComplex.DegreewiseIsoBoundedBy.rebound_degreeObject_weightLevel_le
    {complex : TraceAnalyticAdditiveCochainComplex}
    {lower upper : Nat}
    (bound_le : lower ≤ upper)
    (isoBounded :
      TraceAnalyticAdditiveCochainComplex.DegreewiseIsoBoundedBy
        complex
        lower)
    (degree : ℤ) :
    ((isoBounded.rebound bound_le).degreeObject degree).boundedRepresentative.object.weightLevel ≤
      upper :=
  (isoBounded.rebound bound_le).degreeObject_weightLevel_le degree

end AnalyticMotives
end LFunctions
end Boundary
