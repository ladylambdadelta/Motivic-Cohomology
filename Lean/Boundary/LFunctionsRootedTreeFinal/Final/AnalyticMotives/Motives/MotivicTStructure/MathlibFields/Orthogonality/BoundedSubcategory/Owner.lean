import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.Orthogonality.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.TruncationTriangle.BoundedSubcategory.Owner

/-!
# Orthogonality on bounded stable source objects

The bounded stable source is a full subcategory of the analytic comparison
source.  Its morphisms are the ambient morphisms between the underlying stable
objects, so the Mathlib-facing ambient orthogonality theorem restricts
directly to bounded objects.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource
namespace BoundedStable

/-- Shifted-bounded endpoint vanishing implies orthogonality for bounded
stable source objects in the pulled-back Mathlib-facing predicates. -/
theorem zero_of_shiftedBounded_zero
    (shiftedBounded_zero :
      ∀ {sourceBound targetBound : Nat}
        (sourceComplex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
            sourceBound)
        (sourceDegree : ℤ)
        (targetComplex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
            targetBound)
        (targetDegree : ℤ),
        -0 ≤ sourceDegree →
        targetDegree ≤ -1 →
        (endpointHom :
          TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
            sourceComplex
            sourceDegree ⟶
          TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
            targetComplex
            targetDegree) →
        endpointHom = 0)
    {source target : TraceAnalyticDMgmComparisonSource.BoundedStable}
    (hom : source ⟶ target)
    (source_mem :
      TraceAnalyticDMgmComparisonSource.BoundedStable.mathlibLE 0 source)
    (target_mem :
      TraceAnalyticDMgmComparisonSource.BoundedStable.mathlibGE 1 target) :
    hom = 0 :=
  TraceAnalyticMotivicTStructure.mathlib_zero_of_shiftedBounded_zero
    shiftedBounded_zero
    hom
    source_mem
    target_mem

/-- Common-bound shifted-bounded endpoint vanishing implies orthogonality for
bounded stable source objects in the pulled-back Mathlib-facing predicates. -/
theorem zero_of_commonBound_shiftedBounded_zero
    (commonBound_zero :
      ∀ {bound : Nat}
        (sourceComplex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
        (sourceDegree : ℤ)
        (targetComplex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
        (targetDegree : ℤ),
        -0 ≤ sourceDegree →
        targetDegree ≤ -1 →
        (endpointHom :
          TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
            sourceComplex
            sourceDegree ⟶
          TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
            targetComplex
            targetDegree) →
        endpointHom = 0)
    {source target : TraceAnalyticDMgmComparisonSource.BoundedStable}
    (hom : source ⟶ target)
    (source_mem :
      TraceAnalyticDMgmComparisonSource.BoundedStable.mathlibLE 0 source)
    (target_mem :
      TraceAnalyticDMgmComparisonSource.BoundedStable.mathlibGE 1 target) :
    hom = 0 :=
  TraceAnalyticDMgmComparisonSource.BoundedStable
    .zero_of_shiftedBounded_zero
      (TraceAnalyticMotivicTStructure
        .shiftedBounded_zero_of_commonBound_zero commonBound_zero)
      hom
      source_mem
      target_mem

end BoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
