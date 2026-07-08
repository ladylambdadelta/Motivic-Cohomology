import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Weights.Source.Bounds.Stable.Owner

/-!
# Rebounding shifted-bounded orthogonality endpoints

This file reduces shifted-bounded endpoint vanishing with two independent
weight bounds to the same statement after rebounding both endpoints to a common
maximum bound.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- It is enough to prove shifted-bounded endpoint vanishing when source and
target are bounded by the same natural number. -/
theorem shiftedBounded_zero_of_commonBound_zero
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
        (hom :
          TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
              sourceComplex
              sourceDegree ⟶
            TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
              targetComplex
              targetDegree) →
        hom = 0)
    {sourceBound targetBound : Nat}
    (sourceComplex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy sourceBound)
    (sourceDegree : ℤ)
    (targetComplex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy targetBound)
    (targetDegree : ℤ)
    (sourceDegree_mem : -0 ≤ sourceDegree)
    (targetDegree_mem : targetDegree ≤ -1)
    (hom :
      TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
          sourceComplex
          sourceDegree ⟶
        TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
          targetComplex
          targetDegree) :
    hom = 0 :=
  let commonBound : Nat := Nat.max sourceBound targetBound
  let sourceBound_le_common : sourceBound ≤ commonBound :=
    Nat.le_max_left sourceBound targetBound
  let targetBound_le_common : targetBound ≤ commonBound :=
    Nat.le_max_right sourceBound targetBound
  let source_eq :
      TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
          (sourceComplex.rebound sourceBound_le_common)
          sourceDegree =
        TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
          sourceComplex
          sourceDegree :=
    TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject_rebound
      sourceBound_le_common
      sourceComplex
      sourceDegree
  let target_eq :
      TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
          (targetComplex.rebound targetBound_le_common)
          targetDegree =
        TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
          targetComplex
          targetDegree :=
    TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject_rebound
      targetBound_le_common
      targetComplex
      targetDegree
  Eq.subst
    (motive := fun sourceObject =>
      ∀ homFromSource :
        sourceObject ⟶
          TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
            targetComplex
            targetDegree,
        homFromSource = 0)
    source_eq
    (Eq.subst
      (motive := fun targetObject =>
        ∀ homToTarget :
          TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
              (sourceComplex.rebound sourceBound_le_common)
              sourceDegree ⟶
            targetObject,
          homToTarget = 0)
      target_eq
      (fun homCommon =>
        commonBound_zero
          (sourceComplex.rebound sourceBound_le_common)
          sourceDegree
          (targetComplex.rebound targetBound_le_common)
          targetDegree
          sourceDegree_mem
          targetDegree_mem
          homCommon))
    hom

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
