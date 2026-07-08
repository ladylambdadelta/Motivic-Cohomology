import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Aisles.Owner

/-!
# Representative unpacking for Mathlib-facing orthogonality

This file peels the representative layer of the Mathlib `TStructure.zero'`
field.  Vanishing for concrete shifted bounded endpoints implies vanishing for
the concrete representative coaisle and aisle predicates at the cuts used by
the reindexed Mathlib field.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Shifted-bounded endpoint vanishing implies representative-level
orthogonality from the concrete coaisle at `0` to the concrete aisle at `-1`.
-/
theorem representative_zero_of_shiftedBounded_zero
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
        (hom :
          TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
            sourceComplex
            sourceDegree ⟶
          TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
            targetComplex
            targetDegree) →
        hom = 0)
    {source target : TraceAnalyticDMgmComparisonSource}
    (hom : source ⟶ target)
    (source_mem : TraceAnalyticMotivicTStructure.coaisleGE (-0) source)
    (target_mem : TraceAnalyticMotivicTStructure.aisleLE (-1) target) :
    hom = 0 :=
  Exists.elim
    source_mem
    (fun sourceBound sourceBoundData =>
      Exists.elim
        sourceBoundData
        (fun sourceComplex sourceComplexData =>
          Exists.elim
            sourceComplexData
            (fun sourceDegree sourceDegreeData =>
              And.elim
                sourceDegreeData
                (fun sourceDegree_mem source_eq =>
                  Exists.elim
                    target_mem
                    (fun targetBound targetBoundData =>
                      Exists.elim
                        targetBoundData
                        (fun targetComplex targetComplexData =>
                          Exists.elim
                            targetComplexData
                            (fun targetDegree targetDegreeData =>
                              And.elim
                                targetDegreeData
                                (fun targetDegree_mem target_eq =>
                                  match source_eq, target_eq with
                                  | rfl, rfl =>
                                      shiftedBounded_zero
                                        sourceComplex
                                        sourceDegree
                                        targetComplex
                                        targetDegree
                                        sourceDegree_mem
                                        targetDegree_mem
                                        hom)))))))))

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
