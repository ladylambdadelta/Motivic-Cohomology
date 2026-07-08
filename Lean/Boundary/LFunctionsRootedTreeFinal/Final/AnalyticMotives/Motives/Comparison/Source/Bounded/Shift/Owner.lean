import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.Bounded.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Weights.Source.Bounds.Stable.Shift.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Weights.Source.Bounds.Stable.ZeroShift.Owner

/-!
# Shift closure for bounded stable comparison-source objects

Bounded stable comparison-source objects are generated up to isomorphism by
bounded analytic complexes.  This file proves that the iso-closed bounded
source is closed under the ambient stable shift, using the already constructed
zero-shift and add-right shifted-representative isomorphisms.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource

/-- The ambient shift of a concrete bounded stable representative is bounded
stable. -/
theorem boundedStableObject_shift_of_representative
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    TraceAnalyticDMgmComparisonSource.boundedStableObject
      ((TraceAnalyticMotiveComparison.sourceStableWeightBoundedObject
        complex)⟦degree⟧) :=
  let shiftedDegree_mem :
      TraceAnalyticDMgmComparisonSource.boundedStableObject
        (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
          complex
          degree) :=
    TraceAnalyticDMgmComparisonSource
      .boundedStableObject_of_sourceStableShiftedWeightBoundedObject
        complex
        degree
  let shiftedZeroAdd_mem :
      TraceAnalyticDMgmComparisonSource.boundedStableObject
        (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
          complex
          (0 + degree)) :=
    Eq.subst
      (motive := fun shiftedDegree =>
        TraceAnalyticDMgmComparisonSource.boundedStableObject
          (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
            complex
            shiftedDegree))
      (Eq.symm (zero_add degree))
      shiftedDegree_mem
  let shiftedRepresentativeIso :
      TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
          complex
          (0 + degree) ≅
        (TraceAnalyticMotiveComparison.sourceStableWeightBoundedObject
          complex)⟦degree⟧ :=
    TraceAnalyticMotiveComparison
      .sourceStableShiftedWeightBoundedObjectAddRightIso
        complex
        0
        degree ≪≫
      (shiftFunctor TraceAnalyticDMgmComparisonSource degree).mapIso
        (TraceAnalyticMotiveComparison
          .sourceStableShiftedWeightBoundedObjectZeroIso complex)
  CategoryTheory.mem_of_iso
    (P := TraceAnalyticDMgmComparisonSource.boundedStableObject)
    shiftedRepresentativeIso
    shiftedZeroAdd_mem

/-- The ambient shift of any bounded stable comparison-source object remains
bounded stable. -/
theorem boundedStableObject_shift
    {object : TraceAnalyticDMgmComparisonSource}
    (membership :
      TraceAnalyticDMgmComparisonSource.boundedStableObject object)
    (degree : ℤ) :
    TraceAnalyticDMgmComparisonSource.boundedStableObject
      (object⟦degree⟧) :=
  Exists.elim
    membership
    (fun representative representativeData =>
      Exists.elim
        representativeData
        (fun representativeMembership objectIsoData =>
          Nonempty.elim
            objectIsoData
            (fun objectIso =>
              Exists.elim
                representativeMembership
                (fun bound boundData =>
                  Exists.elim
                    boundData
                    (fun complex representative_eq =>
                      let shiftedRepresentative_mem :
                          TraceAnalyticDMgmComparisonSource
                            .boundedStableObject
                            (representative⟦degree⟧) :=
                        Eq.subst
                          (motive := fun candidate =>
                            TraceAnalyticDMgmComparisonSource
                              .boundedStableObject
                              (candidate⟦degree⟧))
                          (Eq.symm representative_eq)
                          (TraceAnalyticDMgmComparisonSource
                            .boundedStableObject_shift_of_representative
                              complex
                              degree)
                      CategoryTheory.mem_of_iso
                        (P := TraceAnalyticDMgmComparisonSource
                          .boundedStableObject)
                        ((shiftFunctor
                            TraceAnalyticDMgmComparisonSource
                            degree).mapIso objectIso).symm
                        shiftedRepresentative_mem)))))

end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
