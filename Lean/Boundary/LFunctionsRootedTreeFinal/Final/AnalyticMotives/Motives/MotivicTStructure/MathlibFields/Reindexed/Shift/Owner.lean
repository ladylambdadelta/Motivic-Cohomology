import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Weights.Source.Bounds.Stable.Shift.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.Reindexed.Shift.Arithmetic.Owner

/-!
# Shift fields for the Mathlib-facing analytic motivic predicates

This file proves the actual `LE_shift` and `GE_shift` fields for the
reindexed analytic motivic predicates.  The proof unpacks iso-closed
representatives, applies the categorical shift, and uses the stable
representative shift isomorphism.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Mathlib `TStructure.LE_shift` field for the reindexed analytic predicates.

The Mathlib-facing `LE` predicate is the opposite-cut analytic coaisle, so the
underlying representative degree bound is transported by
`neg_target_le_degree_add_shift`. -/
theorem TraceAnalyticMotivicTStructure.mathlibLE_shift
    (n a n' : ℤ)
    (h : a + n' = n)
    (X : TraceAnalyticDMgmComparisonSource)
    (hX : TraceAnalyticMotivicTStructure.mathlibLE n X) :
    TraceAnalyticMotivicTStructure.mathlibLE n' (X⟦a⟧) :=
  Exists.elim hX
    (fun representative representativeData =>
      Exists.elim representativeData
        (fun representativeMembership representativeIsoData =>
          Nonempty.elim representativeIsoData
            (fun representativeIso =>
              Exists.elim representativeMembership
                (fun bound boundData =>
                  Exists.elim boundData
                    (fun complex complexData =>
                      Exists.elim complexData
                        (fun degree degreeData =>
                          And.elim degreeData
                            (fun cut_le_degree representative_eq =>
                              match representative_eq with
                              | rfl =>
                                  Exists.intro
                                    (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
                                      complex
                                      (degree + a))
                                    (Exists.intro
                                      bound
                                      (Exists.intro
                                        complex
                                        (Exists.intro
                                          (degree + a)
                                          (And.intro
                                            (TraceAnalyticMotivicTStructure.neg_target_le_degree_add_shift
                                              n
                                              a
                                              n'
                                              degree
                                              h
                                              cut_le_degree)
                                            rfl))))
                                    (Nonempty.intro
                                      (((shiftFunctor
                                          TraceAnalyticDMgmComparisonSource
                                          a).mapIso
                                          representativeIso) ≪≫
                                        (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObjectAddRightIso
                                          complex
                                          degree
                                          a).symm)))))))))))

/-- Mathlib `TStructure.GE_shift` field for the reindexed analytic predicates.

The Mathlib-facing `GE` predicate is the opposite-cut analytic aisle, so the
underlying representative degree bound is transported by
`degree_add_shift_le_neg_target`. -/
theorem TraceAnalyticMotivicTStructure.mathlibGE_shift
    (n a n' : ℤ)
    (h : a + n' = n)
    (X : TraceAnalyticDMgmComparisonSource)
    (hX : TraceAnalyticMotivicTStructure.mathlibGE n X) :
    TraceAnalyticMotivicTStructure.mathlibGE n' (X⟦a⟧) :=
  Exists.elim hX
    (fun representative representativeData =>
      Exists.elim representativeData
        (fun representativeMembership representativeIsoData =>
          Nonempty.elim representativeIsoData
            (fun representativeIso =>
              Exists.elim representativeMembership
                (fun bound boundData =>
                  Exists.elim boundData
                    (fun complex complexData =>
                      Exists.elim complexData
                        (fun degree degreeData =>
                          And.elim degreeData
                            (fun degree_le_cut representative_eq =>
                              match representative_eq with
                              | rfl =>
                                  Exists.intro
                                    (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
                                      complex
                                      (degree + a))
                                    (Exists.intro
                                      bound
                                      (Exists.intro
                                        complex
                                        (Exists.intro
                                          (degree + a)
                                          (And.intro
                                            (TraceAnalyticMotivicTStructure.degree_add_shift_le_neg_target
                                              n
                                              a
                                              n'
                                              degree
                                              h
                                              degree_le_cut)
                                            rfl))))
                                    (Nonempty.intro
                                      (((shiftFunctor
                                          TraceAnalyticDMgmComparisonSource
                                          a).mapIso
                                          representativeIso) ≪≫
                                        (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObjectAddRightIso
                                          complex
                                          degree
                                          a).symm)))))))))))

end AnalyticMotives
end LFunctions
end Boundary
