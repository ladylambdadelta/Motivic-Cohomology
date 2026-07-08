import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.Reindexed.Owner

/-!
# Arithmetic for Mathlib-facing analytic motivic shift fields

Mathlib's `TStructure` shift fields use the convention `a + n' = n`.
The analytic representative calculus shifts degrees by adding `a`.  This file
owns the signed integer arithmetic translating between those two conventions.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- If Mathlib's shift indices satisfy `a + n' = n`, then adding the
categorical shift to the opposite cut gives the opposite target cut. -/
theorem TraceAnalyticMotivicTStructure.neg_add_shift_eq_neg_target
    (n a n' : ℤ)
    (h : a + n' = n) :
    -n + a = -n' :=
  Eq.trans
    (congrArg (fun index : ℤ => -index + a) h.symm)
    (Eq.trans
      (congrArg (fun index : ℤ => index + a) (neg_add_rev a n'))
      (Eq.trans
        (add_assoc (-n') (-a) a)
        (Eq.trans
          (congrArg (fun index : ℤ => -n' + index) (neg_add_cancel a))
          (add_zero (-n')))))

/-- Coaisle degree bounds transport through Mathlib's shift convention. -/
theorem TraceAnalyticMotivicTStructure.neg_target_le_degree_add_shift
    (n a n' degree : ℤ)
    (h : a + n' = n)
    (cut_le_degree : -n ≤ degree) :
    -n' ≤ degree + a :=
  le_trans
    (le_of_eq
      (TraceAnalyticMotivicTStructure.neg_add_shift_eq_neg_target
        n
        a
        n'
        h).symm)
    (add_le_add_right cut_le_degree a)

/-- Aisle degree bounds transport through Mathlib's shift convention. -/
theorem TraceAnalyticMotivicTStructure.degree_add_shift_le_neg_target
    (n a n' degree : ℤ)
    (h : a + n' = n)
    (degree_le_cut : degree ≤ -n) :
    degree + a ≤ -n' :=
  le_trans
    (add_le_add_right degree_le_cut a)
    (le_of_eq
      (TraceAnalyticMotivicTStructure.neg_add_shift_eq_neg_target
        n
        a
        n'
        h))

end AnalyticMotives
end LFunctions
end Boundary
