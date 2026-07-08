import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Fields.Owner

/-!
# Arithmetic for derived analytic t-structure shift fields

Mathlib's `TStructure` shift fields use indices satisfying `a + n' = n`.
The concrete derived homological shift theorem uses the cut `n - a`.  This
file owns the integer equality translating between those conventions.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDerivedMotiveCategory

/-- Mathlib's shift-index equation `a + n' = n` identifies the concrete shifted
cut `n - a` with the target cut `n'`. -/
theorem cut_sub_shift_eq_target_of_add_target_eq_cut
    (n a n' : ℤ)
    (h : a + n' = n) :
    n - a = n' :=
  Eq.symm
    ((eq_sub_iff_add_eq).mpr
      (Eq.trans
        (add_comm n' a)
        h))

end TraceAnalyticDerivedMotiveCategory

end AnalyticMotives
end LFunctions
end Boundary
