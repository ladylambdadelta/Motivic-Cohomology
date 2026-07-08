import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Fields.Shift.Arithmetic.Owner

/-!
# Mathlib-shape shift fields for the derived analytic t-structure surface

This file converts the concrete cut-minus-shift transport theorem into
Mathlib's `TStructure` shift-field convention `a + n' = n`.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open scoped CategoryTheory

namespace TraceAnalyticDerivedMotiveCategory

/-- Mathlib-shape `LE_shift` field for the derived analytic homological
predicate. -/
theorem tStructureLE_shift
    (n a n' : ℤ)
    (h : a + n' = n)
    (object : TraceAnalyticDerivedMotiveCategory)
    (membership :
      TraceAnalyticDerivedMotiveCategory.tStructureLE n object) :
    TraceAnalyticDerivedMotiveCategory.tStructureLE n' (object⟦a⟧) :=
  Eq.subst
    (motive := fun targetCut : ℤ =>
      TraceAnalyticDerivedMotiveCategory.tStructureLE targetCut
        (object⟦a⟧))
    (TraceAnalyticDerivedMotiveCategory
      .cut_sub_shift_eq_target_of_add_target_eq_cut
        n
        a
        n'
        h)
    (TraceAnalyticDerivedMotiveCategory.tStructureLE_shift_cutSub
      n
      a
      object
      membership)

/-- Mathlib-shape `GE_shift` field for the derived analytic homological
predicate. -/
theorem tStructureGE_shift
    (n a n' : ℤ)
    (h : a + n' = n)
    (object : TraceAnalyticDerivedMotiveCategory)
    (membership :
      TraceAnalyticDerivedMotiveCategory.tStructureGE n object) :
    TraceAnalyticDerivedMotiveCategory.tStructureGE n' (object⟦a⟧) :=
  Eq.subst
    (motive := fun targetCut : ℤ =>
      TraceAnalyticDerivedMotiveCategory.tStructureGE targetCut
        (object⟦a⟧))
    (TraceAnalyticDerivedMotiveCategory
      .cut_sub_shift_eq_target_of_add_target_eq_cut
        n
        a
        n'
        h)
    (TraceAnalyticDerivedMotiveCategory.tStructureGE_shift_cutSub
      n
      a
      object
      membership)

end TraceAnalyticDerivedMotiveCategory

end AnalyticMotives
end LFunctions
end Boundary
