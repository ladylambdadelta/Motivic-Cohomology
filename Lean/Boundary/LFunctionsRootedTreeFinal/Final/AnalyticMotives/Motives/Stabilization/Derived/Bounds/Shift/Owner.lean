import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.Bounds.Owner

/-!
# Shift stability of derived analytic homological bounds

This file exposes the Mathlib shift-sequence compatibility of derived homology
and uses it to prove the concrete cut-transport formulas for the homological
bound predicates.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDerivedMotiveCategory

attribute [local instance]
  TraceAnalyticDerivedMotiveCategory.hasDerivedCategory

/-- The shift sequence for derived analytic homology identifies degree
`degree` homology of `object⟦shift⟧` with degree `shift + degree` homology of
`object`, hence preserves and reflects zero objects. -/
theorem homologyFunctor_shift_obj_isZero_iff
    (shift degree shiftedDegree : ℤ)
    (hdegree : shift + degree = shiftedDegree)
    (object : TraceAnalyticDerivedMotiveCategory) :
    IsZero
        ((TraceAnalyticDerivedMotiveCategory.homologyFunctor degree).obj
          (object⟦shift⟧)) ↔
      IsZero
        ((TraceAnalyticDerivedMotiveCategory.homologyFunctor shiftedDegree).obj
          object) :=
  Iso.isZero_iff
    (((TraceAnalyticDerivedMotiveCategory.homologyFunctor 0).shiftIso
      shift
      degree
      shiftedDegree
      hdegree).app object)

/-- If `cut - shift < degree`, then `cut < shift + degree`. -/
theorem cut_lt_shift_add_degree_of_shifted_cut_lt
    (cut shift degree : ℤ)
    (hdegree : cut - shift < degree) :
    cut < shift + degree :=
  (add_comm degree shift) ▸
    ((sub_lt_iff_lt_add).mp hdegree)

/-- If `degree < cut - shift`, then `shift + degree < cut`. -/
theorem shift_add_degree_lt_cut_of_degree_lt_shifted_cut
    (cut shift degree : ℤ)
    (hdegree : degree < cut - shift) :
    shift + degree < cut :=
  (add_comm degree shift) ▸
    ((lt_sub_iff_add_lt).mp hdegree)

/-- The derived analytic `≤ cut` predicate is transported by shifts with the
usual cohomological cut convention. -/
theorem homologicalLE_shift
    (cut shift : ℤ)
    (object : TraceAnalyticDerivedMotiveCategory)
    (hobject :
      TraceAnalyticDerivedMotiveCategory.HomologicalLE cut object) :
    TraceAnalyticDerivedMotiveCategory.HomologicalLE
      (cut - shift)
      (object⟦shift⟧) :=
  fun degree hdegree =>
    (TraceAnalyticDerivedMotiveCategory
      .homologyFunctor_shift_obj_isZero_iff
        shift
        degree
        (shift + degree)
        rfl
        object).mpr
      (hobject
        (shift + degree)
        (TraceAnalyticDerivedMotiveCategory
          .cut_lt_shift_add_degree_of_shifted_cut_lt
            cut
            shift
            degree
            hdegree))

/-- The derived analytic `≥ cut` predicate is transported by shifts with the
usual cohomological cut convention. -/
theorem homologicalGE_shift
    (cut shift : ℤ)
    (object : TraceAnalyticDerivedMotiveCategory)
    (hobject :
      TraceAnalyticDerivedMotiveCategory.HomologicalGE cut object) :
    TraceAnalyticDerivedMotiveCategory.HomologicalGE
      (cut - shift)
      (object⟦shift⟧) :=
  fun degree hdegree =>
    (TraceAnalyticDerivedMotiveCategory
      .homologyFunctor_shift_obj_isZero_iff
        shift
        degree
        (shift + degree)
        rfl
        object).mpr
      (hobject
        (shift + degree)
        (TraceAnalyticDerivedMotiveCategory
          .shift_add_degree_lt_cut_of_degree_lt_shifted_cut
            cut
            shift
            degree
            hdegree))

end TraceAnalyticDerivedMotiveCategory

end AnalyticMotives
end LFunctions
end Boundary
