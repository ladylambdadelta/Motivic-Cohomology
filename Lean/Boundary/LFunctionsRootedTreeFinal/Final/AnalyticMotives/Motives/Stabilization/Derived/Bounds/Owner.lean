import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.Homology.Owner

/-!
# Homological bounds for derived analytic motives

This file defines the concrete homology-vanishing predicates that will form
the aisles and coaisles of the analytic derived t-structure.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDerivedMotiveCategory

/-- A derived analytic motive is homologically `≤ cut` when all homology above
`cut` vanishes. -/
def HomologicalLE
    (cut : ℤ)
    (object : TraceAnalyticDerivedMotiveCategory) :
    Prop :=
  ∀ degree : ℤ,
    cut < degree →
      IsZero
        ((TraceAnalyticDerivedMotiveCategory.homologyFunctor degree).obj
          object)

/-- A derived analytic motive is homologically `≥ cut` when all homology below
`cut` vanishes. -/
def HomologicalGE
    (cut : ℤ)
    (object : TraceAnalyticDerivedMotiveCategory) :
    Prop :=
  ∀ degree : ℤ,
    degree < cut →
      IsZero
        ((TraceAnalyticDerivedMotiveCategory.homologyFunctor degree).obj
          object)

/-- Membership in the derived analytic `≤ cut` predicate for a represented
cochain complex is equivalent to exactness above `cut` in the underlying
complex. -/
theorem homologicalLE_objectOf_iff_exactAt
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex) :
    TraceAnalyticDerivedMotiveCategory.HomologicalLE
        cut
        (TraceAnalyticDerivedMotiveCategory.objectOf complex) ↔
      ∀ degree : ℤ,
        cut < degree →
          complex.ExactAt degree :=
  ⟨fun h degree hcut =>
      (TraceAnalyticDerivedMotiveCategory
        .homologyFunctor_objectOf_isZero_iff_exactAt
          complex
          degree).mp
        (h degree hcut),
    fun h degree hcut =>
      (TraceAnalyticDerivedMotiveCategory
        .homologyFunctor_objectOf_isZero_iff_exactAt
          complex
          degree).mpr
        (h degree hcut)⟩

/-- Membership in the derived analytic `≥ cut` predicate for a represented
cochain complex is equivalent to exactness below `cut` in the underlying
complex. -/
theorem homologicalGE_objectOf_iff_exactAt
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex) :
    TraceAnalyticDerivedMotiveCategory.HomologicalGE
        cut
        (TraceAnalyticDerivedMotiveCategory.objectOf complex) ↔
      ∀ degree : ℤ,
        degree < cut →
          complex.ExactAt degree :=
  ⟨fun h degree hcut =>
      (TraceAnalyticDerivedMotiveCategory
        .homologyFunctor_objectOf_isZero_iff_exactAt
          complex
          degree).mp
        (h degree hcut),
    fun h degree hcut =>
      (TraceAnalyticDerivedMotiveCategory
        .homologyFunctor_objectOf_isZero_iff_exactAt
          complex
          degree).mpr
        (h degree hcut)⟩

/-- A represented complex with exactness above the cut is in the derived
analytic `≤ cut` predicate. -/
theorem homologicalLE_objectOf_of_exactAt
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (hexact :
      ∀ degree : ℤ,
        cut < degree →
          complex.ExactAt degree) :
    TraceAnalyticDerivedMotiveCategory.HomologicalLE
      cut
      (TraceAnalyticDerivedMotiveCategory.objectOf complex) :=
  (TraceAnalyticDerivedMotiveCategory
    .homologicalLE_objectOf_iff_exactAt cut complex).mpr
    hexact

/-- A represented complex with exactness below the cut is in the derived
analytic `≥ cut` predicate. -/
theorem homologicalGE_objectOf_of_exactAt
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (hexact :
      ∀ degree : ℤ,
        degree < cut →
          complex.ExactAt degree) :
    TraceAnalyticDerivedMotiveCategory.HomologicalGE
      cut
      (TraceAnalyticDerivedMotiveCategory.objectOf complex) :=
  (TraceAnalyticDerivedMotiveCategory
    .homologicalGE_objectOf_iff_exactAt cut complex).mpr
    hexact

end TraceAnalyticDerivedMotiveCategory

end AnalyticMotives
end LFunctions
end Boundary
