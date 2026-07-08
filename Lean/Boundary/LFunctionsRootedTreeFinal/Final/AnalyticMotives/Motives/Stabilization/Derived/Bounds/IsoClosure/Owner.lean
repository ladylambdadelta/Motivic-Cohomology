import Mathlib.CategoryTheory.ClosedUnderIsomorphisms
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.Bounds.Owner

/-!
# Isomorphism closure of derived analytic homological bounds

This file proves that the concrete derived homological `≤ cut` and `≥ cut`
predicates are closed under isomorphisms in the derived analytic motive
category.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDerivedMotiveCategory

/-- The derived analytic `≤ cut` homological predicate transports along an
isomorphism. -/
theorem homologicalLE_of_iso
    (cut : ℤ)
    {source target : TraceAnalyticDerivedMotiveCategory}
    (iso : source ≅ target)
    (hsource :
      TraceAnalyticDerivedMotiveCategory.HomologicalLE cut source) :
    TraceAnalyticDerivedMotiveCategory.HomologicalLE cut target :=
  fun degree hdegree =>
    (Iso.isZero_iff
      ((TraceAnalyticDerivedMotiveCategory.homologyFunctor degree).mapIso
        iso)).mp
      (hsource degree hdegree)

/-- The derived analytic `≥ cut` homological predicate transports along an
isomorphism. -/
theorem homologicalGE_of_iso
    (cut : ℤ)
    {source target : TraceAnalyticDerivedMotiveCategory}
    (iso : source ≅ target)
    (hsource :
      TraceAnalyticDerivedMotiveCategory.HomologicalGE cut source) :
    TraceAnalyticDerivedMotiveCategory.HomologicalGE cut target :=
  fun degree hdegree =>
    (Iso.isZero_iff
      ((TraceAnalyticDerivedMotiveCategory.homologyFunctor degree).mapIso
        iso)).mp
      (hsource degree hdegree)

/-- The derived analytic `≤ cut` homological predicate is closed under
isomorphisms. -/
def homologicalLE_closedUnderIsomorphisms
    (cut : ℤ) :
    CategoryTheory.ClosedUnderIsomorphisms
      (TraceAnalyticDerivedMotiveCategory.HomologicalLE cut) where
  of_iso := fun iso hsource =>
    TraceAnalyticDerivedMotiveCategory.homologicalLE_of_iso
      cut
      iso
      hsource

/-- The derived analytic `≥ cut` homological predicate is closed under
isomorphisms. -/
def homologicalGE_closedUnderIsomorphisms
    (cut : ℤ) :
    CategoryTheory.ClosedUnderIsomorphisms
      (TraceAnalyticDerivedMotiveCategory.HomologicalGE cut) where
  of_iso := fun iso hsource =>
    TraceAnalyticDerivedMotiveCategory.homologicalGE_of_iso
      cut
      iso
      hsource

/-- Membership in the `≤ cut` predicate is invariant under isomorphism. -/
theorem homologicalLE_iff_of_iso
    (cut : ℤ)
    {source target : TraceAnalyticDerivedMotiveCategory}
    (iso : source ≅ target) :
    TraceAnalyticDerivedMotiveCategory.HomologicalLE cut source ↔
      TraceAnalyticDerivedMotiveCategory.HomologicalLE cut target :=
  ⟨TraceAnalyticDerivedMotiveCategory.homologicalLE_of_iso cut iso,
    TraceAnalyticDerivedMotiveCategory.homologicalLE_of_iso cut iso.symm⟩

/-- Membership in the `≥ cut` predicate is invariant under isomorphism. -/
theorem homologicalGE_iff_of_iso
    (cut : ℤ)
    {source target : TraceAnalyticDerivedMotiveCategory}
    (iso : source ≅ target) :
    TraceAnalyticDerivedMotiveCategory.HomologicalGE cut source ↔
      TraceAnalyticDerivedMotiveCategory.HomologicalGE cut target :=
  ⟨TraceAnalyticDerivedMotiveCategory.homologicalGE_of_iso cut iso,
    TraceAnalyticDerivedMotiveCategory.homologicalGE_of_iso cut iso.symm⟩

end TraceAnalyticDerivedMotiveCategory

end AnalyticMotives
end LFunctions
end Boundary
