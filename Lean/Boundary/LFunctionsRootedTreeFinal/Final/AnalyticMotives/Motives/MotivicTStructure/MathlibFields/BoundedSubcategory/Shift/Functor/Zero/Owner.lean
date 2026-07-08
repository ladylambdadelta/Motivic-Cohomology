import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.BoundedSubcategory.Shift.Functor.Inclusion.Owner

/-!
# Zero-shift isomorphisms for bounded stable shifts

The bounded stable shift functor is the ambient shift restricted to the
bounded full subcategory.  This file packages the ambient zero-shift
isomorphism `X⟦0⟧ ≅ X` as an isomorphism inside the bounded full subcategory.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource
namespace BoundedStable

/-- The zero-shift isomorphism for a bounded stable source object. -/
def shiftFunctorZeroIso
    (object : TraceAnalyticDMgmComparisonSource.BoundedStable) :
    (TraceAnalyticDMgmComparisonSource.BoundedStable.shiftFunctor 0).obj
        object ≅
      object where
  hom :=
    ((shiftFunctorZero TraceAnalyticDMgmComparisonSource ℤ).app
      object.object).hom
  inv :=
    ((shiftFunctorZero TraceAnalyticDMgmComparisonSource ℤ).app
      object.object).inv
  hom_inv_id :=
    ((shiftFunctorZero TraceAnalyticDMgmComparisonSource ℤ).app
      object.object).hom_inv_id
  inv_hom_id :=
    ((shiftFunctorZero TraceAnalyticDMgmComparisonSource ℤ).app
      object.object).inv_hom_id

/-- The bounded zero-shift isomorphism has the ambient zero-shift hom. -/
theorem shiftFunctorZeroIso_hom
    (object : TraceAnalyticDMgmComparisonSource.BoundedStable) :
    (TraceAnalyticDMgmComparisonSource.BoundedStable
      .shiftFunctorZeroIso object).hom =
      ((shiftFunctorZero TraceAnalyticDMgmComparisonSource ℤ).app
        object.object).hom :=
  rfl

/-- The bounded zero-shift isomorphism has the ambient zero-shift inverse. -/
theorem shiftFunctorZeroIso_inv
    (object : TraceAnalyticDMgmComparisonSource.BoundedStable) :
    (TraceAnalyticDMgmComparisonSource.BoundedStable
      .shiftFunctorZeroIso object).inv =
      ((shiftFunctorZero TraceAnalyticDMgmComparisonSource ℤ).app
        object.object).inv :=
  rfl

end BoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
