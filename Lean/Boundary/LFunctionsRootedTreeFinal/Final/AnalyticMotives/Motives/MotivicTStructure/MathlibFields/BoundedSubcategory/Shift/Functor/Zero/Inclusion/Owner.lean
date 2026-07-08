import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.BoundedSubcategory.Shift.Functor.Zero.Naturality.Owner

/-!
# Inclusion compatibility for bounded zero-shift isomorphisms

The bounded zero-shift natural isomorphism is the restriction of the ambient
zero-shift natural isomorphism along the bounded full-subcategory inclusion.
This file records the component-level compatibility used by later unit
coherence proofs.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource
namespace BoundedStable

/-- The bounded zero-shift hom component includes to the ambient zero-shift
hom component. -/
theorem shiftFunctorZeroIso_inclusion_hom
    (object : TraceAnalyticDMgmComparisonSource.BoundedStable) :
    TraceAnalyticDMgmComparisonSource.BoundedStable.inclusion.map
      (TraceAnalyticDMgmComparisonSource.BoundedStable
        .shiftFunctorZeroIso object).hom =
      ((shiftFunctorZero TraceAnalyticDMgmComparisonSource ℤ).app
        object.object).hom :=
  rfl

/-- The bounded zero-shift inverse component includes to the ambient
zero-shift inverse component. -/
theorem shiftFunctorZeroIso_inclusion_inv
    (object : TraceAnalyticDMgmComparisonSource.BoundedStable) :
    TraceAnalyticDMgmComparisonSource.BoundedStable.inclusion.map
      (TraceAnalyticDMgmComparisonSource.BoundedStable
        .shiftFunctorZeroIso object).inv =
      ((shiftFunctorZero TraceAnalyticDMgmComparisonSource ℤ).app
        object.object).inv :=
  rfl

/-- The bounded zero-shift natural-isomorphism hom component includes to the
ambient zero-shift hom component. -/
theorem shiftFunctorZeroNatIso_inclusion_hom_app
    (object : TraceAnalyticDMgmComparisonSource.BoundedStable) :
    TraceAnalyticDMgmComparisonSource.BoundedStable.inclusion.map
      (TraceAnalyticDMgmComparisonSource.BoundedStable
        .shiftFunctorZeroNatIso.hom.app object) =
      ((shiftFunctorZero TraceAnalyticDMgmComparisonSource ℤ).hom
        .app object.object) :=
  rfl

/-- The bounded zero-shift natural-isomorphism inverse component includes to
the ambient zero-shift inverse component. -/
theorem shiftFunctorZeroNatIso_inclusion_inv_app
    (object : TraceAnalyticDMgmComparisonSource.BoundedStable) :
    TraceAnalyticDMgmComparisonSource.BoundedStable.inclusion.map
      (TraceAnalyticDMgmComparisonSource.BoundedStable
        .shiftFunctorZeroNatIso.inv.app object) =
      ((shiftFunctorZero TraceAnalyticDMgmComparisonSource ℤ).inv
        .app object.object) :=
  rfl

end BoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
