import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.BoundedSubcategory.Shift.Functor.Add.Owner

/-!
# Inclusion compatibility for bounded add-shift isomorphisms

The bounded add-shift natural isomorphism is the restriction of the ambient
add-shift natural isomorphism along the bounded full-subcategory inclusion.
This file records the component-level compatibility used by later coherence
proofs.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource
namespace BoundedStable

/-- The bounded add-shift hom component includes to the ambient add-shift
hom component. -/
theorem shiftFunctorAddIso_inclusion_hom
    (first second : ℤ)
    (object : TraceAnalyticDMgmComparisonSource.BoundedStable) :
    TraceAnalyticDMgmComparisonSource.BoundedStable.inclusion.map
      (TraceAnalyticDMgmComparisonSource.BoundedStable
        .shiftFunctorAddIso first second object).hom =
      ((shiftFunctorAdd TraceAnalyticDMgmComparisonSource first second).app
        object.object).hom :=
  rfl

/-- The bounded add-shift inverse component includes to the ambient add-shift
inverse component. -/
theorem shiftFunctorAddIso_inclusion_inv
    (first second : ℤ)
    (object : TraceAnalyticDMgmComparisonSource.BoundedStable) :
    TraceAnalyticDMgmComparisonSource.BoundedStable.inclusion.map
      (TraceAnalyticDMgmComparisonSource.BoundedStable
        .shiftFunctorAddIso first second object).inv =
      ((shiftFunctorAdd TraceAnalyticDMgmComparisonSource first second).app
        object.object).inv :=
  rfl

/-- The bounded add-shift natural-isomorphism hom component includes to the
ambient add-shift hom component. -/
theorem shiftFunctorAddNatIso_inclusion_hom_app
    (first second : ℤ)
    (object : TraceAnalyticDMgmComparisonSource.BoundedStable) :
    TraceAnalyticDMgmComparisonSource.BoundedStable.inclusion.map
      ((TraceAnalyticDMgmComparisonSource.BoundedStable
        .shiftFunctorAddNatIso first second).hom.app object) =
      ((shiftFunctorAdd TraceAnalyticDMgmComparisonSource first second).hom
        .app object.object) :=
  rfl

/-- The bounded add-shift natural-isomorphism inverse component includes to
the ambient add-shift inverse component. -/
theorem shiftFunctorAddNatIso_inclusion_inv_app
    (first second : ℤ)
    (object : TraceAnalyticDMgmComparisonSource.BoundedStable) :
    TraceAnalyticDMgmComparisonSource.BoundedStable.inclusion.map
      ((TraceAnalyticDMgmComparisonSource.BoundedStable
        .shiftFunctorAddNatIso first second).inv.app object) =
      ((shiftFunctorAdd TraceAnalyticDMgmComparisonSource first second).inv
        .app object.object) :=
  rfl

end BoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
