import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.BoundedSubcategory.Shift.Functor.Zero.Owner

/-!
# Naturality of bounded zero-shift isomorphisms

The bounded zero-shift isomorphism is the ambient zero-shift isomorphism
restricted to the bounded full subcategory.  This file records its naturality
and packages it as a natural isomorphism.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource
namespace BoundedStable

/-- Naturality of the bounded zero-shift isomorphism. -/
theorem shiftFunctorZeroIso_naturality
    {source target : TraceAnalyticDMgmComparisonSource.BoundedStable}
    (hom : source ⟶ target) :
    (TraceAnalyticDMgmComparisonSource.BoundedStable.shiftFunctor 0).map
        hom ≫
      (TraceAnalyticDMgmComparisonSource.BoundedStable
        .shiftFunctorZeroIso target).hom =
    (TraceAnalyticDMgmComparisonSource.BoundedStable
        .shiftFunctorZeroIso source).hom ≫
      hom :=
  ((shiftFunctorZero TraceAnalyticDMgmComparisonSource ℤ).hom.naturality
    hom)

/-- The bounded zero-shift functor is naturally isomorphic to the identity. -/
def shiftFunctorZeroNatIso :
    TraceAnalyticDMgmComparisonSource.BoundedStable.shiftFunctor 0 ≅
      𝟭 TraceAnalyticDMgmComparisonSource.BoundedStable :=
  NatIso.ofComponents
    (fun object =>
      TraceAnalyticDMgmComparisonSource.BoundedStable
        .shiftFunctorZeroIso object)
    (fun hom =>
      TraceAnalyticDMgmComparisonSource.BoundedStable
        .shiftFunctorZeroIso_naturality hom)

/-- The bounded zero-shift natural isomorphism has the packaged component. -/
theorem shiftFunctorZeroNatIso_app
    (object : TraceAnalyticDMgmComparisonSource.BoundedStable) :
    TraceAnalyticDMgmComparisonSource.BoundedStable
      .shiftFunctorZeroNatIso.app object =
      TraceAnalyticDMgmComparisonSource.BoundedStable
        .shiftFunctorZeroIso object :=
  NatIso.ofComponents.app
    (fun object =>
      TraceAnalyticDMgmComparisonSource.BoundedStable
        .shiftFunctorZeroIso object)
    (fun hom =>
      TraceAnalyticDMgmComparisonSource.BoundedStable
        .shiftFunctorZeroIso_naturality hom)
    object

/-- The natural-isomorphism hom component is the bounded zero-shift hom. -/
theorem shiftFunctorZeroNatIso_hom_app
    (object : TraceAnalyticDMgmComparisonSource.BoundedStable) :
    TraceAnalyticDMgmComparisonSource.BoundedStable
      .shiftFunctorZeroNatIso.hom.app object =
      (TraceAnalyticDMgmComparisonSource.BoundedStable
        .shiftFunctorZeroIso object).hom :=
  rfl

/-- The natural-isomorphism inverse component is the bounded zero-shift inverse. -/
theorem shiftFunctorZeroNatIso_inv_app
    (object : TraceAnalyticDMgmComparisonSource.BoundedStable) :
    TraceAnalyticDMgmComparisonSource.BoundedStable
      .shiftFunctorZeroNatIso.inv.app object =
      (TraceAnalyticDMgmComparisonSource.BoundedStable
        .shiftFunctorZeroIso object).inv :=
  rfl

end BoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
