import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.BoundedSubcategory.Shift.Functor.Owner

/-!
# Additivity isomorphisms for bounded stable shift functors

The bounded stable shift functors are the ambient analytic comparison-source
shift functors restricted to the bounded full subcategory.  This file packages
the ambient add-shift isomorphism inside the bounded full subcategory and
records its naturality.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource
namespace BoundedStable

/-- The add-shift isomorphism for a bounded stable source object. -/
def shiftFunctorAddIso
    (first second : ℤ)
    (object : TraceAnalyticDMgmComparisonSource.BoundedStable) :
    (TraceAnalyticDMgmComparisonSource.BoundedStable
      .shiftFunctor (first + second)).obj object ≅
      ((TraceAnalyticDMgmComparisonSource.BoundedStable.shiftFunctor first ⋙
        TraceAnalyticDMgmComparisonSource.BoundedStable.shiftFunctor second)
          .obj object) where
  hom :=
    ((shiftFunctorAdd TraceAnalyticDMgmComparisonSource first second).app
      object.object).hom
  inv :=
    ((shiftFunctorAdd TraceAnalyticDMgmComparisonSource first second).app
      object.object).inv
  hom_inv_id :=
    ((shiftFunctorAdd TraceAnalyticDMgmComparisonSource first second).app
      object.object).hom_inv_id
  inv_hom_id :=
    ((shiftFunctorAdd TraceAnalyticDMgmComparisonSource first second).app
      object.object).inv_hom_id

/-- The bounded add-shift isomorphism has the ambient add-shift hom. -/
theorem shiftFunctorAddIso_hom
    (first second : ℤ)
    (object : TraceAnalyticDMgmComparisonSource.BoundedStable) :
    (TraceAnalyticDMgmComparisonSource.BoundedStable
      .shiftFunctorAddIso first second object).hom =
      ((shiftFunctorAdd TraceAnalyticDMgmComparisonSource first second).app
        object.object).hom :=
  rfl

/-- The bounded add-shift isomorphism has the ambient add-shift inverse. -/
theorem shiftFunctorAddIso_inv
    (first second : ℤ)
    (object : TraceAnalyticDMgmComparisonSource.BoundedStable) :
    (TraceAnalyticDMgmComparisonSource.BoundedStable
      .shiftFunctorAddIso first second object).inv =
      ((shiftFunctorAdd TraceAnalyticDMgmComparisonSource first second).app
        object.object).inv :=
  rfl

/-- Naturality of the bounded add-shift isomorphism. -/
theorem shiftFunctorAddIso_naturality
    (first second : ℤ)
    {source target : TraceAnalyticDMgmComparisonSource.BoundedStable}
    (hom : source ⟶ target) :
    (TraceAnalyticDMgmComparisonSource.BoundedStable
        .shiftFunctor (first + second)).map hom ≫
      (TraceAnalyticDMgmComparisonSource.BoundedStable
        .shiftFunctorAddIso first second target).hom =
    (TraceAnalyticDMgmComparisonSource.BoundedStable
        .shiftFunctorAddIso first second source).hom ≫
      ((TraceAnalyticDMgmComparisonSource.BoundedStable.shiftFunctor first ⋙
        TraceAnalyticDMgmComparisonSource.BoundedStable.shiftFunctor second)
          .map hom) :=
  ((shiftFunctorAdd TraceAnalyticDMgmComparisonSource first second).hom
    .naturality hom)

/-- The bounded add-shift natural isomorphism. -/
def shiftFunctorAddNatIso
    (first second : ℤ) :
    TraceAnalyticDMgmComparisonSource.BoundedStable
        .shiftFunctor (first + second) ≅
      TraceAnalyticDMgmComparisonSource.BoundedStable.shiftFunctor first ⋙
        TraceAnalyticDMgmComparisonSource.BoundedStable.shiftFunctor second :=
  NatIso.ofComponents
    (fun object =>
      TraceAnalyticDMgmComparisonSource.BoundedStable
        .shiftFunctorAddIso first second object)
    (fun hom =>
      TraceAnalyticDMgmComparisonSource.BoundedStable
        .shiftFunctorAddIso_naturality first second hom)

/-- The bounded add-shift natural isomorphism has the packaged component. -/
theorem shiftFunctorAddNatIso_app
    (first second : ℤ)
    (object : TraceAnalyticDMgmComparisonSource.BoundedStable) :
    (TraceAnalyticDMgmComparisonSource.BoundedStable
      .shiftFunctorAddNatIso first second).app object =
      TraceAnalyticDMgmComparisonSource.BoundedStable
        .shiftFunctorAddIso first second object :=
  NatIso.ofComponents.app
    (fun object =>
      TraceAnalyticDMgmComparisonSource.BoundedStable
        .shiftFunctorAddIso first second object)
    (fun hom =>
      TraceAnalyticDMgmComparisonSource.BoundedStable
        .shiftFunctorAddIso_naturality first second hom)
    object

/-- The add-shift natural-isomorphism hom component is the bounded add-shift hom. -/
theorem shiftFunctorAddNatIso_hom_app
    (first second : ℤ)
    (object : TraceAnalyticDMgmComparisonSource.BoundedStable) :
    (TraceAnalyticDMgmComparisonSource.BoundedStable
      .shiftFunctorAddNatIso first second).hom.app object =
      (TraceAnalyticDMgmComparisonSource.BoundedStable
        .shiftFunctorAddIso first second object).hom :=
  rfl

/-- The add-shift natural-isomorphism inverse component is the bounded add-shift inverse. -/
theorem shiftFunctorAddNatIso_inv_app
    (first second : ℤ)
    (object : TraceAnalyticDMgmComparisonSource.BoundedStable) :
    (TraceAnalyticDMgmComparisonSource.BoundedStable
      .shiftFunctorAddNatIso first second).inv.app object =
      (TraceAnalyticDMgmComparisonSource.BoundedStable
        .shiftFunctorAddIso first second object).inv :=
  rfl

end BoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
