import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.HomotopyCategory.Owner

/-!
# Projections from the stable-infinity homotopy-category identification

This file exposes stable projection names for the concrete fact that the
homotopy category of the analytic stable-infinity model is the existing
Verdier-localized stable analytic motive category.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticStableInfinityCategory

/-- The homotopy category field is the stable analytic motive category. -/
theorem homotopyCategory_presentedCategory_eq :
    TraceAnalyticStableInfinityCategory.HomotopyCategory =
      StableInfinityOwner.PresentedCategory :=
  rfl

/-- The homotopy category field is the Verdier quotient category. -/
theorem homotopyCategory_stableVerdier_eq :
    TraceAnalyticStableInfinityCategory.HomotopyCategory =
      TraceAnalyticStableMotiveCategory :=
  TraceAnalyticStableInfinityCategory
    .homotopyCategory_eq_stableMotiveCategory

/-- The quasicategory model is the nerve of the homotopy category. -/
theorem quasicategory_eq_nerve_homotopyCategory :
    TraceAnalyticStableMotiveQuasicategory =
      CategoryTheory.nerve
        TraceAnalyticStableInfinityCategory.HomotopyCategory :=
  TraceAnalyticStableInfinityCategory
    .presentedQuasicategory_eq_nerve_homotopyCategory

/-- The homotopy-category quotient functor is the stable Verdier quotient
functor. -/
theorem homotopyQuotientFunctor_stableVerdier_eq :
    TraceAnalyticStableInfinityCategory.homotopyQuotientFunctor =
      TraceAnalyticStableMotiveCategory.quotientFunctor :=
  TraceAnalyticStableInfinityCategory.homotopyQuotientFunctor_eq_stable

/-- The homotopy-category localization structure is the stable-presentation
localization structure. -/
theorem homotopyCategoryLocalization_presented_eq :
    TraceAnalyticStableInfinityCategory.homotopyCategoryLocalization =
      TraceAnalyticStableMotiveQuasicategory.isLocalization :=
  TraceAnalyticStableInfinityCategory.homotopyCategoryLocalization_eq_presented

/-- The homotopy-category shift structure is the stable Verdier shift
structure. -/
theorem homotopyCategoryShift_stableVerdier_eq :
    TraceAnalyticStableInfinityCategory.homotopyCategoryShift =
      TraceAnalyticStableMotiveCategory.hasShiftStructure :=
  TraceAnalyticStableInfinityCategory.homotopyCategoryShift_eq_stable

/-- The homotopy-category pretriangulated structure is the stable Verdier
pretriangulated structure. -/
theorem homotopyCategoryPretriangulated_stableVerdier_eq :
    TraceAnalyticStableInfinityCategory.homotopyCategoryPretriangulated =
      TraceAnalyticStableMotiveCategory.pretriangulatedStructure :=
  TraceAnalyticStableInfinityCategory
    .homotopyCategoryPretriangulated_eq_stable

/-- The homotopy-category triangulated structure is the stable Verdier
triangulated structure. -/
theorem homotopyCategoryTriangulated_stableVerdier_eq :
    TraceAnalyticStableInfinityCategory.homotopyCategoryTriangulated =
      TraceAnalyticStableMotiveCategory.triangulatedStructure :=
  TraceAnalyticStableInfinityCategory
    .homotopyCategoryTriangulated_eq_stable

/-- The homotopy-category distinguished triangles are the stable Verdier
distinguished triangles. -/
theorem homotopyCategoryDistinguishedTriangles_stableVerdier_eq :
    TraceAnalyticStableInfinityCategory
        .homotopyCategoryDistinguishedTriangles =
      TraceAnalyticStableMotiveCategory.distinguishedTriangles :=
  TraceAnalyticStableInfinityCategory
    .homotopyCategoryDistinguishedTriangles_eq_stable

end TraceAnalyticStableInfinityCategory

end AnalyticMotives
end LFunctions
end Boundary
