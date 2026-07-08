import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Fiber.Comparison.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.ShortComplex.YonedaExact.CofiberRotations.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.ShortComplex.YonedaExact.Fiber.Owner

/-!
# Comparison of fiber and inverse-rotated cofiber Yoneda exactness

This owner file records that the exactness witnesses for the semantic fiber
short complex and the inverse-rotated chosen cofiber short complex agree.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Covariant preadditive Yoneda exactness for the chosen fiber short complex
agrees with the inverse-rotated cofiber exactness witness. -/
theorem
    TraceAnalyticStableMotiveQuasicategory.fiberCoyonedaShortComplex_exact_eq_invRotated
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (probe : StableInfinityOwner.PresentedCategoryᵒᵖ) :
    TraceAnalyticStableMotiveQuasicategory
        .fiberCoyonedaShortComplex_exact morphism probe =
      TraceAnalyticStableMotiveQuasicategory
        .invRotatedCofiberCoyonedaShortComplex_exact morphism probe :=
  Subsingleton.elim
    (TraceAnalyticStableMotiveQuasicategory
      .fiberCoyonedaShortComplex_exact morphism probe)
    (TraceAnalyticStableMotiveQuasicategory
      .invRotatedCofiberCoyonedaShortComplex_exact morphism probe)

/-- Contravariant preadditive Yoneda exactness for the chosen fiber short
complex agrees with the inverse-rotated cofiber exactness witness. -/
theorem
    TraceAnalyticStableMotiveQuasicategory.fiberYonedaShortComplex_exact_eq_invRotated
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (probe : StableInfinityOwner.PresentedCategory) :
    TraceAnalyticStableMotiveQuasicategory
        .fiberYonedaShortComplex_exact morphism probe =
      TraceAnalyticStableMotiveQuasicategory
        .invRotatedCofiberYonedaShortComplex_exact morphism probe :=
  Subsingleton.elim
    (TraceAnalyticStableMotiveQuasicategory
      .fiberYonedaShortComplex_exact morphism probe)
    (TraceAnalyticStableMotiveQuasicategory
      .invRotatedCofiberYonedaShortComplex_exact morphism probe)

end AnalyticMotives
end LFunctions
end Boundary
