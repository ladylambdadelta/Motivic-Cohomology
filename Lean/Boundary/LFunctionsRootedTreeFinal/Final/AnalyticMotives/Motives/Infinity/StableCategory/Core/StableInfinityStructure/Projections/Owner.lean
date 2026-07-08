import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.StableInfinityStructure.Owner

/-!
# Projections from the stable-infinity structure certificate

This file exposes the owner-level components of the concrete analytic
stable-infinity structure certificate.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Projection to the quasicategory structure. -/
theorem traceAnalyticStableInfinityCategory_actual_quasicategory :
    Quasicategory TraceAnalyticStableMotiveQuasicategory :=
  traceAnalyticStableInfinityCategory_actual_stable_infinity_structure.left

/-- Projection to the Verdier localization structure. -/
theorem traceAnalyticStableInfinityCategory_actual_localization :
    TraceAnalyticStableMotiveQuasicategory.quotientFunctor.IsLocalization
      TraceAnalyticStableMotiveQuasicategory.invertedMorphisms :=
  traceAnalyticStableInfinityCategory_actual_stable_infinity_structure
    .right
    .left

/-- Projection to pointedness of the homotopy category. -/
theorem traceAnalyticStableInfinityCategory_actual_pointed :
    HasZeroObject
      TraceAnalyticStableInfinityCategory.HomotopyCategory :=
  traceAnalyticStableInfinityCategory_actual_stable_infinity_structure
    .right
    .right
    .left

/-- Projection to integer shifts on the homotopy category. -/
theorem traceAnalyticStableInfinityCategory_actual_shift :
    HasShift
      TraceAnalyticStableInfinityCategory.HomotopyCategory
      ℤ :=
  traceAnalyticStableInfinityCategory_actual_stable_infinity_structure
    .right
    .right
    .right
    .left

/-- Projection to the suspension-loop equivalence identification. -/
theorem traceAnalyticStableInfinityCategory_actual_suspensionLoopEquivalence :
    traceAnalyticStableInfinityCategory.suspensionLoopEquivalence =
      shiftEquiv
        TraceAnalyticStableInfinityCategory.HomotopyCategory
        (1 : ℤ) :=
  traceAnalyticStableInfinityCategory_actual_stable_infinity_structure
    .right
    .right
    .right
    .right
    .left

/-- Projection to the triangulated homotopy category. -/
theorem traceAnalyticStableInfinityCategory_actual_triangulated :
    IsTriangulated
      TraceAnalyticStableInfinityCategory.HomotopyCategory :=
  traceAnalyticStableInfinityCategory_actual_stable_infinity_structure
    .right
    .right
    .right
    .right
    .right
    .left

/-- Projection to the global stability certificate. -/
theorem traceAnalyticStableInfinityCategory_actual_global_stability :
    traceAnalyticStableInfinityCategory_global_stability_certificate :=
  traceAnalyticStableInfinityCategory_actual_stable_infinity_structure
    .right
    .right
    .right
    .right
    .right
    .right
    .left

/-- Projection to the certified per-morphism short-complex calculus. -/
theorem traceAnalyticStableInfinityCategory_actual_shortComplex_certificate
    {source target :
      TraceAnalyticStableInfinityCategory.HomotopyCategory}
    (morphism : source ⟶ target)
    (leftProbe :
      TraceAnalyticStableInfinityCategory.HomotopyCategoryᵒᵖ)
    (rightProbe :
      TraceAnalyticStableInfinityCategory.HomotopyCategory) :
    traceAnalyticStableInfinityCategory_global_perMorphism_shortComplex_certificate
      morphism
      leftProbe
      rightProbe :=
  traceAnalyticStableInfinityCategory_actual_stable_infinity_structure
    .right
    .right
    .right
    .right
    .right
    .right
    .right
    morphism
    leftProbe
    rightProbe

end AnalyticMotives
end LFunctions
end Boundary
