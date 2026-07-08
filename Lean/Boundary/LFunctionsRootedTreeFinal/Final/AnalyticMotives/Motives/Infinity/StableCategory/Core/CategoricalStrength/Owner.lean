import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.Construction.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Certificate.Global.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Certificate.Global.ShortComplex.PerMorphism.Certificate.Owner

/-!
# Categorical-strength stable infinity package

This file states the stable-infinity category of analytic motives at the
owner level, not as a downstream comparison surface.  The theorem below
combines the actual quasicategory/localization data, pointed shifted homotopy
category, suspension-loop equivalence, triangulated structure, bicartesian
fiber/cofiber calculus, Hom-exactness tests, and finite biproduct exactness.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The analytic motive owner object is a stable infinity category at
categorical strength: it is the localized analytic motive quasicategory, its
homotopy category is pointed and shifted, suspension and loop are inverse by
the unit shift equivalence, it is triangulated, every morphism has compatible
cofiber/fiber triangles, distinguished triangles are Hom-exact on both sides,
and finite biproduct/product triangles pass the same Hom-exactness tests. -/
theorem traceAnalyticStableInfinityCategory_categorical_strength :
    Quasicategory TraceAnalyticStableMotiveQuasicategory ∧
      TraceAnalyticStableMotiveQuasicategory.quotientFunctor.IsLocalization
        TraceAnalyticStableMotiveQuasicategory.invertedMorphisms ∧
        HasZeroObject StableInfinityOwner.PresentedCategory ∧
          HasShift StableInfinityOwner.PresentedCategory ℤ ∧
            traceAnalyticStableInfinityCategory.suspension =
              shiftFunctor StableInfinityOwner.PresentedCategory (1 : ℤ) ∧
              traceAnalyticStableInfinityCategory.loop =
                shiftFunctor StableInfinityOwner.PresentedCategory (-1 : ℤ) ∧
                traceAnalyticStableInfinityCategory
                    .suspensionLoopEquivalence =
                  shiftEquiv StableInfinityOwner.PresentedCategory
                    (1 : ℤ) ∧
                  IsTriangulated StableInfinityOwner.PresentedCategory ∧
                    traceAnalyticStableInfinityCategory_global_stability_certificate ∧
                      (∀ {source target :
                          StableInfinityOwner.PresentedCategory}
                        (morphism : source ⟶ target)
                        (leftProbe :
                          StableInfinityOwner.PresentedCategoryᵒᵖ)
                        (rightProbe :
                          StableInfinityOwner.PresentedCategory),
                        traceAnalyticStableInfinityCategory_global_perMorphism_shortComplex_certificate
                          morphism
                          leftProbe
                          rightProbe) ∧
                        (∀ (left right :
                            StableInfinityOwner.PresentedCategory)
                          (leftProbe :
                            StableInfinityOwner.PresentedCategoryᵒᵖ)
                          (rightProbe :
                            StableInfinityOwner.PresentedCategory),
                          ((traceAnalyticStableInfinityCategory
                            .binaryBiproductShortComplex left right).map
                              (preadditiveCoyoneda.obj leftProbe)).Exact ∧
                            ((traceAnalyticStableInfinityCategory
                              .binaryBiproductShortComplex left right).op.map
                                (preadditiveYoneda.obj rightProbe)).Exact ∧
                              ((traceAnalyticStableInfinityCategory
                                .binaryProductShortComplex left right).map
                                  (preadditiveCoyoneda.obj leftProbe)).Exact ∧
                                ((traceAnalyticStableInfinityCategory
                                  .binaryProductShortComplex left right).op.map
                                    (preadditiveYoneda.obj rightProbe)).Exact) :=
  And.intro
    traceAnalyticStableInfinityCategory.quasicategory
    (And.intro
      traceAnalyticStableInfinityCategory.localization
      (And.intro
        traceAnalyticStableInfinityCategory.zeroObject
        (And.intro
          traceAnalyticStableInfinityCategory.shift
          (And.intro
            traceAnalyticStableInfinityCategory.suspension_eq_shift
            (And.intro
              traceAnalyticStableInfinityCategory.loop_eq_shift
              (And.intro
                traceAnalyticStableInfinityCategory
                  .suspensionLoopEquivalence_eq_shiftEquiv
                (And.intro
                  traceAnalyticStableInfinityCategory.triangulated
                  (And.intro
                    traceAnalyticStableInfinityCategory_global_stability_certificate
                    (And.intro
                      (fun morphism leftProbe rightProbe =>
                        traceAnalyticStableInfinityCategory_global_perMorphism_shortComplex_certificate
                          morphism
                          leftProbe
                          rightProbe)
                      (fun left right leftProbe rightProbe =>
                        And.intro
                          (traceAnalyticStableInfinityCategory
                            .binaryBiproductCoyonedaShortComplex_exact
                              left
                              right
                              leftProbe)
                          (And.intro
                            (traceAnalyticStableInfinityCategory
                              .binaryBiproductYonedaShortComplex_exact
                                left
                                right
                                rightProbe)
                            (And.intro
                              (traceAnalyticStableInfinityCategory
                                .binaryProductCoyonedaShortComplex_exact
                                  left
                                  right
                                  leftProbe)
                              (traceAnalyticStableInfinityCategory
                                .binaryProductYonedaShortComplex_exact
                                  left
                                  right
                                  rightProbe)))))))))))

end AnalyticMotives
end LFunctions
end Boundary
