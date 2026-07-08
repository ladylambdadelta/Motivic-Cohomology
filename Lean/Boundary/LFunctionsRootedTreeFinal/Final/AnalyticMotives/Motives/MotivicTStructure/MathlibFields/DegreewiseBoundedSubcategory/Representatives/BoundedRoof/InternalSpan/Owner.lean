import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.Representatives.BoundedRoof.Projections.Owner

/-!
# Internal bounded roof spans

This file packages the source representative, target representative, and roof
vertex of a representative Verdier fraction as objects of the degreewise
bounded stable source.  The numerator and denominator are then honest morphisms
inside that full subcategory.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- A degreewise-bounded morphism factors, after conjugating by concrete
representative isomorphisms, through an internal bounded roof span. -/
theorem exists_internalRepresentativeBoundedRoofSpan
    {source target :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    (morphism : source ⟶ target) :
    ∃ (sourceBound : Nat),
      ∃ (sourceComplex : TraceAnalyticAdditiveCochainComplex),
        ∃ (targetBound : Nat),
          ∃ (targetComplex : TraceAnalyticAdditiveCochainComplex),
            ∃ (sourceRepresentative :
              TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable),
              ∃ (targetRepresentative :
                TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable),
                ∃ (roof :
                  TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable),
                  ∃ (sourceIso :
                    sourceRepresentative.object ≅ source.object),
                    ∃ (targetIso :
                      targetRepresentative.object ≅ target.object),
                      ∃ (denominator :
                        targetRepresentative ⟶ roof),
                        ∃ (numerator :
                          sourceRepresentative ⟶ roof),
                          (sourceIso.hom ≫ morphism ≫ targetIso.inv) ≫
                              denominator =
                            numerator :=
  Exists.elim
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .exists_representativeBoundedRoof_stableMaps morphism)
    (fun sourceBound sourceData =>
      Exists.elim
        sourceData
        (fun sourceComplex sourceBoundedData =>
          Exists.elim
            sourceBoundedData
            (fun sourceBounded sourceIsoData =>
              Exists.elim
                sourceIsoData
                (fun sourceIso targetBoundData =>
                  Exists.elim
                    targetBoundData
                    (fun targetBound targetData =>
                      Exists.elim
                        targetData
                        (fun targetComplex targetBoundedData =>
                          Exists.elim
                            targetBoundedData
                            (fun targetBounded targetIsoData =>
                              Exists.elim
                                targetIsoData
                                (fun targetIso roofData =>
                                  Exists.elim
                                    roofData
                                    (fun roof denominatorData =>
                                      Exists.elim
                                        denominatorData
                                        (fun stableDenominator
                                          numeratorData =>
                                          Exists.elim
                                            numeratorData
                                            (fun stableNumerator
                                              stableEquation =>
                                              let sourceRepresentative :
                                                  TraceAnalyticDMgmComparisonSource
                                                    .DegreewiseBoundedStable where
                                                obj :=
                                                  TraceAnalyticDMgmComparisonSource
                                                    .objectOf
                                                      (TraceAnalyticAdditiveHomotopyCategory
                                                        .objectOf
                                                        sourceComplex)
                                                property :=
                                                  CategoryTheory.le_isoClosure
                                                    TraceAnalyticDMgmComparisonSource
                                                      .degreewiseIsoClosureBoundedStableRepresentative
                                                    (TraceAnalyticDMgmComparisonSource
                                                      .objectOf
                                                        (TraceAnalyticAdditiveHomotopyCategory
                                                          .objectOf
                                                          sourceComplex))
                                                    (Exists.intro
                                                      sourceBound
                                                      (Exists.intro
                                                        sourceComplex
                                                        (And.intro
                                                          sourceBounded
                                                          rfl)))
                                              let targetRepresentative :
                                                  TraceAnalyticDMgmComparisonSource
                                                    .DegreewiseBoundedStable where
                                                obj :=
                                                  TraceAnalyticDMgmComparisonSource
                                                    .objectOf
                                                      (TraceAnalyticAdditiveHomotopyCategory
                                                        .objectOf
                                                        targetComplex)
                                                property :=
                                                  CategoryTheory.le_isoClosure
                                                    TraceAnalyticDMgmComparisonSource
                                                      .degreewiseIsoClosureBoundedStableRepresentative
                                                    (TraceAnalyticDMgmComparisonSource
                                                      .objectOf
                                                        (TraceAnalyticAdditiveHomotopyCategory
                                                          .objectOf
                                                          targetComplex))
                                                    (Exists.intro
                                                      targetBound
                                                      (Exists.intro
                                                        targetComplex
                                                        (And.intro
                                                          targetBounded
                                                          rfl)))
                                              Exists.intro
                                                sourceBound
                                                (Exists.intro
                                                  sourceComplex
                                                  (Exists.intro
                                                    targetBound
                                                    (Exists.intro
                                                      targetComplex
                                                      (Exists.intro
                                                        sourceRepresentative
                                                        (Exists.intro
                                                          targetRepresentative
                                                          (Exists.intro
                                                            roof
                                                            (Exists.intro
                                                              sourceIso
                                                              (Exists.intro
                                                                targetIso
                                                                (Exists.intro
                                                                  stableDenominator
                                                                  (Exists.intro
                                                                    stableNumerator
                                                                    stableEquation))))))))))))))))))))

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
