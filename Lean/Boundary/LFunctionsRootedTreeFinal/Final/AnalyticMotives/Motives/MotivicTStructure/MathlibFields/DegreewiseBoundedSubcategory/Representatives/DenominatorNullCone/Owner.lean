import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.Representatives.Owner

/-!
# Denominator null-cone representatives

This file isolates the final refinement of the degreewise-bounded
representative calculus: after representing a morphism by a left fraction, the
denominator is unpacked as the first map of a distinguished triangle whose cone
lies in the analytic stable null subcategory.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- A morphism between degreewise bounded stable objects has a representative
left fraction whose denominator is not merely named as inverted: the denominator
is the first map of a concrete distinguished triangle with null cone. -/
theorem exists_representativeDenominatorNullCone
    {source target :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    (morphism : source ⟶ target) :
    ∃ (sourceBound : Nat),
      ∃ (sourceComplex : TraceAnalyticAdditiveCochainComplex),
        ∃ (sourceBounded :
          TraceAnalyticMotiveComparison
            .sourceComplexDegreewiseIsoClosureBoundedBy
              sourceComplex
              sourceBound),
          ∃ (sourceIso :
            TraceAnalyticDMgmComparisonSource.objectOf
                (TraceAnalyticAdditiveHomotopyCategory.objectOf
                  sourceComplex) ≅
              source.object),
            ∃ (targetBound : Nat),
              ∃ (targetComplex : TraceAnalyticAdditiveCochainComplex),
                ∃ (targetBounded :
                  TraceAnalyticMotiveComparison
                    .sourceComplexDegreewiseIsoClosureBoundedBy
                      targetComplex
                      targetBound),
                  ∃ (targetIso :
                    TraceAnalyticDMgmComparisonSource.objectOf
                        (TraceAnalyticAdditiveHomotopyCategory.objectOf
                          targetComplex) ≅
                      target.object),
                    ∃ (roofVertex : TraceAnalyticAdditiveHomotopyCategory),
                      ∃ (denominator :
                        TraceAnalyticAdditiveHomotopyCategory.objectOf
                            targetComplex ⟶ roofVertex),
                        ∃ (numerator :
                          TraceAnalyticAdditiveHomotopyCategory.objectOf
                              sourceComplex ⟶ roofVertex),
                          ∃ (denominatorCone :
                            TraceAnalyticAdditiveHomotopyCategory),
                            ∃ (denominatorCoconeMap :
                              roofVertex ⟶ denominatorCone),
                              ∃ (denominatorBoundary :
                                denominatorCone ⟶
                                  (TraceAnalyticAdditiveHomotopyCategory
                                    .objectOf targetComplex)⟦(1 : ℤ)⟧),
                                ∃ (_ :
                                  Triangle.mk
                                      denominator
                                      denominatorCoconeMap
                                      denominatorBoundary ∈
                                    TraceAnalyticAdditiveHomotopyCategory
                                      .distinguishedTriangles),
                                  ∃ (_ :
                                    TraceAnalyticStableNullSubcategory.P
                                      denominatorCone),
                                    (sourceIso.hom ≫
                                          morphism ≫ targetIso.inv) ≫
                                        (TraceAnalyticDMgmComparisonSource
                                          .quotientFunctor.map
                                          denominator) =
                                      TraceAnalyticDMgmComparisonSource
                                        .quotientFunctor.map numerator :=
  Exists.elim
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .exists_representativeNumeratorDenominator morphism)
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
                                    (fun roofVertex denominatorData =>
                                      Exists.elim
                                        denominatorData
                                        (fun denominator
                                          denominatorInvertedData =>
                                          Exists.elim
                                            denominatorInvertedData
                                            (fun denominatorInverted
                                              numeratorData =>
                                              Exists.elim
                                                numeratorData
                                                (fun numerator
                                                  numeratorEquation =>
                                                  Exists.elim
                                                    denominatorInverted
                                                    (fun denominatorCone
                                                      coneMapData =>
                                                      Exists.elim
                                                        coneMapData
                                                        (fun denominatorCoconeMap
                                                          boundaryData =>
                                                          Exists.elim
                                                            boundaryData
                                                            (fun denominatorBoundary
                                                              distinguishedData =>
                                                              Exists.elim
                                                                distinguishedData
                                                                (fun distinguished
                                                                  null =>
                                                                  Exists.intro
                                                                    sourceBound
                                                                    (Exists.intro
                                                                      sourceComplex
                                                                      (Exists.intro
                                                                        sourceBounded
                                                                        (Exists.intro
                                                                          sourceIso
                                                                          (Exists.intro
                                                                            targetBound
                                                                            (Exists.intro
                                                                              targetComplex
                                                                              (Exists.intro
                                                                                targetBounded
                                                                                (Exists.intro
                                                                                  targetIso
                                                                                  (Exists.intro
                                                                                    roofVertex
                                                                                    (Exists.intro
                                                                                      denominator
                                                                                      (Exists.intro
                                                                                        numerator
                                                                                        (Exists.intro
                                                                                          denominatorCone
                                                                                          (Exists.intro
                                                                                            denominatorCoconeMap
                                                                                            (Exists.intro
                                                                                              denominatorBoundary
                                                                                              (Exists.intro
                                                                                                distinguished
                                                                                                (Exists.intro
                                                                                                  null
                                                                                                  numeratorEquation)))))))))))))))))))))))))))))))))))

/-- The denominator-null-cone representative may be chosen with the roof vertex
still packaged as a degreewise bounded stable object. -/
theorem exists_representativeBoundedRoofDenominatorNullCone
    {source target :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    (morphism : source ⟶ target) :
    ∃ (sourceBound : Nat),
      ∃ (sourceComplex : TraceAnalyticAdditiveCochainComplex),
        ∃ (sourceBounded :
          TraceAnalyticMotiveComparison
            .sourceComplexDegreewiseIsoClosureBoundedBy
              sourceComplex
              sourceBound),
          ∃ (sourceIso :
            TraceAnalyticDMgmComparisonSource.objectOf
                (TraceAnalyticAdditiveHomotopyCategory.objectOf
                  sourceComplex) ≅
              source.object),
            ∃ (targetBound : Nat),
              ∃ (targetComplex : TraceAnalyticAdditiveCochainComplex),
                ∃ (targetBounded :
                  TraceAnalyticMotiveComparison
                    .sourceComplexDegreewiseIsoClosureBoundedBy
                      targetComplex
                      targetBound),
                  ∃ (targetIso :
                    TraceAnalyticDMgmComparisonSource.objectOf
                        (TraceAnalyticAdditiveHomotopyCategory.objectOf
                          targetComplex) ≅
                      target.object),
                    ∃ (roof :
                      TraceAnalyticDMgmComparisonSource
                        .DegreewiseBoundedStable),
                      ∃ (roofVertex :
                        TraceAnalyticAdditiveHomotopyCategory),
                        ∃ (_ :
                          roof.object =
                            TraceAnalyticDMgmComparisonSource.objectOf
                              roofVertex),
                          ∃ (denominator :
                            TraceAnalyticAdditiveHomotopyCategory.objectOf
                                targetComplex ⟶ roofVertex),
                            ∃ (numerator :
                              TraceAnalyticAdditiveHomotopyCategory.objectOf
                                  sourceComplex ⟶ roofVertex),
                              ∃ (denominatorCone :
                                TraceAnalyticAdditiveHomotopyCategory),
                                ∃ (denominatorCoconeMap :
                                  roofVertex ⟶ denominatorCone),
                                  ∃ (denominatorBoundary :
                                    denominatorCone ⟶
                                      (TraceAnalyticAdditiveHomotopyCategory
                                        .objectOf targetComplex)⟦(1 : ℤ)⟧),
                                    ∃ (_ :
                                      Triangle.mk
                                          denominator
                                          denominatorCoconeMap
                                          denominatorBoundary ∈
                                        TraceAnalyticAdditiveHomotopyCategory
                                          .distinguishedTriangles),
                                      ∃ (_ :
                                        TraceAnalyticStableNullSubcategory.P
                                          denominatorCone),
                                        (sourceIso.hom ≫
                                              morphism ≫ targetIso.inv) ≫
                                            (TraceAnalyticDMgmComparisonSource
                                              .quotientFunctor.map
                                              denominator) =
                                          TraceAnalyticDMgmComparisonSource
                                            .quotientFunctor.map numerator :=
  Exists.elim
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .exists_representativeNumeratorDenominator_boundedRoof morphism)
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
                                    (fun roofVertex roofStableBoundedData =>
                                      Exists.elim
                                        roofStableBoundedData
                                        (fun roofStableBounded
                                          denominatorData =>
                                          let roof :
                                              TraceAnalyticDMgmComparisonSource
                                                .DegreewiseBoundedStable where
                                            obj :=
                                              TraceAnalyticDMgmComparisonSource
                                                .objectOf roofVertex
                                            property := roofStableBounded
                                          Exists.elim
                                            denominatorData
                                            (fun denominator
                                              denominatorInvertedData =>
                                              Exists.elim
                                                denominatorInvertedData
                                                (fun denominatorInverted
                                                  numeratorData =>
                                                  Exists.elim
                                                    numeratorData
                                                    (fun numerator
                                                      numeratorEquation =>
                                                      Exists.elim
                                                        denominatorInverted
                                                        (fun denominatorCone
                                                          coneMapData =>
                                                          Exists.elim
                                                            coneMapData
                                                            (fun denominatorCoconeMap
                                                              boundaryData =>
                                                              Exists.elim
                                                                boundaryData
                                                                (fun denominatorBoundary
                                                                  distinguishedData =>
                                                                  Exists.elim
                                                                    distinguishedData
                                                                    (fun distinguished
                                                                      null =>
                                                                      Exists.intro
                                                                        sourceBound
                                                                        (Exists.intro
                                                                          sourceComplex
                                                                          (Exists.intro
                                                                            sourceBounded
                                                                            (Exists.intro
                                                                              sourceIso
                                                                              (Exists.intro
                                                                                targetBound
                                                                                (Exists.intro
                                                                                  targetComplex
                                                                                  (Exists.intro
                                                                                    targetBounded
                                                                                    (Exists.intro
                                                                                      targetIso
                                                                                      (Exists.intro
                                                                                        roof
                                                                                        (Exists.intro
                                                                                          roofVertex
                                                                                          (Exists.intro
                                                                                            rfl
                                                                                            (Exists.intro
                                                                                              denominator
                                                                                              (Exists.intro
                                                                                                numerator
                                                                                                (Exists.intro
                                                                                                  denominatorCone
                                                                                                  (Exists.intro
                                                                                                    denominatorCoconeMap
                                                                                                    (Exists.intro
                                                                                                      denominatorBoundary
                                                                                                      (Exists.intro
                                                                                                        distinguished
                                                                                                        (Exists.intro
                                                                                                          null
                                                                                                          numeratorEquation)))))))))))))))))))))))))))))))))))))

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
