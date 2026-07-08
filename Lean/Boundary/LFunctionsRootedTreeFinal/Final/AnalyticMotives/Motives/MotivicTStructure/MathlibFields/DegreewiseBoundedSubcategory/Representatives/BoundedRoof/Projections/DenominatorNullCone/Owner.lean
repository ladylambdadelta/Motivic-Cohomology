import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.Representatives.DenominatorNullCone.Owner

/-!
# Stable projections preserving denominator null-cone data

This file refines the bounded-roof stable-map projection by keeping the
analytic certificate that the denominator is the first map of a distinguished
triangle with null cone.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- A bounded representative roof supplies stable numerator and denominator
maps into the packaged roof object while preserving the raw distinguished
triangle and null-cone certificate for the denominator. -/
theorem exists_representativeBoundedRoof_stableMaps_denominatorNullCone
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
                      ∃ (stableDenominator :
                        TraceAnalyticDMgmComparisonSource.objectOf
                            (TraceAnalyticAdditiveHomotopyCategory.objectOf
                              targetComplex) ⟶
                          roof.object),
                        ∃ (stableNumerator :
                          TraceAnalyticDMgmComparisonSource.objectOf
                              (TraceAnalyticAdditiveHomotopyCategory.objectOf
                                sourceComplex) ⟶
                            roof.object),
                          ∃ (roofVertex :
                            TraceAnalyticAdditiveHomotopyCategory),
                            ∃ (roof_eq :
                              roof.object =
                                TraceAnalyticDMgmComparisonSource.objectOf
                                  roofVertex),
                              ∃ (denominator :
                                TraceAnalyticAdditiveHomotopyCategory.objectOf
                                    targetComplex ⟶ roofVertex),
                                ∃ (numerator :
                                  TraceAnalyticAdditiveHomotopyCategory
                                      .objectOf sourceComplex ⟶ roofVertex),
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
                                            stableDenominator =
                                                TraceAnalyticDMgmComparisonSource
                                                  .quotientFunctor.map
                                                  denominator ≫
                                              eqToHom (Eq.symm roof_eq) ∧
                                              stableNumerator =
                                                TraceAnalyticDMgmComparisonSource
                                                  .quotientFunctor.map
                                                  numerator ≫
                                              eqToHom (Eq.symm roof_eq) ∧
                                                (sourceIso.hom ≫
                                                      morphism ≫
                                                    targetIso.inv) ≫
                                                  stableDenominator =
                                                stableNumerator :=
  Exists.elim
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .exists_representativeBoundedRoofDenominatorNullCone morphism)
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
                                    (fun roof roofVertexData =>
                                      Exists.elim
                                        roofVertexData
                                        (fun roofVertex roofEqData =>
                                          Exists.elim
                                            roofEqData
                                            (fun roof_eq denominatorData =>
                                              Exists.elim
                                                denominatorData
                                                (fun denominator
                                                  numeratorData =>
                                                  Exists.elim
                                                    numeratorData
                                                    (fun numerator
                                                      coneData =>
                                                      Exists.elim
                                                        coneData
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
                                                                      nullData =>
                                                                      Exists.elim
                                                                        nullData
                                                                        (fun null
                                                                          numeratorEquation =>
                                                                          let roofTransport :
                                                                              TraceAnalyticDMgmComparisonSource
                                                                                  .objectOf
                                                                                  roofVertex ⟶
                                                                                roof.object :=
                                                                            eqToHom
                                                                              (Eq.symm roof_eq)
                                                                          let stableDenominator :
                                                                              TraceAnalyticDMgmComparisonSource
                                                                                  .objectOf
                                                                                  (TraceAnalyticAdditiveHomotopyCategory
                                                                                    .objectOf
                                                                                    targetComplex) ⟶
                                                                                roof.object :=
                                                                            TraceAnalyticDMgmComparisonSource
                                                                                .quotientFunctor.map
                                                                                denominator ≫
                                                                              roofTransport
                                                                          let stableNumerator :
                                                                              TraceAnalyticDMgmComparisonSource
                                                                                  .objectOf
                                                                                  (TraceAnalyticAdditiveHomotopyCategory
                                                                                    .objectOf
                                                                                    sourceComplex) ⟶
                                                                                roof.object :=
                                                                            TraceAnalyticDMgmComparisonSource
                                                                                .quotientFunctor.map
                                                                                numerator ≫
                                                                              roofTransport
                                                                          let conjugated :
                                                                              TraceAnalyticDMgmComparisonSource
                                                                                  .objectOf
                                                                                  (TraceAnalyticAdditiveHomotopyCategory
                                                                                    .objectOf
                                                                                    sourceComplex) ⟶
                                                                                TraceAnalyticDMgmComparisonSource
                                                                                  .objectOf
                                                                                  (TraceAnalyticAdditiveHomotopyCategory
                                                                                    .objectOf
                                                                                    targetComplex) :=
                                                                            sourceIso.hom ≫
                                                                              morphism ≫
                                                                                targetIso.inv
                                                                          let stableEquation :
                                                                              conjugated ≫
                                                                                  stableDenominator =
                                                                                stableNumerator :=
                                                                            Eq.trans
                                                                              (Category.assoc
                                                                                conjugated
                                                                                (TraceAnalyticDMgmComparisonSource
                                                                                  .quotientFunctor.map
                                                                                  denominator)
                                                                                roofTransport)
                                                                              (congrArg
                                                                                (fun arrow =>
                                                                                  arrow ≫
                                                                                    roofTransport)
                                                                                numeratorEquation)
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
                                                                                              stableDenominator
                                                                                              (Exists.intro
                                                                                                stableNumerator
                                                                                                (Exists.intro
                                                                                                  roofVertex
                                                                                                  (Exists.intro
                                                                                                    roof_eq
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
                                                                                                                  (And.intro
                                                                                                                    rfl
                                                                                                                    (And.intro
                                                                                                                      rfl
                                                                                                                      stableEquation)))))))))))))))))))))))))))))))))))))))))

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
