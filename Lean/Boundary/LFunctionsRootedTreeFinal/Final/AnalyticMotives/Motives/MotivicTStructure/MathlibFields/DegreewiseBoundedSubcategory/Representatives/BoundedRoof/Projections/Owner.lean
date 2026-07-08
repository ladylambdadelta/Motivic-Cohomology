import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.Representatives.BoundedRoof.Owner

/-!
# Stable projections from bounded representative roofs

This file turns the raw Verdier roof numerator and denominator into stable
comparison-source maps landing in the packaged degreewise bounded roof object.
The only transport is the equality identifying that packaged object with the
stable image of the raw additive-homotopy roof vertex.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- A bounded representative roof supplies stable numerator and denominator
maps into the packaged degreewise bounded roof object, with the same conjugated
morphism factorization equation. -/
theorem exists_representativeBoundedRoof_stableMaps
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
                          (sourceIso.hom ≫ morphism ≫ targetIso.inv) ≫
                              stableDenominator =
                            stableNumerator :=
  Exists.elim
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .exists_representativeBoundedRoof morphism)
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
                                                  denominatorInvertedData =>
                                                  Exists.elim
                                                    denominatorInvertedData
                                                    (fun _ numeratorData =>
                                                      Exists.elim
                                                        numeratorData
                                                        (fun numerator
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
                                                                                stableEquation))))))))))))))))))))))))))))

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
