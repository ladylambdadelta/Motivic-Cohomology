import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.Representatives.BoundedRoof.InternalSpan.Owner

/-!
# Isomorphism denominator for internal bounded roof spans

This file strengthens the internal bounded roof span theorem by carrying the
Verdier-inverted denominator all the way into the degreewise bounded stable
source as an actual isomorphism.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- The internal representative bounded roof span can be chosen with an
isomorphism denominator.  The isomorphism proof is transported from the
Verdier-localized denominator and the equality identifying the packaged roof
with the stable image of the raw roof vertex. -/
theorem exists_internalRepresentativeBoundedRoofSpan_denominatorIso
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
                        ∃ (_ : IsIso denominator),
                          ∃ (numerator :
                            sourceRepresentative ⟶ roof),
                            (sourceIso.hom ≫ morphism ≫ targetIso.inv) ≫
                                denominator =
                              numerator :=
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
                                                    (fun denominatorInverted
                                                      numeratorData =>
                                                      Exists.elim
                                                        numeratorData
                                                        (fun numerator
                                                          numeratorEquation =>
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
                                                          let roofTransport :
                                                              TraceAnalyticDMgmComparisonSource
                                                                  .objectOf
                                                                  roofVertex ⟶
                                                                roof.object :=
                                                            (eqToIso
                                                              (Eq.symm
                                                                roof_eq)).hom
                                                          let stableDenominator :
                                                              targetRepresentative ⟶
                                                                roof :=
                                                            TraceAnalyticDMgmComparisonSource
                                                                .quotientFunctor.map
                                                                denominator ≫
                                                              roofTransport
                                                          let stableNumerator :
                                                              sourceRepresentative ⟶
                                                                roof :=
                                                            TraceAnalyticDMgmComparisonSource
                                                                .quotientFunctor.map
                                                                numerator ≫
                                                              roofTransport
                                                          let quotientDenominatorIso :
                                                              IsIso
                                                                (TraceAnalyticDMgmComparisonSource
                                                                  .quotientFunctor.map
                                                                  denominator) :=
                                                            CategoryTheory.Localization
                                                              .inverts
                                                              TraceAnalyticDMgmComparisonSource
                                                                .quotientFunctor
                                                              denominatorInverted
                                                          let roofTransportIso :
                                                              IsIso roofTransport :=
                                                            (eqToIso
                                                              (Eq.symm
                                                                roof_eq)).isIso_hom
                                                          let stableDenominatorIso :
                                                              IsIso
                                                                stableDenominator :=
                                                            IsIso.comp_isIso'
                                                              quotientDenominatorIso
                                                              roofTransportIso
                                                          let conjugated :
                                                              sourceRepresentative.object ⟶
                                                                targetRepresentative.object :=
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
                                                                                stableDenominatorIso
                                                                                (Exists.intro
                                                                                  stableNumerator
                                                                                  stableEquation)))))))))))))))))))))))))))))

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
