import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.Representatives.Owner

/-!
# Bounded roof objects for degreewise bounded representative fractions

This file packages the roof vertex produced by a representative Verdier
fraction as an actual object of the degreewise bounded stable source.  The
boundedness is transported across the Verdier-inverted denominator in the
stable comparison source.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- A degreewise-bounded morphism has concrete cochain representatives and
a Verdier roof whose roof vertex is packaged as a degreewise bounded stable
object.  The quotient images of the numerator and denominator are maps into
that internal roof object. -/
theorem exists_representativeBoundedRoof
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
                        ∃ (denominatorInverted :
                          TraceAnalyticStableNullSubcategory
                            .invertedMorphisms denominator),
                          ∃ (numerator :
                            TraceAnalyticAdditiveHomotopyCategory.objectOf
                                sourceComplex ⟶ roofVertex),
                            (sourceIso.hom ≫ morphism ≫ targetIso.inv) ≫
                                (TraceAnalyticDMgmComparisonSource
                                  .quotientFunctor.map denominator) =
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
                                    (fun roofVertex roofBoundedData =>
                                      Exists.elim
                                        roofBoundedData
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
                                                                                denominatorInverted
                                                                                (Exists.intro
                                                                                  numerator
                                                                                  numeratorEquation)))))))))))))))))))))))))))))

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
