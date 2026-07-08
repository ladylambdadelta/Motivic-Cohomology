import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.SupportPredicates.IsoClosure.Owner

/-!
# Transport for support predicates

Strict support is contravariant in the complement of the embedding image: if
every degree outside the target embedding is also outside the source embedding,
then strict support on the source embedding gives strict support on the target
embedding.  This file packages that elementary support transport for the
degreewise bounded support predicates.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- Strict support transports along an implication between complements of
embedding images. -/
def strictSupport_transport
    {sourceIndex targetIndex : Type*}
    {sourceShape : ComplexShape sourceIndex}
    {targetShape : ComplexShape targetIndex}
    (sourceEmbedding :
      sourceShape.Embedding (ComplexShape.up ℤ))
    (targetEmbedding :
      targetShape.Embedding (ComplexShape.up ℤ))
    (complex : TraceAnalyticAdditiveCochainComplex)
    (complement :
      ∀ degree,
        (∀ targetIndex, targetEmbedding.f targetIndex ≠ degree) →
          ∀ sourceIndex, sourceEmbedding.f sourceIndex ≠ degree)
    (support : complex.IsStrictlySupported sourceEmbedding) :
    complex.IsStrictlySupported targetEmbedding where
  isZero :=
    fun degree targetComplement =>
      support.isZero degree (complement degree targetComplement)

/-- Ambient lower-tail support transports along strict-support transport. -/
theorem supportedLEAmbient_transport
    (sourceCut targetCut : ℤ)
    (complement :
      ∀ degree,
        (∀ targetIndex,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding targetCut).f
              targetIndex ≠ degree) →
          ∀ sourceIndex,
            (TraceAnalyticMotivicTStructure.truncLEEmbedding sourceCut).f
                sourceIndex ≠ degree)
    (object : TraceAnalyticDMgmComparisonSource)
    (membership :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportedLEAmbient sourceCut object) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportedLEAmbient targetCut object :=
  Exists.elim
    membership
    (fun bound boundData =>
      Exists.elim
        boundData
        (fun complex complexData =>
          And.elim
            complexData
            (fun bounded supportAndObject =>
              And.elim
                supportAndObject
                (fun support objectEq =>
                  Exists.intro
                    bound
                    (Exists.intro
                      complex
                      (And.intro
                        bounded
                        (And.intro
                          (Nonempty.elim
                            support
                            (fun supportWitness =>
                              Nonempty.intro
                                (TraceAnalyticDMgmComparisonSource
                                  .DegreewiseBoundedStable
                                  .strictSupport_transport
                                    (TraceAnalyticMotivicTStructure
                                      .truncLEEmbedding sourceCut)
                                    (TraceAnalyticMotivicTStructure
                                      .truncLEEmbedding targetCut)
                                    complex
                                    complement
                                    supportWitness)))
                          objectEq)))))))

/-- Ambient upper-tail support transports along strict-support transport. -/
theorem supportedGEAmbient_transport
    (sourceCut targetCut : ℤ)
    (complement :
      ∀ degree,
        (∀ targetIndex,
          (TraceAnalyticMotivicTStructure.truncGEEmbedding targetCut).f
              targetIndex ≠ degree) →
          ∀ sourceIndex,
            (TraceAnalyticMotivicTStructure.truncGEEmbedding sourceCut).f
                sourceIndex ≠ degree)
    (object : TraceAnalyticDMgmComparisonSource)
    (membership :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportedGEAmbient sourceCut object) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportedGEAmbient targetCut object :=
  Exists.elim
    membership
    (fun bound boundData =>
      Exists.elim
        boundData
        (fun complex complexData =>
          And.elim
            complexData
            (fun bounded supportAndObject =>
              And.elim
                supportAndObject
                (fun support objectEq =>
                  Exists.intro
                    bound
                    (Exists.intro
                      complex
                      (And.intro
                        bounded
                        (And.intro
                          (Nonempty.elim
                            support
                            (fun supportWitness =>
                              Nonempty.intro
                                (TraceAnalyticDMgmComparisonSource
                                  .DegreewiseBoundedStable
                                  .strictSupport_transport
                                    (TraceAnalyticMotivicTStructure
                                      .truncGEEmbedding sourceCut)
                                    (TraceAnalyticMotivicTStructure
                                      .truncGEEmbedding targetCut)
                                    complex
                                    complement
                                    supportWitness)))
                          objectEq)))))))

/-- Iso-closed lower-tail support transports along a complement implication. -/
theorem supportedLEIsoClosedAmbient_transport
    (sourceCut targetCut : ℤ)
    (complement :
      ∀ degree,
        (∀ targetIndex,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding targetCut).f
              targetIndex ≠ degree) →
          ∀ sourceIndex,
            (TraceAnalyticMotivicTStructure.truncLEEmbedding sourceCut).f
                sourceIndex ≠ degree) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportedLEIsoClosedAmbient sourceCut ≤
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportedLEIsoClosedAmbient targetCut :=
  CategoryTheory.monotone_isoClosure
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportedLEAmbient_transport sourceCut targetCut complement)

/-- Iso-closed upper-tail support transports along a complement implication. -/
theorem supportedGEIsoClosedAmbient_transport
    (sourceCut targetCut : ℤ)
    (complement :
      ∀ degree,
        (∀ targetIndex,
          (TraceAnalyticMotivicTStructure.truncGEEmbedding targetCut).f
              targetIndex ≠ degree) →
          ∀ sourceIndex,
            (TraceAnalyticMotivicTStructure.truncGEEmbedding sourceCut).f
                sourceIndex ≠ degree) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportedGEIsoClosedAmbient sourceCut ≤
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportedGEIsoClosedAmbient targetCut :=
  CategoryTheory.monotone_isoClosure
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportedGEAmbient_transport sourceCut targetCut complement)

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
