import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.ConeComparison.Map.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Exact.Owner

/-!
# Short-exact cone comparison in the abelian envelope

This file applies Mathlib's short-exact mapping-cone theorem to the intrinsic
abelian-envelope truncation short complex.  A proved short exact truncation
sequence therefore supplies a quasi-isomorphism from the lower-inclusion
mapping cone to the upper truncation.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- The canonical Mathlib cone-to-third-object map attached to the intrinsic
abelian-envelope truncation short complex. -/
def abelianEnvelopeIntrinsicCochainDecompositionDescShortComplex
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex) :
    CochainComplex.mappingCone
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionLowerMap cut complex) ⟶
      TraceAnalyticMotivicTStructure.abelianEnvelopeTruncGE cut complex :=
  CochainComplex.mappingCone.descShortComplex
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionShortComplex cut complex)

/-- The canonical short-exact cone comparison restricts along the original
complex summand to the abelian upper projection. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionDescShortComplex_inr
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex) :
    CochainComplex.mappingCone.inr
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionLowerMap cut complex) ≫
      TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionDescShortComplex
          cut
          complex =
      TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionUpperMap cut complex :=
  CochainComplex.mappingCone.inr_descShortComplex
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionShortComplex cut complex)

/-- The canonical short-exact cone comparison is zero on the shifted lower
summand. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionDescShortComplex_inl_v
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (sourceDegree targetDegree : ℤ)
    (degreeRelation : sourceDegree + (-1) = targetDegree) :
    (CochainComplex.mappingCone.inl
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionLowerMap cut complex)).v
        sourceDegree
        targetDegree
        degreeRelation ≫
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionDescShortComplex
          cut
          complex).f targetDegree =
      0 :=
  CochainComplex.mappingCone.inl_v_descShortComplex_f
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionShortComplex cut complex)
    sourceDegree
    targetDegree
    degreeRelation

/-- The named abelian-envelope normalized cone comparison is the canonical
short-exact mapping-cone descent map attached to the intrinsic truncation short
complex. -/
theorem abelianEnvelopeNormalizedConeComparisonCochainMap_eq_descShortComplex
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex) :
    TraceAnalyticMotivicTStructure
        .abelianEnvelopeNormalizedConeComparisonCochainMap cut complex =
      TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionDescShortComplex
          cut
          complex :=
  HomologicalComplex.hom_ext
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeNormalizedConeComparisonCochainMap cut complex)
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionDescShortComplex
        cut
        complex)
    (fun degree =>
      CochainComplex.mappingCone.ext_from
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionLowerMap cut complex)
        (degree + 1)
        degree
        (by omega)
        (Eq.trans
          (CochainComplex.mappingCone.inl_v_desc_f
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeCochainDecompositionLowerMap cut complex)
            (0 :
              Cochain
                (TraceAnalyticMotivicTStructure
                  .abelianEnvelopeDecompositionTruncLE cut complex)
                (TraceAnalyticMotivicTStructure
                  .abelianEnvelopeTruncGE cut complex)
                (-1))
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeCochainDecompositionUpperMap cut complex)
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeNormalizedConeComparisonCochainMap_desc_eq
                cut
                complex)
            (degree + 1)
            degree
            (by omega))
          (Eq.symm
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeIntrinsicCochainDecompositionDescShortComplex_inl_v
                cut
                complex
                (degree + 1)
                degree
                (by omega))))
        (Eq.trans
          (CochainComplex.mappingCone.inr_f_desc_f
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeCochainDecompositionLowerMap cut complex)
            (0 :
              Cochain
                (TraceAnalyticMotivicTStructure
                  .abelianEnvelopeDecompositionTruncLE cut complex)
                (TraceAnalyticMotivicTStructure
                  .abelianEnvelopeTruncGE cut complex)
                (-1))
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeCochainDecompositionUpperMap cut complex)
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeNormalizedConeComparisonCochainMap_desc_eq
                cut
                complex)
            degree)
          (Eq.symm
            (CochainComplex.mappingCone.inr_f_descShortComplex_f
              (TraceAnalyticMotivicTStructure
                .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
                  cut
                  complex)
              degree))))

/-- The canonical short-exact cone comparison is a quasi-isomorphism whenever
the intrinsic abelian-envelope truncation short complex is short exact. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionDescShortComplex_quasiIso
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            cut
            complex)) :
    QuasiIso
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionDescShortComplex
          cut
          complex) :=
  CochainComplex.mappingCone.quasiIso_descShortComplex hshortExact

/-- The named abelian-envelope normalized cone-to-upper comparison is a
quasi-isomorphism whenever the intrinsic abelian-envelope truncation short
complex is short exact. -/
theorem abelianEnvelopeNormalizedConeComparisonCochainMap_quasiIso
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            cut
            complex)) :
    QuasiIso
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeNormalizedConeComparisonCochainMap cut complex) :=
  Eq.subst
    (motive :=
      fun comparisonMap =>
        QuasiIso comparisonMap)
    (Eq.symm
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeNormalizedConeComparisonCochainMap_eq_descShortComplex
          cut
          complex))
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionDescShortComplex_quasiIso
        cut
        complex
        hshortExact)

/-- Degreewise short exactness of the intrinsic abelian-envelope truncation
sequence supplies the canonical cone-to-upper quasi-isomorphism. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionDescShortComplex_quasiIso_of_degreewise
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (hdegree :
      ∀ degree : ℤ,
        ((TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
              cut
              complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveAbelianEnvelope
            (ComplexShape.up ℤ)
            degree)).ShortExact) :
    QuasiIso
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionDescShortComplex
          cut
          complex) :=
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeIntrinsicCochainDecompositionDescShortComplex_quasiIso
      cut
      complex
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionShortExact_of_degreewise
          cut
          complex
          hdegree)

/-- Degreewise short exactness of the intrinsic abelian-envelope truncation
sequence supplies the named cone-to-upper quasi-isomorphism. -/
theorem abelianEnvelopeNormalizedConeComparisonCochainMap_quasiIso_of_degreewise
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (hdegree :
      ∀ degree : ℤ,
        ((TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
              cut
              complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveAbelianEnvelope
            (ComplexShape.up ℤ)
            degree)).ShortExact) :
    QuasiIso
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeNormalizedConeComparisonCochainMap cut complex) :=
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeNormalizedConeComparisonCochainMap_quasiIso
      cut
      complex
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionShortExact_of_degreewise
          cut
          complex
          hdegree)

/-- Degreewise exactness, monicity of the lower map, and epicity of the upper
map supply the canonical cone-to-upper quasi-isomorphism. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionDescShortComplex_quasiIso_of_degreewise_exact_mono_epi
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (hexact :
      ∀ degree : ℤ,
        ((TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
              cut
              complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveAbelianEnvelope
            (ComplexShape.up ℤ)
            degree)).Exact)
    (hmono :
      ∀ degree : ℤ,
        Mono
          (((TraceAnalyticMotivicTStructure
              .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
                cut
                complex).map
            (HomologicalComplex.eval
              TraceAnalyticAdditiveAbelianEnvelope
              (ComplexShape.up ℤ)
              degree)).f))
    (hepi :
      ∀ degree : ℤ,
        Epi
          (((TraceAnalyticMotivicTStructure
              .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
                cut
                complex).map
            (HomologicalComplex.eval
              TraceAnalyticAdditiveAbelianEnvelope
              (ComplexShape.up ℤ)
              degree)).g)) :
    QuasiIso
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionDescShortComplex
          cut
          complex) :=
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeIntrinsicCochainDecompositionDescShortComplex_quasiIso
      cut
      complex
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionShortExact_of_degreewise_exact_mono_epi
          cut
          complex
          hexact
          hmono
          hepi)

/-- Degreewise exactness, monicity of the lower map, and epicity of the upper
map supply the named cone-to-upper quasi-isomorphism. -/
theorem abelianEnvelopeNormalizedConeComparisonCochainMap_quasiIso_of_degreewise_exact_mono_epi
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (hexact :
      ∀ degree : ℤ,
        ((TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
              cut
              complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveAbelianEnvelope
            (ComplexShape.up ℤ)
            degree)).Exact)
    (hmono :
      ∀ degree : ℤ,
        Mono
          (((TraceAnalyticMotivicTStructure
              .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
                cut
                complex).map
            (HomologicalComplex.eval
              TraceAnalyticAdditiveAbelianEnvelope
              (ComplexShape.up ℤ)
              degree)).f))
    (hepi :
      ∀ degree : ℤ,
        Epi
          (((TraceAnalyticMotivicTStructure
              .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
                cut
                complex).map
            (HomologicalComplex.eval
              TraceAnalyticAdditiveAbelianEnvelope
              (ComplexShape.up ℤ)
              degree)).g)) :
    QuasiIso
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeNormalizedConeComparisonCochainMap cut complex) :=
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeNormalizedConeComparisonCochainMap_quasiIso
      cut
      complex
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionShortExact_of_degreewise_exact_mono_epi
          cut
          complex
          hexact
          hmono
          hepi)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
