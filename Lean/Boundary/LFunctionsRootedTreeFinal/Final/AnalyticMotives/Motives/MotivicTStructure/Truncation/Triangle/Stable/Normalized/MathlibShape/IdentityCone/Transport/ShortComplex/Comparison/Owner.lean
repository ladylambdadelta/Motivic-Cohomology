import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.MathlibShape.IdentityCone.Transport.ShortComplex.Owner

/-!
# Comparison with the named stable cochain-decomposition short complex

The transported distinguished triangle has a Mathlib short complex.  The named
stable cochain-decomposition short complex has the same first two maps and
vertices.  This file gives the componentwise identity isomorphism from the
named short complex to Mathlib's attached short complex.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticMotivicTStructure

/-- The named stable cochain-decomposition short complex is isomorphic to
Mathlib's short complex attached to the transported stable
cochain-decomposition triangle. -/
def stableCochainDecompositionShortComplexIsoTransportedTriangleShortComplex
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    TraceAnalyticMotivicTStructure.stableCochainDecompositionShortComplex
        cut
        complex ≅
      shortComplexOfDistTriangle
        (TraceAnalyticMotivicTStructure
          .stableCochainDecompositionTransportedTriangle cut complex)
        (TraceAnalyticMotivicTStructure
          .stableCochainDecompositionTransportedTriangle_distinguished
            cut
            complex) :=
  ShortComplex.isoMk
    (Iso.refl _)
    (Iso.refl _)
    (Iso.refl _)
    (Eq.trans
      (id_comp
        (shortComplexOfDistTriangle
          (TraceAnalyticMotivicTStructure
            .stableCochainDecompositionTransportedTriangle cut complex)
          (TraceAnalyticMotivicTStructure
            .stableCochainDecompositionTransportedTriangle_distinguished
              cut
              complex)).f)
      (Eq.trans
        (TraceAnalyticMotivicTStructure
          .transportedTriangleShortComplex_f_eq_stableCochainDecomposition
            cut
            complex)
        (Eq.symm
          (comp_id
            (TraceAnalyticMotivicTStructure
              .stableCochainDecompositionShortComplex cut complex).f))))
    (Eq.trans
      (id_comp
        (shortComplexOfDistTriangle
          (TraceAnalyticMotivicTStructure
            .stableCochainDecompositionTransportedTriangle cut complex)
          (TraceAnalyticMotivicTStructure
            .stableCochainDecompositionTransportedTriangle_distinguished
              cut
              complex)).g)
      (Eq.trans
        (TraceAnalyticMotivicTStructure
          .transportedTriangleShortComplex_g_eq_stableCochainDecomposition
            cut
            complex)
        (Eq.symm
          (comp_id
            (TraceAnalyticMotivicTStructure
              .stableCochainDecompositionShortComplex cut complex).g))))

/-- The first component of the named-to-transported short-complex comparison
is the identity. -/
theorem stableCochainDecompositionShortComplexIsoTransportedTriangleShortComplex_hom_τ₁
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    (TraceAnalyticMotivicTStructure
      .stableCochainDecompositionShortComplexIsoTransportedTriangleShortComplex
        cut
        complex).hom.τ₁ =
      𝟙 _ :=
  rfl

/-- The second component of the named-to-transported short-complex comparison
is the identity. -/
theorem stableCochainDecompositionShortComplexIsoTransportedTriangleShortComplex_hom_τ₂
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    (TraceAnalyticMotivicTStructure
      .stableCochainDecompositionShortComplexIsoTransportedTriangleShortComplex
        cut
        complex).hom.τ₂ =
      𝟙 _ :=
  rfl

/-- The third component of the named-to-transported short-complex comparison
is the identity. -/
theorem stableCochainDecompositionShortComplexIsoTransportedTriangleShortComplex_hom_τ₃
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    (TraceAnalyticMotivicTStructure
      .stableCochainDecompositionShortComplexIsoTransportedTriangleShortComplex
        cut
        complex).hom.τ₃ =
      𝟙 _ :=
  rfl

/-- The opposite of Mathlib's short complex attached to the transported
triangle is isomorphic to the opposite of the named stable cochain-decomposition
short complex. -/
def transportedTriangleShortComplexOpIsoStableCochainDecompositionShortComplexOp
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    (shortComplexOfDistTriangle
        (TraceAnalyticMotivicTStructure
          .stableCochainDecompositionTransportedTriangle cut complex)
        (TraceAnalyticMotivicTStructure
          .stableCochainDecompositionTransportedTriangle_distinguished
            cut
            complex)).op ≅
      (TraceAnalyticMotivicTStructure.stableCochainDecompositionShortComplex
        cut
        complex).op :=
  ShortComplex.isoMk
    (Iso.refl _)
    (Iso.refl _)
    (Iso.refl _)
    (Eq.trans
      (id_comp
        (TraceAnalyticMotivicTStructure
          .stableCochainDecompositionShortComplex cut complex).op.f)
      (Eq.trans
        (congrArg
          Quiver.Hom.op
          (TraceAnalyticMotivicTStructure
            .transportedTriangleShortComplex_g_eq_stableCochainDecomposition
              cut
              complex))
        (Eq.symm
          (comp_id
            (shortComplexOfDistTriangle
              (TraceAnalyticMotivicTStructure
                .stableCochainDecompositionTransportedTriangle cut complex)
              (TraceAnalyticMotivicTStructure
                .stableCochainDecompositionTransportedTriangle_distinguished
                  cut
                  complex)).op.f))))
    (Eq.trans
      (id_comp
        (TraceAnalyticMotivicTStructure
          .stableCochainDecompositionShortComplex cut complex).op.g)
      (Eq.trans
        (congrArg
          Quiver.Hom.op
          (TraceAnalyticMotivicTStructure
            .transportedTriangleShortComplex_f_eq_stableCochainDecomposition
              cut
              complex))
        (Eq.symm
          (comp_id
            (shortComplexOfDistTriangle
              (TraceAnalyticMotivicTStructure
                .stableCochainDecompositionTransportedTriangle cut complex)
              (TraceAnalyticMotivicTStructure
                .stableCochainDecompositionTransportedTriangle_distinguished
                  cut
                  complex)).op.g))))

/-- The first component of the opposite short-complex comparison is the
identity. -/
theorem transportedTriangleShortComplexOpIsoStableCochainDecompositionShortComplexOp_hom_τ₁
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    (TraceAnalyticMotivicTStructure
      .transportedTriangleShortComplexOpIsoStableCochainDecompositionShortComplexOp
        cut
        complex).hom.τ₁ =
      𝟙 _ :=
  rfl

/-- The second component of the opposite short-complex comparison is the
identity. -/
theorem transportedTriangleShortComplexOpIsoStableCochainDecompositionShortComplexOp_hom_τ₂
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    (TraceAnalyticMotivicTStructure
      .transportedTriangleShortComplexOpIsoStableCochainDecompositionShortComplexOp
        cut
        complex).hom.τ₂ =
      𝟙 _ :=
  rfl

/-- The third component of the opposite short-complex comparison is the
identity. -/
theorem transportedTriangleShortComplexOpIsoStableCochainDecompositionShortComplexOp_hom_τ₃
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    (TraceAnalyticMotivicTStructure
      .transportedTriangleShortComplexOpIsoStableCochainDecompositionShortComplexOp
        cut
        complex).hom.τ₃ =
      𝟙 _ :=
  rfl

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
