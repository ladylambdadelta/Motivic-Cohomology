import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.ShortComplex.Transport.Owner

/-!
# Comparison with the transported normalized short complex

The normalized stable short complex extracted from the quotient distinguished
triangle agrees with the short complex obtained by directly transporting the
normalized additive short complex through the Verdier quotient.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- The extracted normalized stable short complex is isomorphic to the direct
Verdier transport of the normalized additive lower-inclusion short complex. -/
def stableNormalizedLowerInclusionShortComplexIsoTransported
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionShortComplex
        cut
        complex ≅
      TraceAnalyticMotivicTStructure
        .stableTransportedNormalizedLowerInclusionShortComplex cut complex :=
  ShortComplex.isoMk
    (Iso.refl _)
    (Iso.refl _)
    (Iso.refl _)
    (Eq.trans
      (id_comp
        (TraceAnalyticMotivicTStructure
          .stableTransportedNormalizedLowerInclusionShortComplex
            cut
            complex).f)
      (Eq.trans
        (Eq.trans
          (TraceAnalyticMotivicTStructure
            .stableTransportedNormalizedLowerInclusionShortComplex_f
              cut
              complex)
          (Eq.symm
            (TraceAnalyticMotivicTStructure
              .stableNormalizedLowerInclusionShortComplex_f cut complex)))
        (Eq.symm
          (comp_id
            (TraceAnalyticMotivicTStructure
              .stableNormalizedLowerInclusionShortComplex cut complex).f))))
    (Eq.trans
      (id_comp
        (TraceAnalyticMotivicTStructure
          .stableTransportedNormalizedLowerInclusionShortComplex
            cut
            complex).g)
      (Eq.trans
        (Eq.trans
          (TraceAnalyticMotivicTStructure
            .stableTransportedNormalizedLowerInclusionShortComplex_g
              cut
              complex)
          (Eq.symm
            (TraceAnalyticMotivicTStructure
              .stableNormalizedLowerInclusionConeMap_eq_mapOf_additiveNormalizedConeMap
                cut
                complex)))
        (Eq.trans
          (Eq.symm
            (TraceAnalyticMotivicTStructure
              .stableNormalizedLowerInclusionShortComplex_g cut complex))
          (Eq.symm
            (comp_id
              (TraceAnalyticMotivicTStructure
                .stableNormalizedLowerInclusionShortComplex cut complex).g)))))

/-- The first component of the normalized transport-comparison isomorphism is
the identity. -/
theorem stableNormalizedLowerInclusionShortComplexIsoTransported_hom_τ₁
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure
      .stableNormalizedLowerInclusionShortComplexIsoTransported
        cut
        complex).hom.τ₁ =
      𝟙 _ :=
  rfl

/-- The second component of the normalized transport-comparison isomorphism is
the identity. -/
theorem stableNormalizedLowerInclusionShortComplexIsoTransported_hom_τ₂
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure
      .stableNormalizedLowerInclusionShortComplexIsoTransported
        cut
        complex).hom.τ₂ =
      𝟙 _ :=
  rfl

/-- The third component of the normalized transport-comparison isomorphism is
the identity. -/
theorem stableNormalizedLowerInclusionShortComplexIsoTransported_hom_τ₃
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure
      .stableNormalizedLowerInclusionShortComplexIsoTransported
        cut
        complex).hom.τ₃ =
      𝟙 _ :=
  rfl

/-- The first component of the inverse normalized transport-comparison
isomorphism is the identity. -/
theorem stableNormalizedLowerInclusionShortComplexIsoTransported_inv_τ₁
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure
      .stableNormalizedLowerInclusionShortComplexIsoTransported
        cut
        complex).inv.τ₁ =
      𝟙 _ :=
  rfl

/-- The second component of the inverse normalized transport-comparison
isomorphism is the identity. -/
theorem stableNormalizedLowerInclusionShortComplexIsoTransported_inv_τ₂
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure
      .stableNormalizedLowerInclusionShortComplexIsoTransported
        cut
        complex).inv.τ₂ =
      𝟙 _ :=
  rfl

/-- The third component of the inverse normalized transport-comparison
isomorphism is the identity. -/
theorem stableNormalizedLowerInclusionShortComplexIsoTransported_inv_τ₃
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure
      .stableNormalizedLowerInclusionShortComplexIsoTransported
        cut
        complex).inv.τ₃ =
      𝟙 _ :=
  rfl

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
