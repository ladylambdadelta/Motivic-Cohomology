import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.ShortComplex.Transport.Owner

/-!
# Comparison with the transported lower-inclusion short complex

The stable lower-inclusion short complex extracted from the quotient
distinguished triangle agrees with the short complex obtained by directly
transporting the additive lower-inclusion short complex through the Verdier
quotient.  This file packages that agreement as an isomorphism of short
complexes.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- The extracted stable short complex is isomorphic to the direct Verdier
transport of the additive lower-inclusion short complex. -/
def stableLowerInclusionShortComplexIsoTransported
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.stableLowerInclusionShortComplex
        cut
        complex ≅
      TraceAnalyticMotivicTStructure.stableTransportedLowerInclusionShortComplex
        cut
        complex :=
  ShortComplex.isoMk
    (Iso.refl _)
    (Iso.refl _)
    (Iso.refl _)
    (Eq.trans
      (id_comp
        (TraceAnalyticMotivicTStructure
          .stableTransportedLowerInclusionShortComplex cut complex).f)
      (Eq.trans
        (Eq.trans
          (TraceAnalyticMotivicTStructure
            .stableTransportedLowerInclusionShortComplex_f cut complex)
          (Eq.symm
            (TraceAnalyticMotivicTStructure
              .stableLowerInclusionShortComplex_f cut complex)))
        (Eq.symm
          (comp_id
            (TraceAnalyticMotivicTStructure
              .stableLowerInclusionShortComplex cut complex).f))))
    (Eq.trans
      (id_comp
        (TraceAnalyticMotivicTStructure
          .stableTransportedLowerInclusionShortComplex cut complex).g)
      (Eq.trans
        (Eq.trans
          (TraceAnalyticMotivicTStructure
            .stableTransportedLowerInclusionShortComplex_g cut complex)
          (Eq.symm
            (TraceAnalyticMotivicTStructure
              .stableLowerInclusionConeMap_eq_mapOf_additiveLowerInclusionConeMap
                cut
                complex)))
        (Eq.trans
          (Eq.symm
            (TraceAnalyticMotivicTStructure
              .stableLowerInclusionShortComplex_g_eq_coneMap cut complex))
          (Eq.symm
            (comp_id
              (TraceAnalyticMotivicTStructure
                .stableLowerInclusionShortComplex cut complex).g)))))

/-- The first component of the transport-comparison isomorphism is the identity. -/
theorem stableLowerInclusionShortComplexIsoTransported_hom_τ₁
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure
      .stableLowerInclusionShortComplexIsoTransported cut complex).hom.τ₁ =
      𝟙 _ :=
  rfl

/-- The second component of the transport-comparison isomorphism is the
identity. -/
theorem stableLowerInclusionShortComplexIsoTransported_hom_τ₂
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure
      .stableLowerInclusionShortComplexIsoTransported cut complex).hom.τ₂ =
      𝟙 _ :=
  rfl

/-- The third component of the transport-comparison isomorphism is the
identity. -/
theorem stableLowerInclusionShortComplexIsoTransported_hom_τ₃
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure
      .stableLowerInclusionShortComplexIsoTransported cut complex).hom.τ₃ =
      𝟙 _ :=
  rfl

/-- The first component of the inverse transport-comparison isomorphism is the
identity. -/
theorem stableLowerInclusionShortComplexIsoTransported_inv_τ₁
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure
      .stableLowerInclusionShortComplexIsoTransported cut complex).inv.τ₁ =
      𝟙 _ :=
  rfl

/-- The second component of the inverse transport-comparison isomorphism is
the identity. -/
theorem stableLowerInclusionShortComplexIsoTransported_inv_τ₂
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure
      .stableLowerInclusionShortComplexIsoTransported cut complex).inv.τ₂ =
      𝟙 _ :=
  rfl

/-- The third component of the inverse transport-comparison isomorphism is the
identity. -/
theorem stableLowerInclusionShortComplexIsoTransported_inv_τ₃
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure
      .stableLowerInclusionShortComplexIsoTransported cut complex).inv.τ₃ =
      𝟙 _ :=
  rfl

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
