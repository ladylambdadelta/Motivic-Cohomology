import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.ConeObject.Contractible.NullHomotopy.Owner

/-!
# Component formulas for normalized cone-comparison null homotopies

This file specializes Mathlib's component formula for `nullHomotopicMap'` to
the concrete mapping cone of the normalized cone-to-upper comparison map.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

/-- The degreewise component of a null-homotopic map on the normalized
cone-comparison mapping cone is the expected adjacent-differential sum. -/
theorem normalizedConeComparison_nullHomotopicMap_f
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hom :
      ∀ i j,
        (ComplexShape.up ℤ).Rel j i →
          (CochainComplex.mappingCone
            (TraceAnalyticMotivicTStructure
              .additiveNormalizedConeComparisonCochainMap cut complex)).X i ⟶
            (CochainComplex.mappingCone
              (TraceAnalyticMotivicTStructure
                .additiveNormalizedConeComparisonCochainMap cut complex)).X j)
    {k₂ k₁ k₀ : ℤ}
    (r₂₁ : (ComplexShape.up ℤ).Rel k₂ k₁)
    (r₁₀ : (ComplexShape.up ℤ).Rel k₁ k₀) :
    (_root_.HomologicalComplex.nullHomotopicMap' hom).f k₁ =
      (CochainComplex.mappingCone
        (TraceAnalyticMotivicTStructure
          .additiveNormalizedConeComparisonCochainMap cut complex)).d k₁ k₀ ≫
          hom k₀ k₁ r₁₀ +
        hom k₁ k₂ r₂₁ ≫
          (CochainComplex.mappingCone
            (TraceAnalyticMotivicTStructure
              .additiveNormalizedConeComparisonCochainMap cut complex)).d k₂ k₁ :=
  _root_.HomologicalComplex.nullHomotopicMap'_f
    r₂₁
    r₁₀
    hom

/-- If the identity on the normalized cone-comparison mapping cone is presented
as `nullHomotopicMap'`, then each interior degree component of the identity is
the corresponding adjacent-differential sum. -/
theorem normalizedConeComparison_identity_f_eq_nullHomotopicMap_f
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hom :
      ∀ i j,
        (ComplexShape.up ℤ).Rel j i →
          (CochainComplex.mappingCone
            (TraceAnalyticMotivicTStructure
              .additiveNormalizedConeComparisonCochainMap cut complex)).X i ⟶
            (CochainComplex.mappingCone
              (TraceAnalyticMotivicTStructure
                .additiveNormalizedConeComparisonCochainMap cut complex)).X j)
    (identity_eq :
      𝟙
          (CochainComplex.mappingCone
            (TraceAnalyticMotivicTStructure
              .additiveNormalizedConeComparisonCochainMap cut complex)) =
        _root_.HomologicalComplex.nullHomotopicMap' hom)
    {k₂ k₁ k₀ : ℤ}
    (r₂₁ : (ComplexShape.up ℤ).Rel k₂ k₁)
    (r₁₀ : (ComplexShape.up ℤ).Rel k₁ k₀) :
    (𝟙
      (CochainComplex.mappingCone
        (TraceAnalyticMotivicTStructure
          .additiveNormalizedConeComparisonCochainMap cut complex))).f k₁ =
      (CochainComplex.mappingCone
        (TraceAnalyticMotivicTStructure
          .additiveNormalizedConeComparisonCochainMap cut complex)).d k₁ k₀ ≫
          hom k₀ k₁ r₁₀ +
        hom k₁ k₂ r₂₁ ≫
          (CochainComplex.mappingCone
            (TraceAnalyticMotivicTStructure
              .additiveNormalizedConeComparisonCochainMap cut complex)).d k₂ k₁ :=
  Eq.trans
    (congrArg
      (fun map =>
        map.f k₁)
      identity_eq)
    (TraceAnalyticMotivicTStructure
      .normalizedConeComparison_nullHomotopicMap_f
        cut
        complex
        hom
        r₂₁
        r₁₀)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
