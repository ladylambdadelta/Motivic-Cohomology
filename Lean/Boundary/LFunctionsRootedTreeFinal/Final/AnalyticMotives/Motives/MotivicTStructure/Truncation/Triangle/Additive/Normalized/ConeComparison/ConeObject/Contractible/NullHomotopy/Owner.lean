import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.ConeObject.Contractible.Owner

/-!
# Null-homotopic identity criterion for normalized cone-comparison cone objects

This file keeps the cochain-level contracting-homotopy criterion at the additive
cone-object owner level.  A presentation of the mapping-cone identity as
Mathlib's `nullHomotopicMap'` gives a contracting homotopy, hence nullity of
the normalized cone-comparison cone object and inversion of the comparison map.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

/-- If the identity on a cochain complex is presented as Mathlib's
`nullHomotopicMap'`, then the identity is homotopic to zero. -/
theorem cochainComplex_contractible_of_identity_eq_nullHomotopicMap
    (complex : TraceAnalyticAdditiveCochainComplex)
    (hom :
      ∀ i j,
        (ComplexShape.up ℤ).Rel j i →
          complex.X i ⟶ complex.X j)
    (identity_eq :
      𝟙 complex =
        _root_.HomologicalComplex.nullHomotopicMap' hom) :
    Nonempty (Homotopy (𝟙 complex) 0) :=
  let nullHomotopy :
      Homotopy (_root_.HomologicalComplex.nullHomotopicMap' hom) 0 :=
    _root_.HomologicalComplex.nullHomotopy' hom
  Eq.subst
    (motive := fun map => Nonempty (Homotopy map 0))
    (Eq.symm identity_eq)
    (Nonempty.intro nullHomotopy)

/-- A null-homotopic identity presentation for the concrete mapping cone of the
normalized cone-to-upper map makes the normalized cone object null. -/
theorem additiveNormalizedConeComparisonConeObject_null_of_identity_eq_nullHomotopicMap
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
        _root_.HomologicalComplex.nullHomotopicMap' hom) :
    TraceAnalyticStableNullSubcategory.P
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonConeObject
        cut
        complex) :=
  TraceAnalyticMotivicTStructure
    .additiveNormalizedConeComparisonConeObject_null_of_contractible
      cut
      complex
      (TraceAnalyticMotivicTStructure
        .cochainComplex_contractible_of_identity_eq_nullHomotopicMap
          (CochainComplex.mappingCone
            (TraceAnalyticMotivicTStructure
              .additiveNormalizedConeComparisonCochainMap cut complex))
          hom
          identity_eq)

/-- A null-homotopic identity presentation for the concrete mapping cone makes
the normalized cone-to-upper comparison map inverted by the analytic Verdier
class. -/
theorem additiveNormalizedConeComparisonMap_inverted_of_identity_eq_nullHomotopicMap
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
        _root_.HomologicalComplex.nullHomotopicMap' hom) :
    TraceAnalyticStableNullSubcategory.invertedMorphisms
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonMap
        cut
        complex) :=
  TraceAnalyticMotivicTStructure
    .additiveNormalizedConeComparisonMap_inverted_of_coneObject_null
      cut
      complex
      (TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonConeObject_null_of_identity_eq_nullHomotopicMap
          cut
          complex
          hom
          identity_eq)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
