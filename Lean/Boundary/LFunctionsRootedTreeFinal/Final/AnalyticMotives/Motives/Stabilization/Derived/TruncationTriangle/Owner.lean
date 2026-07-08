import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.ConeComparison.Owner

/-!
# Derived truncation triangle for analytic motives

This file packages the Yoneda abelian-envelope truncation short exact sequence
as the distinguished short-exact-sequence triangle in the derived analytic
motive category.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticMotivicTStructure

attribute [local instance]
  TraceAnalyticDerivedMotiveCategory.hasDerivedCategory

/-- The derived connecting morphism attached to the analytic Yoneda
truncation short exact sequence. -/
def abelianEnvelopeCochainDecompositionDerivedConnectingMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortComplex cut complex)) :
    TraceAnalyticDerivedMotiveCategory.localizationFunctor.obj
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortComplex cut complex).X₃ ⟶
      (TraceAnalyticDerivedMotiveCategory.localizationFunctor.obj
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortComplex cut complex).X₁)⟦(1 : ℤ)⟧ :=
  DerivedCategory.triangleOfSESδ hshortExact

/-- The distinguished derived triangle associated to the analytic Yoneda
truncation short exact sequence. -/
def abelianEnvelopeCochainDecompositionDerivedTriangle
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortComplex cut complex)) :
    Triangle TraceAnalyticDerivedMotiveCategory :=
  DerivedCategory.triangleOfSES hshortExact

/-- The first vertex of the derived analytic truncation triangle is the lower
truncation complex localized in the derived category. -/
theorem abelianEnvelopeCochainDecompositionDerivedTriangle_obj₁
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortComplex cut complex)) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeCochainDecompositionDerivedTriangle
        cut
        complex
        hshortExact).obj₁ =
      TraceAnalyticDerivedMotiveCategory.localizationFunctor.obj
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortComplex cut complex).X₁ :=
  rfl

/-- The second vertex of the derived analytic truncation triangle is the
original represented complex localized in the derived category. -/
theorem abelianEnvelopeCochainDecompositionDerivedTriangle_obj₂
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortComplex cut complex)) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeCochainDecompositionDerivedTriangle
        cut
        complex
        hshortExact).obj₂ =
      TraceAnalyticDerivedMotiveCategory.localizationFunctor.obj
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortComplex cut complex).X₂ :=
  rfl

/-- The third vertex of the derived analytic truncation triangle is the upper
truncation complex localized in the derived category. -/
theorem abelianEnvelopeCochainDecompositionDerivedTriangle_obj₃
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortComplex cut complex)) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeCochainDecompositionDerivedTriangle
        cut
        complex
        hshortExact).obj₃ =
      TraceAnalyticDerivedMotiveCategory.localizationFunctor.obj
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortComplex cut complex).X₃ :=
  rfl

/-- The first map of the derived analytic truncation triangle is the derived
image of the lower inclusion. -/
theorem abelianEnvelopeCochainDecompositionDerivedTriangle_mor₁
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortComplex cut complex)) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeCochainDecompositionDerivedTriangle
        cut
        complex
        hshortExact).mor₁ =
      TraceAnalyticDerivedMotiveCategory.localizationFunctor.map
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortComplex cut complex).f :=
  rfl

/-- The second map of the derived analytic truncation triangle is the derived
image of the upper projection. -/
theorem abelianEnvelopeCochainDecompositionDerivedTriangle_mor₂
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortComplex cut complex)) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeCochainDecompositionDerivedTriangle
        cut
        complex
        hshortExact).mor₂ =
      TraceAnalyticDerivedMotiveCategory.localizationFunctor.map
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortComplex cut complex).g :=
  rfl

/-- The third map of the derived analytic truncation triangle is the
short-exact-sequence connecting morphism. -/
theorem abelianEnvelopeCochainDecompositionDerivedTriangle_mor₃
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortComplex cut complex)) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeCochainDecompositionDerivedTriangle
        cut
        complex
        hshortExact).mor₃ =
      TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionDerivedConnectingMap
          cut
          complex
          hshortExact :=
  rfl

/-- The derived analytic truncation triangle is distinguished. -/
theorem abelianEnvelopeCochainDecompositionDerivedTriangle_distinguished
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortComplex cut complex)) :
    TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionDerivedTriangle
          cut
          complex
          hshortExact ∈
      distTriang TraceAnalyticDerivedMotiveCategory :=
  DerivedCategory.triangleOfSES_distinguished hshortExact

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
