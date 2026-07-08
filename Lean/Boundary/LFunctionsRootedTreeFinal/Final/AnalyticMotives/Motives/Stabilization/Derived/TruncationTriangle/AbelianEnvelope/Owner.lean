import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.ConeComparison.Owner

/-!
# Derived triangle from the intrinsic abelian-envelope truncation sequence

This file packages the intrinsic abelian-envelope truncation short exact
sequence as the distinguished short-exact-sequence triangle in the derived
analytic motive category.
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

/-- The derived connecting morphism attached to the intrinsic abelian-envelope
truncation short exact sequence. -/
def abelianEnvelopeIntrinsicCochainDecompositionDerivedConnectingMap
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            cut
            complex)) :
    TraceAnalyticDerivedMotiveCategory.localizationFunctor.obj
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            cut
            complex).X₃ ⟶
      (TraceAnalyticDerivedMotiveCategory.localizationFunctor.obj
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            cut
            complex).X₁)⟦(1 : ℤ)⟧ :=
  DerivedCategory.triangleOfSESδ hshortExact

/-- The distinguished derived triangle attached to the intrinsic
abelian-envelope truncation short exact sequence. -/
def abelianEnvelopeIntrinsicCochainDecompositionDerivedTriangle
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            cut
            complex)) :
    Triangle TraceAnalyticDerivedMotiveCategory :=
  DerivedCategory.triangleOfSES hshortExact

/-- The first vertex of the intrinsic abelian-envelope derived truncation
triangle is the localized lower truncation complex. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionDerivedTriangle_obj₁
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            cut
            complex)) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionDerivedTriangle
        cut
        complex
        hshortExact).obj₁ =
      TraceAnalyticDerivedMotiveCategory.localizationFunctor.obj
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            cut
            complex).X₁ :=
  rfl

/-- The second vertex of the intrinsic abelian-envelope derived truncation
triangle is the localized input complex. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionDerivedTriangle_obj₂
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            cut
            complex)) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionDerivedTriangle
        cut
        complex
        hshortExact).obj₂ =
      TraceAnalyticDerivedMotiveCategory.localizationFunctor.obj
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            cut
            complex).X₂ :=
  rfl

/-- The third vertex of the intrinsic abelian-envelope derived truncation
triangle is the localized upper truncation complex. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionDerivedTriangle_obj₃
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            cut
            complex)) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionDerivedTriangle
        cut
        complex
        hshortExact).obj₃ =
      TraceAnalyticDerivedMotiveCategory.localizationFunctor.obj
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            cut
            complex).X₃ :=
  rfl

/-- The first map of the intrinsic abelian-envelope derived truncation triangle
is the localized lower inclusion. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionDerivedTriangle_mor₁
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            cut
            complex)) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionDerivedTriangle
        cut
        complex
        hshortExact).mor₁ =
      TraceAnalyticDerivedMotiveCategory.localizationFunctor.map
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            cut
            complex).f :=
  rfl

/-- The second map of the intrinsic abelian-envelope derived truncation
triangle is the localized upper projection. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionDerivedTriangle_mor₂
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            cut
            complex)) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionDerivedTriangle
        cut
        complex
        hshortExact).mor₂ =
      TraceAnalyticDerivedMotiveCategory.localizationFunctor.map
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            cut
            complex).g :=
  rfl

/-- The third map of the intrinsic abelian-envelope derived truncation triangle
is the short-exact-sequence connecting morphism. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionDerivedTriangle_mor₃
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            cut
            complex)) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionDerivedTriangle
        cut
        complex
        hshortExact).mor₃ =
      TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionDerivedConnectingMap
          cut
          complex
          hshortExact :=
  rfl

/-- The intrinsic abelian-envelope derived truncation triangle is
distinguished. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionDerivedTriangle_distinguished
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            cut
            complex)) :
    TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionDerivedTriangle
          cut
          complex
          hshortExact ∈
      distTriang TraceAnalyticDerivedMotiveCategory :=
  DerivedCategory.triangleOfSES_distinguished hshortExact

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
