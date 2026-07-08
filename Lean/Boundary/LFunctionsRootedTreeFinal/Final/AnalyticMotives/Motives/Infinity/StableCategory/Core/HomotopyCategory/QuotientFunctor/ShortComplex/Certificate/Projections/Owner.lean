import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.HomotopyCategory.QuotientFunctor.ShortComplex.Certificate.Owner

/-!
# Projections from the homotopy quotient short-complex certificate

This file exposes named projections from the bundled certificate for the short
complex attached to a homotopy quotient image.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticStableInfinityCategory

/-- The first map projection from the homotopy quotient short-complex
certificate. -/
theorem homotopyQuotientFunctor_shortComplex_certificate_f
    (triangle :
      Pretriangulated.Triangle TraceAnalyticAdditiveHomotopyCategory)
    (distinguished :
      triangle ∈
        TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles)
    (leftProbe : TraceAnalyticStableInfinityCategory.HomotopyCategoryᵒᵖ)
    (rightProbe : TraceAnalyticStableInfinityCategory.HomotopyCategory) :
    (TraceAnalyticStableInfinityCategory
      .homotopyQuotientFunctor_shortComplex
        triangle
        distinguished).f =
      ((TraceAnalyticStableInfinityCategory.homotopyQuotientFunctor)
        .mapTriangle.obj triangle).mor₁ :=
  (TraceAnalyticStableInfinityCategory
    .homotopyQuotientFunctor_shortComplex_certificate
      triangle
      distinguished
      leftProbe
      rightProbe).left

/-- The second map projection from the homotopy quotient short-complex
certificate. -/
theorem homotopyQuotientFunctor_shortComplex_certificate_g
    (triangle :
      Pretriangulated.Triangle TraceAnalyticAdditiveHomotopyCategory)
    (distinguished :
      triangle ∈
        TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles)
    (leftProbe : TraceAnalyticStableInfinityCategory.HomotopyCategoryᵒᵖ)
    (rightProbe : TraceAnalyticStableInfinityCategory.HomotopyCategory) :
    (TraceAnalyticStableInfinityCategory
      .homotopyQuotientFunctor_shortComplex
        triangle
        distinguished).g =
      ((TraceAnalyticStableInfinityCategory.homotopyQuotientFunctor)
        .mapTriangle.obj triangle).mor₂ :=
  (TraceAnalyticStableInfinityCategory
    .homotopyQuotientFunctor_shortComplex_certificate
      triangle
      distinguished
      leftProbe
      rightProbe).right.left

/-- The zero-field projection from the homotopy quotient short-complex
certificate. -/
theorem homotopyQuotientFunctor_shortComplex_certificate_zero
    (triangle :
      Pretriangulated.Triangle TraceAnalyticAdditiveHomotopyCategory)
    (distinguished :
      triangle ∈
        TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles)
    (leftProbe : TraceAnalyticStableInfinityCategory.HomotopyCategoryᵒᵖ)
    (rightProbe : TraceAnalyticStableInfinityCategory.HomotopyCategory) :
    (TraceAnalyticStableInfinityCategory
      .homotopyQuotientFunctor_shortComplex
        triangle
        distinguished).zero =
      TraceAnalyticStableInfinityCategory
        .homotopyQuotientFunctor_distinguished_mor₁_comp_mor₂
          triangle
          distinguished :=
  (TraceAnalyticStableInfinityCategory
    .homotopyQuotientFunctor_shortComplex_certificate
      triangle
      distinguished
      leftProbe
      rightProbe).right.right.left

/-- The zero-composition triple projection from the homotopy quotient
short-complex certificate. -/
theorem homotopyQuotientFunctor_shortComplex_certificate_zeroCompositions
    (triangle :
      Pretriangulated.Triangle TraceAnalyticAdditiveHomotopyCategory)
    (distinguished :
      triangle ∈
        TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles)
    (leftProbe : TraceAnalyticStableInfinityCategory.HomotopyCategoryᵒᵖ)
    (rightProbe : TraceAnalyticStableInfinityCategory.HomotopyCategory) :
    ((TraceAnalyticStableInfinityCategory.homotopyQuotientFunctor)
        .mapTriangle.obj triangle).mor₁ ≫
      ((TraceAnalyticStableInfinityCategory.homotopyQuotientFunctor)
        .mapTriangle.obj triangle).mor₂ =
        0 ∧
      ((TraceAnalyticStableInfinityCategory.homotopyQuotientFunctor)
          .mapTriangle.obj triangle).mor₂ ≫
        ((TraceAnalyticStableInfinityCategory.homotopyQuotientFunctor)
          .mapTriangle.obj triangle).mor₃ =
          0 ∧
        ((TraceAnalyticStableInfinityCategory.homotopyQuotientFunctor)
            .mapTriangle.obj triangle).mor₃ ≫
          (((TraceAnalyticStableInfinityCategory.homotopyQuotientFunctor)
            .mapTriangle.obj triangle).mor₁)⟦(1 : ℤ)⟧' =
            0 :=
  And.intro
    ((TraceAnalyticStableInfinityCategory
      .homotopyQuotientFunctor_shortComplex_certificate
        triangle
        distinguished
        leftProbe
        rightProbe).right.right.right.left)
    (And.intro
      ((TraceAnalyticStableInfinityCategory
        .homotopyQuotientFunctor_shortComplex_certificate
          triangle
          distinguished
          leftProbe
          rightProbe).right.right.right.right.left)
      ((TraceAnalyticStableInfinityCategory
        .homotopyQuotientFunctor_shortComplex_certificate
          triangle
          distinguished
          leftProbe
          rightProbe).right.right.right.right.right.left))

/-- The paired exactness projection from the homotopy quotient short-complex
certificate. -/
theorem homotopyQuotientFunctor_shortComplex_certificate_pairedExact
    (triangle :
      Pretriangulated.Triangle TraceAnalyticAdditiveHomotopyCategory)
    (distinguished :
      triangle ∈
        TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles)
    (leftProbe : TraceAnalyticStableInfinityCategory.HomotopyCategoryᵒᵖ)
    (rightProbe : TraceAnalyticStableInfinityCategory.HomotopyCategory) :
    ((TraceAnalyticStableInfinityCategory
      .homotopyQuotientFunctor_shortComplex
        triangle
        distinguished).map
        (preadditiveCoyoneda.obj leftProbe)).Exact ∧
      ((TraceAnalyticStableInfinityCategory
        .homotopyQuotientFunctor_shortComplex
          triangle
          distinguished).op.map
          (preadditiveYoneda.obj rightProbe)).Exact :=
  (TraceAnalyticStableInfinityCategory
    .homotopyQuotientFunctor_shortComplex_certificate
      triangle
      distinguished
      leftProbe
      rightProbe).right.right.right.right.right.right

end TraceAnalyticStableInfinityCategory

end AnalyticMotives
end LFunctions
end Boundary
