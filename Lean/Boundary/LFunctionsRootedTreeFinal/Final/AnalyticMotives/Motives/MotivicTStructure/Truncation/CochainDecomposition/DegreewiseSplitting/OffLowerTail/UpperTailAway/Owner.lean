import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.DegreewiseSplitting.OffLowerTail.ArithmeticBridge.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.DegreewiseSplitting.OffLowerTail.ZeroLower.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.DegreewiseSplitting.OffLowerTail.UpperInverse.TwoSided.Owner

/-!
# Nonboundary upper-tail exactness for the cochain decomposition

This file proves the honest off-lower-tail splitting theorem only away from
the boundary degree.  The boundary degree is governed by the opcycles quotient
and is intentionally excluded here.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- In an off-lower-tail degree strictly away from the boundary cut, the
normalized cochain-decomposition short complex splits by the concrete
upper-truncation isomorphism. -/
def additiveCochainDecompositionUpperTailAwaySplitting
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (degree : ℤ)
    (hnone :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding
        (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
        none)
    (hdegree : cut ≤ degree)
    (hne : degree ≠ cut) :
    ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
        cut
        complex).map
      (HomologicalComplex.eval
        TraceAnalyticAdditiveCategoryObject
        (ComplexShape.up ℤ)
        degree)).Splitting :=
  let tail : ℕ :=
    Int.toNat (degree - cut)
  let tailDegree :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).f tail =
        degree :=
    ComplexShape.Embedding.f_eq_of_r_eq_some
      (e := TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
      (TraceAnalyticMotivicTStructure
        .truncGEEmbedding_r_eq_some_of_cut_le_degree
          cut
          degree
          hdegree)
  let nonboundary :
      ¬ (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE
        tail :=
    TraceAnalyticMotivicTStructure
      .truncGEEmbedding_not_boundary_of_cut_le_degree_ne
        cut
        degree
        hdegree
        hne
  let inverse :
      ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
          cut
          complex).map
        (HomologicalComplex.eval
          TraceAnalyticAdditiveCategoryObject
          (ComplexShape.up ℤ)
          degree)).X₃ ⟶
        ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
          cut
          complex).map
        (HomologicalComplex.eval
          TraceAnalyticAdditiveCategoryObject
          (ComplexShape.up ℤ)
          degree)).X₂ :=
    TraceAnalyticMotivicTStructure
      .additiveCochainDecompositionOffLowerTailUpperInverse
        cut
        complex
        tail
        degree
        tailDegree
        nonboundary
  TraceAnalyticMotivicTStructure
    .additiveCochainDecompositionOffLowerTailSplitting_of_upperMap_twoSidedInverse
      cut
      complex
      degree
      hnone
      inverse
      (TraceAnalyticMotivicTStructure
        .additiveCochainDecompositionOffLowerTailUpperInverse_s_g
          cut
          complex
          tail
          degree
          tailDegree
          nonboundary)
      (TraceAnalyticMotivicTStructure
        .additiveCochainDecompositionOffLowerTailUpperInverse_g_s
          cut
          complex
          tail
          degree
          tailDegree
          nonboundary)

/-- Nonboundary upper-tail splitting gives exactness of the evaluated
cochain-decomposition short complex. -/
theorem additiveCochainDecompositionUpperTailAwayExact
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (degree : ℤ)
    (hnone :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding
        (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
        none)
    (hdegree : cut ≤ degree)
    (hne : degree ≠ cut) :
    ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
        cut
        complex).map
      (HomologicalComplex.eval
        TraceAnalyticAdditiveCategoryObject
        (ComplexShape.up ℤ)
        degree)).Exact :=
  (TraceAnalyticMotivicTStructure
    .additiveCochainDecompositionUpperTailAwaySplitting
      cut
      complex
      degree
      hnone
      hdegree
      hne).exact

/-- Nonboundary upper-tail splitting makes the evaluated upper map epic. -/
theorem additiveCochainDecompositionUpperTailAwayEpi_g
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (degree : ℤ)
    (hnone :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding
        (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
        none)
    (hdegree : cut ≤ degree)
    (hne : degree ≠ cut) :
    Epi
      ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
          cut
          complex).map
        (HomologicalComplex.eval
          TraceAnalyticAdditiveCategoryObject
          (ComplexShape.up ℤ)
          degree)).g :=
  (TraceAnalyticMotivicTStructure
    .additiveCochainDecompositionUpperTailAwaySplitting
      cut
      complex
      degree
      hnone
      hdegree
      hne).epi_g

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
