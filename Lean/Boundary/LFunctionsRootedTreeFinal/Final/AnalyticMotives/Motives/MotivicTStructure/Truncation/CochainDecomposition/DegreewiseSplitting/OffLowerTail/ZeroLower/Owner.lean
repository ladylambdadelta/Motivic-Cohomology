import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.DegreewiseSplitting.CaseSplit.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.Support.LowerInclusion.Owner

/-!
# Off-lower-tail degreewise splitting from a zero lower object

Outside the paired lower-tail embedding, the lower truncation object is zero.
This file packages the resulting off-tail splitting constructor: once the
upper map is supplied with a two-sided inverse at that degree, the lower
retraction is the zero map and the splitting identities follow.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- If the first object of a short complex is zero and the second map has a
two-sided inverse, then the short complex is split. -/
def shortComplexSplittingOfIsZeroX₁OfTwoSidedInverse
    {S : ShortComplex TraceAnalyticAdditiveCategoryObject}
    (hzero : CategoryTheory.Limits.IsZero S.X₁)
    (s : S.X₃ ⟶ S.X₂)
    (s_g : s ≫ S.g = 𝟙 S.X₃)
    (g_s : S.g ≫ s = 𝟙 S.X₂) :
    S.Splitting where
  r := 0
  s := s
  f_r :=
    Eq.trans
      (comp_zero S.f)
      (hzero.eq_of_src
        (0 : S.X₁ ⟶ S.X₁)
        (𝟙 S.X₁))
  s_g := s_g
  id :=
    Eq.trans
      (congrArg
        (fun term => term + S.g ≫ s)
        (zero_comp S.f))
      (Eq.trans
        (zero_add (S.g ≫ s))
        g_s)

/-- Off-lower-tail degreewise splitting of the normalized cochain decomposition
reduces to a two-sided inverse for its upper map at that degree. -/
def additiveCochainDecompositionOffLowerTailSplitting_of_upperMap_twoSidedInverse
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (degree : ℤ)
    (hnone :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding
        (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
        none)
    (s :
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
          degree)).X₂)
    (s_g :
      s ≫
        ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
            cut
            complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveCategoryObject
            (ComplexShape.up ℤ)
            degree)).g =
        𝟙 _)
    (g_s :
      ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
          cut
          complex).map
        (HomologicalComplex.eval
          TraceAnalyticAdditiveCategoryObject
          (ComplexShape.up ℤ)
          degree)).g ≫ s =
        𝟙 _) :
    ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
        cut
        complex).map
      (HomologicalComplex.eval
        TraceAnalyticAdditiveCategoryObject
        (ComplexShape.up ℤ)
        degree)).Splitting :=
  TraceAnalyticMotivicTStructure.shortComplexSplittingOfIsZeroX₁OfTwoSidedInverse
    (TraceAnalyticMotivicTStructure.additiveTruncLE_X_isZero_of_r_eq_none
      (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
      complex
      degree
      hnone)
    s
    s_g
    g_s

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
