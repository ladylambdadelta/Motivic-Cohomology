import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.DegreewiseSplitting.CaseSplit.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.Support.UpperProjection.Owner

/-!
# Lower-tail degreewise splitting from a zero upper object

At a normalized lower-tail degree, the upper truncation object is zero.  This
file packages the resulting lower-tail splitting constructor: once the lower
map is supplied with a two-sided inverse at that degree, the upper section is
the zero map and the splitting identities follow.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- If the third object of a short complex is zero and the first map has a
two-sided inverse, then the short complex is split. -/
def shortComplexSplittingOfIsZeroX₃OfTwoSidedInverse
    {S : ShortComplex TraceAnalyticAdditiveCategoryObject}
    (hzero : CategoryTheory.Limits.IsZero S.X₃)
    (r : S.X₂ ⟶ S.X₁)
    (f_r : S.f ≫ r = 𝟙 S.X₁)
    (r_f : r ≫ S.f = 𝟙 S.X₂) :
    S.Splitting where
  r := r
  s := 0
  f_r := f_r
  s_g :=
    Eq.trans
      (zero_comp S.g)
      (hzero.eq_of_src
        (0 : S.X₃ ⟶ S.X₃)
        (𝟙 S.X₃))
  id :=
    Eq.trans
      (congrArg
        (fun term => r ≫ S.f + term)
        (comp_zero S.g))
      (Eq.trans
        (add_zero (r ≫ S.f))
        r_f)

/-- Lower-tail degreewise splitting of the normalized cochain decomposition
reduces to a two-sided inverse for its lower map at that degree. -/
def additiveCochainDecompositionLowerTailSplitting_of_lowerMap_twoSidedInverse
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (lowerTail : ℕ)
    (r :
      ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
          cut
          complex).map
        (HomologicalComplex.eval
          TraceAnalyticAdditiveCategoryObject
          (ComplexShape.up ℤ)
          (cut - 1 - (lowerTail : ℤ)))).X₂ ⟶
        ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
          cut
          complex).map
        (HomologicalComplex.eval
          TraceAnalyticAdditiveCategoryObject
          (ComplexShape.up ℤ)
          (cut - 1 - (lowerTail : ℤ)))).X₁)
    (f_r :
      ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
          cut
          complex).map
        (HomologicalComplex.eval
          TraceAnalyticAdditiveCategoryObject
          (ComplexShape.up ℤ)
          (cut - 1 - (lowerTail : ℤ)))).f ≫ r =
        𝟙 _)
    (r_f :
      r ≫
        ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
            cut
            complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveCategoryObject
            (ComplexShape.up ℤ)
            (cut - 1 - (lowerTail : ℤ)))).f =
        𝟙 _) :
    ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
        cut
        complex).map
      (HomologicalComplex.eval
        TraceAnalyticAdditiveCategoryObject
        (ComplexShape.up ℤ)
        (cut - 1 - (lowerTail : ℤ)))).Splitting :=
  TraceAnalyticMotivicTStructure.shortComplexSplittingOfIsZeroX₃OfTwoSidedInverse
    (TraceAnalyticMotivicTStructure.additiveTruncGE_X_isZero_of_decompositionLowerTail
      cut
      complex
      lowerTail)
    r
    f_r
    r_f

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
