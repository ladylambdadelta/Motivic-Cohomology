import Mathlib.Algebra.Homology.Embedding.IsSupported
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.LE.Objects.Owner

/-!
# Support of lower analytic truncations

The concrete lower truncation is strictly supported on the lower-tail
embedding: outside that tail its degree object is zero.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Limits

namespace TraceAnalyticMotivicTStructure

/-- Lower analytic truncation is strictly supported on its lower-tail
embedding. -/
def additiveTruncLE_isStrictlySupported
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.additiveTruncLE cut complex)
      .IsStrictlySupported
        (TraceAnalyticMotivicTStructure.truncLEEmbedding cut) where
  isZero degree hdegree :=
    let htail :
        (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).r degree =
          none :=
      (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).r_eq_none
        degree
        hdegree
    let object_eq :
        (TraceAnalyticMotivicTStructure.additiveTruncLE cut complex).X degree =
          0 :=
      TraceAnalyticMotivicTStructure.additiveTruncLE_X_of_r_eq_none
        cut
        complex
        degree
        htail
    Eq.subst
      (motive := fun object =>
        IsZero object)
      (Eq.symm object_eq)
      (show IsZero
        (0 : TraceAnalyticAdditiveCategoryObject) from
        isZero_zero)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
