import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.Maps.Owner

/-!
# Support separation for the normalized cochain decomposition

The normalized decomposition uses the lower cut `cut - 1` and the upper cut
`cut`.  This file proves the elementary integer separation of their embedded
tails: a degree of the form `cut - 1 - n` cannot also be of the form
`cut + m`.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

/-- The lower tail paired with `cut` and the upper tail at `cut` are disjoint
as integer degrees. -/
theorem decompositionLowerUpperTail_disjoint
    (cut : ℤ)
    (lowerTail upperTail : ℕ) :
    cut - 1 - (lowerTail : ℤ) ≠ cut + (upperTail : ℤ) :=
  fun equality => by
    let lowerTailNonnegative : 0 ≤ (lowerTail : ℤ) :=
      Int.ofNat_nonneg lowerTail
    let lowerDegreeLeBoundary :
        cut - 1 - (lowerTail : ℤ) ≤ cut - 1 :=
      sub_le_self (cut - 1) lowerTailNonnegative
    let upperTailNonnegative : 0 ≤ (upperTail : ℤ) :=
      Int.ofNat_nonneg upperTail
    let upperBoundaryLeDegree :
        cut ≤ cut + (upperTail : ℤ) :=
      le_add_of_nonneg_right upperTailNonnegative
    let cutLeLowerDegree :
        cut ≤ cut - 1 - (lowerTail : ℤ) :=
      equality.symm ▸ upperBoundaryLeDegree
    let cutLePrevious :
        cut ≤ cut - 1 :=
      le_trans cutLeLowerDegree lowerDegreeLeBoundary
    exact (not_lt_of_ge cutLePrevious) (sub_one_lt cut)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
