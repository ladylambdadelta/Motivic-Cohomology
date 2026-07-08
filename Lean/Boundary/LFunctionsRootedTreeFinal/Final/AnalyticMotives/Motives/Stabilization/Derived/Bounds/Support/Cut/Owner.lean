import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.LE.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.Bounds.Support.Owner

/-!
# Cut support criteria for derived analytic homological bounds

This file specializes the support-to-bound bridge to the two concrete integer
tail embeddings used by the analytic truncation calculus.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDerivedMotiveCategory

/-- The upper-tail embedding at `cut` has no degree strictly below `cut`. -/
theorem truncGEEmbedding_outside_below_cut
    (cut degree : ℤ)
    (hdegree : degree < cut)
    (upperTail : ℕ) :
    (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).f upperTail ≠
      degree :=
  show cut + (upperTail : ℤ) ≠ degree from
  fun equality =>
    let upperTailNonnegative : 0 ≤ (upperTail : ℤ) :=
      Int.ofNat_nonneg upperTail
    let cutLeImage :
        cut ≤ cut + (upperTail : ℤ) :=
      le_add_of_nonneg_right upperTailNonnegative
    let cutLeDegree :
        cut ≤ degree :=
      equality ▸ cutLeImage
    (not_lt_of_ge cutLeDegree) hdegree

/-- The lower-tail embedding at `cut` has no degree strictly above `cut`. -/
theorem truncLEEmbedding_outside_above_cut
    (cut degree : ℤ)
    (hdegree : cut < degree)
    (lowerTail : ℕ) :
    (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).f lowerTail ≠
      degree :=
  show cut - (lowerTail : ℤ) ≠ degree from
  fun equality =>
    let lowerTailNonnegative : 0 ≤ (lowerTail : ℤ) :=
      Int.ofNat_nonneg lowerTail
    let imageLeCut :
        cut - (lowerTail : ℤ) ≤ cut :=
      sub_le_self cut lowerTailNonnegative
    let degreeLeCut :
        degree ≤ cut :=
      equality.symm ▸ imageLeCut
    (not_lt_of_ge degreeLeCut) hdegree

/-- A represented complex supported on the concrete upper-tail embedding gives
a derived analytic motive homologically `≥ cut`. -/
theorem homologicalGE_objectOf_of_truncGEEmbedding_isSupported
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    [complex.IsSupported
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)] :
    TraceAnalyticDerivedMotiveCategory.HomologicalGE
      cut
      (TraceAnalyticDerivedMotiveCategory.objectOf complex) :=
  TraceAnalyticDerivedMotiveCategory.homologicalGE_objectOf_of_isSupported
    (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
    cut
    complex
    (fun degree hdegree upperTail =>
      TraceAnalyticDerivedMotiveCategory.truncGEEmbedding_outside_below_cut
        cut
        degree
        hdegree
        upperTail)

/-- A represented complex supported on the concrete lower-tail embedding gives
a derived analytic motive homologically `≤ cut`. -/
theorem homologicalLE_objectOf_of_truncLEEmbedding_isSupported
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    [complex.IsSupported
      (TraceAnalyticMotivicTStructure.truncLEEmbedding cut)] :
    TraceAnalyticDerivedMotiveCategory.HomologicalLE
      cut
      (TraceAnalyticDerivedMotiveCategory.objectOf complex) :=
  TraceAnalyticDerivedMotiveCategory.homologicalLE_objectOf_of_isSupported
    (TraceAnalyticMotivicTStructure.truncLEEmbedding cut)
    cut
    complex
    (fun degree hdegree lowerTail =>
      TraceAnalyticDerivedMotiveCategory.truncLEEmbedding_outside_above_cut
        cut
        degree
        hdegree
        lowerTail)

end TraceAnalyticDerivedMotiveCategory

end AnalyticMotives
end LFunctions
end Boundary
