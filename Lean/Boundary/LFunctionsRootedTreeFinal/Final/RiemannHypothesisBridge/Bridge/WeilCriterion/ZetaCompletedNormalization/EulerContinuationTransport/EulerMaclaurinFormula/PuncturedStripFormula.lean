import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.PuncturedStripContinuation

/-!
# Punctured-strip Euler-Maclaurin formula wrapper

This file owns the final raw-zeta Euler-Maclaurin wrappers that consume the
boundary-line analytic-continuation theorem from `PuncturedStripContinuation`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
open Filter MeasureTheory Set

/-- First-order Euler-Maclaurin tail identity for raw zeta at the owner cutoff. -/
theorem eulerMaclaurin_riemannZeta_tail_identity_with_bernoulliIntegralRemainder_standard
    (z : ℂ)
    (hz_one : 1 ≤ z.re)
    (hz_two : z.re ≤ 2)
    (hz_ne_one : z ≠ 1)
    [hz_half_plane_dec : Decidable (1 < z.re)] :
    riemannZeta z - eulerMaclaurinZetaFinitePart z =
        eulerMaclaurinZetaMainTerm z +
        eulerMaclaurinZetaEndpointTerm z +
        eulerMaclaurinZetaBernoulliIntegralRemainder z := by
  exact match hz_half_plane_dec with
  | isTrue hhalf_plane =>
      have hsplit :
          HasSum
            (fun n : ℕ =>
              if eulerMaclaurinPoleClearedZetaCutoff z < n then
                (1 : ℂ) / ((n : ℂ) ^ z)
              else
                0)
            (riemannZeta z - eulerMaclaurinZetaFinitePart z) :=
        eulerMaclaurin_riemannZeta_halfPlane_finite_split_tail_hasSum z hhalf_plane
      have htail :
          HasSum
            (fun n : ℕ =>
              if eulerMaclaurinPoleClearedZetaCutoff z < n then
                (1 : ℂ) / ((n : ℂ) ^ z)
              else
                0)
            (eulerMaclaurinZetaMainTerm z +
              eulerMaclaurinZetaEndpointTerm z +
              eulerMaclaurinZetaBernoulliIntegralRemainder z) :=
        eulerMaclaurin_riemannZeta_postCutoffTail_eulerMaclaurin_hasSum_standard
          z hz_one hz_two hhalf_plane
      hsplit.unique htail
  | isFalse hnot_half_plane =>
      have hz_re_le_one : z.re ≤ 1 :=
        le_of_not_gt hnot_half_plane
      have hz_re_eq_one : z.re = 1 :=
        le_antisymm hz_re_le_one hz_one
      eulerMaclaurin_riemannZeta_boundaryLine_tail_identity_with_bernoulliIntegralRemainder_standard
        z hz_re_eq_one hz_ne_one

/-- First-order Euler-Maclaurin formula for the raw Riemann zeta away from its
pole, with owner cutoff. -/
theorem eulerMaclaurin_riemannZeta_formula_with_bernoulliIntegralRemainder_standard
    (z : ℂ)
    (hz_one : 1 ≤ z.re)
    (hz_two : z.re ≤ 2)
    (hz_ne_one : z ≠ 1) :
    riemannZeta z =
      eulerMaclaurinZetaFinitePart z +
        eulerMaclaurinZetaMainTerm z +
        eulerMaclaurinZetaEndpointTerm z +
        eulerMaclaurinZetaBernoulliIntegralRemainder z := by
  have htail :
      riemannZeta z - eulerMaclaurinZetaFinitePart z =
        eulerMaclaurinZetaMainTerm z +
          eulerMaclaurinZetaEndpointTerm z +
          eulerMaclaurinZetaBernoulliIntegralRemainder z :=
    eulerMaclaurin_riemannZeta_tail_identity_with_bernoulliIntegralRemainder_standard
      z hz_one hz_two hz_ne_one
  have hraw :
      riemannZeta z =
        eulerMaclaurinZetaFinitePart z +
          (eulerMaclaurinZetaMainTerm z +
            eulerMaclaurinZetaEndpointTerm z +
            eulerMaclaurinZetaBernoulliIntegralRemainder z) :=
    complex_eq_add_of_sub_eq htail
  calc
    riemannZeta z =
        eulerMaclaurinZetaFinitePart z +
          (eulerMaclaurinZetaMainTerm z +
            eulerMaclaurinZetaEndpointTerm z +
            eulerMaclaurinZetaBernoulliIntegralRemainder z) :=
      hraw
    _ = eulerMaclaurinZetaFinitePart z +
          eulerMaclaurinZetaMainTerm z +
          eulerMaclaurinZetaEndpointTerm z +
          eulerMaclaurinZetaBernoulliIntegralRemainder z := by
      calc
        eulerMaclaurinZetaFinitePart z +
            (eulerMaclaurinZetaMainTerm z +
              eulerMaclaurinZetaEndpointTerm z +
              eulerMaclaurinZetaBernoulliIntegralRemainder z) =
            (eulerMaclaurinZetaFinitePart z +
              (eulerMaclaurinZetaMainTerm z +
                eulerMaclaurinZetaEndpointTerm z)) +
              eulerMaclaurinZetaBernoulliIntegralRemainder z := by
          exact (add_assoc
            (eulerMaclaurinZetaFinitePart z)
            (eulerMaclaurinZetaMainTerm z + eulerMaclaurinZetaEndpointTerm z)
            (eulerMaclaurinZetaBernoulliIntegralRemainder z)).symm
        _ = eulerMaclaurinZetaFinitePart z +
              eulerMaclaurinZetaMainTerm z +
              eulerMaclaurinZetaEndpointTerm z +
              eulerMaclaurinZetaBernoulliIntegralRemainder z := by
          exact congrArg
            (fun w : ℂ => w + eulerMaclaurinZetaBernoulliIntegralRemainder z)
            ((add_assoc
              (eulerMaclaurinZetaFinitePart z)
              (eulerMaclaurinZetaMainTerm z)
              (eulerMaclaurinZetaEndpointTerm z)).symm)

end
end LFunctions
end Boundary
