import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseCanonicalRadiusIndexBound
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicCanonicalWindowAlgebra

/-!
# Canonical stationary budget with cutoff crossings removed

The Fourier packet majorant has two analytically different pieces.  The
stationary principal integral is modewise, while the two cutoff collars belong
to the reconstructed family and must be charged only once at each endpoint.
This owner records the stationary-only budget and its finite-family algebra.

For a canonical radius `r`, the left reciprocal tail costs at most `2r`, the
central window costs exactly `2r`, and the right reciprocal tail costs at most
`4r`.  Thus the stationary-only packet costs at most `8r`.  The inverse-square
root index owner then sums those radii without introducing a cardinality loss.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The part of the sharp stationary majorant that belongs to the principal
interval.  In particular, it does not contain the `4/3` cutoff-collar term. -/
def Complex.logarithmicPhasePoissonCanonicalStationaryOnlyBudget
    (t : ℝ) (m : ℤ) : ℝ :=
  Complex.logarithmicPhasePoissonCanonicalSharpLeftTailBudget t m +
    Complex.logarithmicPhasePoissonCanonicalWindowWidth t m +
      Complex.logarithmicPhasePoissonCanonicalSharpRightTailBudget t m

/-- Finite-family stationary-only budget. -/
def Complex.logarithmicPhasePoissonCanonicalStationaryOnlyFamilyBudget
    (t : ℝ) (M : Finset ℤ) : ℝ :=
  ∑ m ∈ M,
    Complex.logarithmicPhasePoissonCanonicalStationaryOnlyBudget t m

theorem Complex.logarithmicPhasePoissonCanonicalSharpMajorant_eq_crossing_add_stationaryOnly
    (t : ℝ) (a b m : ℤ) :
    Complex.logarithmicPhasePoissonCanonicalSharpStationaryMajorant t a b m =
      4 / 3 +
        Complex.logarithmicPhasePoissonCanonicalStationaryOnlyBudget t m := by
  unfold Complex.logarithmicPhasePoissonCanonicalSharpStationaryMajorant
  unfold Complex.logarithmicPhasePoissonCanonicalStationaryOnlyBudget
  exact rfl

theorem Complex.logarithmicPhasePoissonCanonicalStationaryOnlyBudget_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖) {m : ℤ} (hm : m < 0)
    (hleft :
      0 < Complex.logarithmicPhasePoissonCanonicalWindowLeft t m) :
    0 ≤ Complex.logarithmicPhasePoissonCanonicalStationaryOnlyBudget t m := by
  have hleftTail :=
    Complex.logarithmicPhasePoissonCanonicalSharpLeftTailBudget_nonneg
      t ht hm hleft
  have hwindow :=
    Complex.logarithmicPhasePoissonCanonicalWindowWidth_nonneg t m
  have hrightTail :=
    Complex.logarithmicPhasePoissonCanonicalSharpRightTailBudget_nonneg
      t ht hm
  unfold Complex.logarithmicPhasePoissonCanonicalStationaryOnlyBudget
  exact add_nonneg (add_nonneg hleftTail hwindow) hrightTail

theorem Complex.logarithmicPhasePoissonCanonicalStationaryOnlyFamilyBudget_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖) (M : Finset ℤ)
    (hMneg : ∀ m ∈ M, m < 0)
    (hMleft : ∀ m ∈ M,
      0 < Complex.logarithmicPhasePoissonCanonicalWindowLeft t m) :
    0 ≤ Complex.logarithmicPhasePoissonCanonicalStationaryOnlyFamilyBudget
      t M := by
  unfold Complex.logarithmicPhasePoissonCanonicalStationaryOnlyFamilyBudget
  exact Finset.sum_nonneg (fun m hm =>
    Complex.logarithmicPhasePoissonCanonicalStationaryOnlyBudget_nonneg
      t ht (hMneg m hm) (hMleft m hm))

theorem Real.two_mul_add_two_mul_eq_four_mul
    (x : ℝ) :
    2 * x + 2 * x = 4 * x := by
  have hfour : (4 : ℝ) = 2 + 2 := OfNat.ofNat_eq_ofNat
  exact Eq.trans (add_mul 2 2 x).symm (congrArg (fun z : ℝ => z * x) hfour.symm)

theorem Real.two_mul_add_two_mul_add_four_mul_eq_eight_mul
    (x : ℝ) :
    2 * x + 2 * x + 4 * x = 8 * x := by
  have hfirst := Real.two_mul_add_two_mul_eq_four_mul x
  have hsecond := Real.two_mul_add_two_mul_eq_four_mul x
  exact Eq.trans (congrArg (fun z : ℝ => z + 4 * x) hfirst)
    (Eq.trans hsecond (congrArg (fun z : ℝ => z * x) (by exact rfl)))

theorem Complex.logarithmicPhasePoissonCanonicalWindowWidth_eq_twoRadius
    (t : ℝ) (m : ℤ) :
    Complex.logarithmicPhasePoissonCanonicalWindowWidth t m =
      2 * Complex.logarithmicPhasePoissonCanonicalRadius t m := by
  unfold Complex.logarithmicPhasePoissonCanonicalWindowWidth
  unfold Complex.logarithmicPhasePoissonCanonicalWindowRight
  unfold Complex.logarithmicPhasePoissonCanonicalWindowLeft
  exact Complex.logarithmicPhaseCanonical_centralLength_eq_twoRadius t m

theorem Complex.logarithmicPhasePoissonCanonicalSharpLeftTailBudget_le_twoRadius
    (t : ℝ) (m : ℤ)
    (hgap :
      Complex.logarithmicPhaseLeftReciprocalGap t m
          (Complex.logarithmicPhasePoissonCanonicalWindowLeft t m) ≤
        Complex.logarithmicPhasePoissonCanonicalRadius t m) :
    Complex.logarithmicPhasePoissonCanonicalSharpLeftTailBudget t m ≤
      2 * Complex.logarithmicPhasePoissonCanonicalRadius t m := by
  unfold Complex.logarithmicPhasePoissonCanonicalSharpLeftTailBudget
  have hadd := add_le_add hgap hgap
  exact le_trans hadd
    (le_of_eq (two_mul
      (Complex.logarithmicPhasePoissonCanonicalRadius t m)).symm)

theorem Complex.logarithmicPhasePoissonCanonicalSharpRightTailBudget_le_fourRadius
    (t : ℝ) (m : ℤ)
    (hgap :
      Complex.logarithmicPhaseRightReciprocalGap t m
          (Complex.logarithmicPhasePoissonCanonicalWindowRight t m) ≤
        2 * Complex.logarithmicPhasePoissonCanonicalRadius t m) :
    Complex.logarithmicPhasePoissonCanonicalSharpRightTailBudget t m ≤
      4 * Complex.logarithmicPhasePoissonCanonicalRadius t m := by
  unfold Complex.logarithmicPhasePoissonCanonicalSharpRightTailBudget
  have hadd := add_le_add hgap hgap
  exact le_trans hadd
    (le_of_eq
      (Real.two_mul_add_two_mul_eq_four_mul
        (Complex.logarithmicPhasePoissonCanonicalRadius t m)))

theorem Complex.logarithmicPhasePoissonCanonicalStationaryOnlyBudget_le_eightRadius
    (t : ℝ) (m : ℤ)
    (hleft :
      Complex.logarithmicPhaseLeftReciprocalGap t m
          (Complex.logarithmicPhasePoissonCanonicalWindowLeft t m) ≤
        Complex.logarithmicPhasePoissonCanonicalRadius t m)
    (hright :
      Complex.logarithmicPhaseRightReciprocalGap t m
          (Complex.logarithmicPhasePoissonCanonicalWindowRight t m) ≤
        2 * Complex.logarithmicPhasePoissonCanonicalRadius t m) :
    Complex.logarithmicPhasePoissonCanonicalStationaryOnlyBudget t m ≤
      8 * Complex.logarithmicPhasePoissonCanonicalRadius t m := by
  have hleftBudget :=
    Complex.logarithmicPhasePoissonCanonicalSharpLeftTailBudget_le_twoRadius
      t m hleft
  have hwindow :=
    le_of_eq
      (Complex.logarithmicPhasePoissonCanonicalWindowWidth_eq_twoRadius
        t m)
  have hrightBudget :=
    Complex.logarithmicPhasePoissonCanonicalSharpRightTailBudget_le_fourRadius
      t m hright
  have hsum := add_le_add (add_le_add hleftBudget hwindow) hrightBudget
  unfold Complex.logarithmicPhasePoissonCanonicalStationaryOnlyBudget
  exact le_trans hsum
    (le_of_eq
      (Real.two_mul_add_two_mul_add_four_mul_eq_eight_mul
        (Complex.logarithmicPhasePoissonCanonicalRadius t m)))

theorem Complex.logarithmicPhasePoissonCanonicalStationaryOnlyFamilyBudget_le_eightRadii
    (t : ℝ) (M : Finset ℤ)
    (hleft : ∀ m ∈ M,
      Complex.logarithmicPhaseLeftReciprocalGap t m
          (Complex.logarithmicPhasePoissonCanonicalWindowLeft t m) ≤
        Complex.logarithmicPhasePoissonCanonicalRadius t m)
    (hright : ∀ m ∈ M,
      Complex.logarithmicPhaseRightReciprocalGap t m
          (Complex.logarithmicPhasePoissonCanonicalWindowRight t m) ≤
        2 * Complex.logarithmicPhasePoissonCanonicalRadius t m) :
    Complex.logarithmicPhasePoissonCanonicalStationaryOnlyFamilyBudget t M ≤
      ∑ m ∈ M,
        8 * Complex.logarithmicPhasePoissonCanonicalRadius t m := by
  unfold Complex.logarithmicPhasePoissonCanonicalStationaryOnlyFamilyBudget
  exact Finset.sum_le_sum (fun m hm =>
    Complex.logarithmicPhasePoissonCanonicalStationaryOnlyBudget_le_eightRadius
      t m (hleft m hm) (hright m hm))

theorem Complex.sum_eight_mul_canonicalRadius_eq_eight_mul_sum
    (t : ℝ) (M : Finset ℤ) :
    (∑ m ∈ M,
      8 * Complex.logarithmicPhasePoissonCanonicalRadius t m) =
      8 *
        (∑ m ∈ M,
          Complex.logarithmicPhasePoissonCanonicalRadius t m) := by
  exact Finset.mul_sum M
    (fun m : ℤ =>
      Complex.logarithmicPhasePoissonCanonicalRadius t m) 8

theorem Complex.logarithmicPhasePoissonCanonicalStationaryOnlyFamilyBudget_le_sixteen_scale_sqrt
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    (M : Finset ℤ) (N : ℕ)
    (hMneg : ∀ m ∈ M, m < 0)
    (hMupper : ∀ m ∈ M,
      Complex.logarithmicPhaseNegativeModeIndex m ≤ N)
    (hleft : ∀ m ∈ M,
      Complex.logarithmicPhaseLeftReciprocalGap t m
          (Complex.logarithmicPhasePoissonCanonicalWindowLeft t m) ≤
        Complex.logarithmicPhasePoissonCanonicalRadius t m)
    (hright : ∀ m ∈ M,
      Complex.logarithmicPhaseRightReciprocalGap t m
          (Complex.logarithmicPhasePoissonCanonicalWindowRight t m) ≤
        2 * Complex.logarithmicPhasePoissonCanonicalRadius t m) :
    Complex.logarithmicPhasePoissonCanonicalStationaryOnlyFamilyBudget t M ≤
      16 *
        (Complex.logarithmicPhaseBProcessScale t * Real.sqrt (N : ℝ)) := by
  have hstationary :=
    Complex.logarithmicPhasePoissonCanonicalStationaryOnlyFamilyBudget_le_eightRadii
      t M hleft hright
  have hradii :=
    Complex.sum_canonicalRadii_le_scale_mul_two_sqrt
      t ht M N hMneg hMupper
  have hscaled := mul_le_mul_of_nonneg_left hradii (OfNat.zero_le 8)
  have hsumEq := Complex.sum_eight_mul_canonicalRadius_eq_eight_mul_sum t M
  have hfirst := Eq.subst (motive := fun value : ℝ => value ≤ _)
    hsumEq.symm hscaled
  have hcombine := le_trans hstationary hfirst
  have hnormalize :
      8 *
          (Complex.logarithmicPhaseBProcessScale t *
            (2 * Real.sqrt (N : ℝ))) =
        16 *
          (Complex.logarithmicPhaseBProcessScale t *
            Real.sqrt (N : ℝ)) := by
    calc
      8 * (Complex.logarithmicPhaseBProcessScale t *
          (2 * Real.sqrt (N : ℝ))) =
          (8 * 2) *
            (Complex.logarithmicPhaseBProcessScale t *
              Real.sqrt (N : ℝ)) := by
            exact Eq.trans
              (mul_assoc 8
                (Complex.logarithmicPhaseBProcessScale t)
                (2 * Real.sqrt (N : ℝ)))
              (Eq.trans
                (congrArg (fun z : ℝ => 8 * z)
                  (Eq.trans
                    (mul_assoc
                      (Complex.logarithmicPhaseBProcessScale t) 2
                      (Real.sqrt (N : ℝ))).symm
                    (congrArg
                      (fun z : ℝ => z * Real.sqrt (N : ℝ))
                      (mul_comm
                        (Complex.logarithmicPhaseBProcessScale t) 2))))
                (mul_assoc 8 2
                  (Complex.logarithmicPhaseBProcessScale t *
                    Real.sqrt (N : ℝ))).symm)
      _ = 16 *
          (Complex.logarithmicPhaseBProcessScale t *
            Real.sqrt (N : ℝ)) := by exact rfl
  exact le_trans hcombine (le_of_eq hnormalize)

end

end LFunctions
end Boundary
