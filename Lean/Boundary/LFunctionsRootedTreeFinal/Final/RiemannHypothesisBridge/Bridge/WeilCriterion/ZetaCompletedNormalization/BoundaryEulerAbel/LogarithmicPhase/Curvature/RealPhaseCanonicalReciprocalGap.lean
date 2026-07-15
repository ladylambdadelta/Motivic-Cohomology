import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseCanonicalStationaryOnlyBudget

/-!
# Reciprocal gaps at the canonical logarithmic window

Write `c` for the stationary center, `r = sqrt c`, and
`q = 2*pi*(-m)`.  At the canonical endpoints the corrected derivative is
exactly `-q*r/(c-r)` and `q*r/(c+r)`.  Since `q*c = ‖t‖`, `r*r = c`, and a
negative integral mode has `q >= 1`, both reciprocal gaps are controlled by
the radius.  This file discharges those facts from the canonical interior-mode
membership, leaving no analytic hypotheses in the finite-family estimate.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Real.sub_self_sub_eq_neg
    (c r : ℝ) :
    (c - r) - c = -r := by
  exact Eq.trans (sub_sub c r c)
    (Eq.trans
      (congrArg (fun z : ℝ => z - r) (sub_self c))
      (zero_sub r))

theorem Real.add_sub_self_eq
    (c r : ℝ) :
    (c + r) - c = r := by
  exact add_sub_cancel_left c r

theorem Real.neg_mul_neg_eq_mul
    (q r : ℝ) :
    -(q * -r) = q * r := by
  exact Eq.trans (neg_mul q r).symm (neg_neg (q * r))

theorem Real.inv_div_eq_div
    {numerator denominator : ℝ}
    (hnumerator : numerator ≠ 0)
    (hdenominator : denominator ≠ 0) :
    (numerator / denominator)⁻¹ = denominator / numerator := by
  exact inv_div numerator denominator

theorem Real.natCast_one_le_of_pos
    {k : ℕ} (hk : 0 < k) :
    (1 : ℝ) ≤ (k : ℝ) := by
  exact Nat.one_le_cast.mpr hk

theorem Real.norm_div_nat_le_norm
    (t : ℝ) {k : ℕ} (hk : 0 < k) :
    ‖t‖ / (k : ℝ) ≤ ‖t‖ := by
  have hkReal := Real.natCast_one_le_of_pos hk
  have hnorm := norm_nonneg t
  exact div_le_self hnorm hkReal

theorem Complex.logarithmicPhase_stationaryCenter_le_norm
    (t : ℝ) (ht : 1 ≤ ‖t‖) {m : ℤ} (hm : m < 0) :
    Complex.logarithmicPhaseFourierStationaryPoint t m ≤ ‖t‖ := by
  have hindex := Complex.logarithmicPhaseNegativeModeIndex_pos hm
  have hfirst :=
    Complex.logarithmicPhase_stationaryCenter_le_norm_div_modeIndex
      t ht hm
  have hsecond := Real.norm_div_nat_le_norm t hindex
  exact le_trans hfirst hsecond

theorem Complex.logarithmicPhaseCanonicalRadius_le_norm
    (t : ℝ) (ht : 1 ≤ ‖t‖) {m : ℤ} (hm : m < 0) :
    Complex.logarithmicPhasePoissonCanonicalRadius t m ≤ ‖t‖ := by
  have hcenter := Complex.logarithmicPhase_stationaryCenter_le_norm t ht hm
  have honeNorm : (1 : ℝ) ≤ ‖t‖ := ht
  have hnormNonneg := le_trans zero_le_one honeNorm
  have hnormSq : ‖t‖ ≤ ‖t‖ * ‖t‖ := by
    have hscaled := mul_le_mul_of_nonneg_right honeNorm hnormNonneg
    exact Eq.subst (motive := fun z : ℝ => z ≤ ‖t‖ * ‖t‖)
      (one_mul ‖t‖).symm hscaled
  have hradiusSq :=
    Complex.logarithmicPhasePoissonCanonicalRadius_sq t ht hm
  have hradiusNonneg :=
    Complex.logarithmicPhasePoissonCanonicalRadius_nonneg t m
  have hsq :
      Complex.logarithmicPhasePoissonCanonicalRadius t m *
          Complex.logarithmicPhasePoissonCanonicalRadius t m ≤
        ‖t‖ * ‖t‖ := by
    exact Eq.subst (motive := fun z : ℝ => z ≤ ‖t‖ * ‖t‖)
      hradiusSq.symm (le_trans hcenter hnormSq)
  exact (mul_self_le_mul_self_iff hradiusNonneg hnormNonneg).mp hsq

theorem Complex.logarithmicPhaseCanonical_angular_mul_radius_sq_eq_norm
    (t : ℝ) (ht : 1 ≤ ‖t‖) {m : ℤ} (hm : m < 0) :
    (2 * Real.pi * (-(m : ℝ))) *
        (Complex.logarithmicPhasePoissonCanonicalRadius t m *
          Complex.logarithmicPhasePoissonCanonicalRadius t m) =
      ‖t‖ := by
  have hsquare :=
    Complex.logarithmicPhasePoissonCanonicalRadius_sq t ht hm
  have hcenter := Complex.logarithmicPhaseAngular_mul_stationaryCenter t hm
  exact Eq.trans
    (congrArg
      (fun z : ℝ => (2 * Real.pi * (-(m : ℝ))) * z)
      hsquare)
    hcenter

theorem Complex.logarithmicPhaseCanonical_radius_mul_angular_mul_radius_eq_norm
    (t : ℝ) (ht : 1 ≤ ‖t‖) {m : ℤ} (hm : m < 0) :
    Complex.logarithmicPhasePoissonCanonicalRadius t m *
        ((2 * Real.pi * (-(m : ℝ))) *
          Complex.logarithmicPhasePoissonCanonicalRadius t m) =
      ‖t‖ := by
  have hbase :=
    Complex.logarithmicPhaseCanonical_angular_mul_radius_sq_eq_norm
      t ht hm
  have hreorder :
      Complex.logarithmicPhasePoissonCanonicalRadius t m *
          ((2 * Real.pi * (-(m : ℝ))) *
            Complex.logarithmicPhasePoissonCanonicalRadius t m) =
        (2 * Real.pi * (-(m : ℝ))) *
          (Complex.logarithmicPhasePoissonCanonicalRadius t m *
            Complex.logarithmicPhasePoissonCanonicalRadius t m) := by
    exact Eq.trans
      (mul_assoc
        (Complex.logarithmicPhasePoissonCanonicalRadius t m)
        (2 * Real.pi * (-(m : ℝ)))
        (Complex.logarithmicPhasePoissonCanonicalRadius t m)).symm
      (congrArg
        (fun z : ℝ =>
          z * Complex.logarithmicPhasePoissonCanonicalRadius t m)
        (mul_comm
          (Complex.logarithmicPhasePoissonCanonicalRadius t m)
          (2 * Real.pi * (-(m : ℝ)))))
  exact Eq.trans hreorder hbase

theorem Complex.logarithmicPhaseCanonical_leftDerivative_eq
    (t : ℝ) (ht : 1 ≤ ‖t‖) {m : ℤ} (hm : m < 0)
    (hleft : 0 < Complex.logarithmicPhasePoissonCanonicalWindowLeft t m) :
    Complex.logarithmicPhaseFourierTwistedDerivative t m
        (Complex.logarithmicPhasePoissonCanonicalWindowLeft t m) =
      -(2 * Real.pi * (-(m : ℝ)) *
          Complex.logarithmicPhasePoissonCanonicalRadius t m) /
        Complex.logarithmicPhasePoissonCanonicalWindowLeft t m := by
  have hfrequency :=
    Complex.logarithmicPhaseFourierTwistedDerivative_eq_frequencyGap_mul_stationaryDistance_div
      t hm hleft
  have hdifference :
      Complex.logarithmicPhasePoissonCanonicalWindowLeft t m -
          Complex.logarithmicPhaseFourierStationaryPoint t m =
        -Complex.logarithmicPhasePoissonCanonicalRadius t m := by
    unfold Complex.logarithmicPhasePoissonCanonicalWindowLeft
    exact Real.sub_self_sub_eq_neg _ _
  have hnumerator :
      (2 * Real.pi * (-(m : ℝ))) *
          (-Complex.logarithmicPhasePoissonCanonicalRadius t m) =
        -((2 * Real.pi * (-(m : ℝ))) *
          Complex.logarithmicPhasePoissonCanonicalRadius t m) := by
    exact mul_neg _ _
  exact Eq.trans hfrequency
    (Eq.trans
      (congrArg
        (fun z : ℝ =>
          (2 * Real.pi * (-(m : ℝ))) * z /
            Complex.logarithmicPhasePoissonCanonicalWindowLeft t m)
        hdifference)
      (congrArg
        (fun z : ℝ => z /
          Complex.logarithmicPhasePoissonCanonicalWindowLeft t m)
        hnumerator))

theorem Complex.logarithmicPhaseCanonical_neg_leftDerivative_eq
    (t : ℝ) (ht : 1 ≤ ‖t‖) {m : ℤ} (hm : m < 0)
    (hleft : 0 < Complex.logarithmicPhasePoissonCanonicalWindowLeft t m) :
    -Complex.logarithmicPhaseFourierTwistedDerivative t m
        (Complex.logarithmicPhasePoissonCanonicalWindowLeft t m) =
      (2 * Real.pi * (-(m : ℝ)) *
          Complex.logarithmicPhasePoissonCanonicalRadius t m) /
        Complex.logarithmicPhasePoissonCanonicalWindowLeft t m := by
  have hderivative :=
    Complex.logarithmicPhaseCanonical_leftDerivative_eq t ht hm hleft
  exact Eq.trans (congrArg Neg.neg hderivative)
    (neg_neg _)

theorem Complex.logarithmicPhaseCanonical_rightDerivative_eq
    (t : ℝ) (ht : 1 ≤ ‖t‖) {m : ℤ} (hm : m < 0) :
    Complex.logarithmicPhaseFourierTwistedDerivative t m
        (Complex.logarithmicPhasePoissonCanonicalWindowRight t m) =
      (2 * Real.pi * (-(m : ℝ)) *
          Complex.logarithmicPhasePoissonCanonicalRadius t m) /
        Complex.logarithmicPhasePoissonCanonicalWindowRight t m := by
  have hcenterPos :=
    Complex.logarithmicPhaseFourierStationaryPoint_pos t ht hm
  have hrightPos :
      0 < Complex.logarithmicPhasePoissonCanonicalWindowRight t m :=
    lt_of_lt_of_le hcenterPos
      (Complex.logarithmicPhasePoissonCanonicalWindowCenter_le_right t m)
  have hfrequency :=
    Complex.logarithmicPhaseFourierTwistedDerivative_eq_frequencyGap_mul_stationaryDistance_div
      t hm hrightPos
  have hdifference :
      Complex.logarithmicPhasePoissonCanonicalWindowRight t m -
          Complex.logarithmicPhaseFourierStationaryPoint t m =
        Complex.logarithmicPhasePoissonCanonicalRadius t m := by
    unfold Complex.logarithmicPhasePoissonCanonicalWindowRight
    exact Real.add_sub_self_eq _ _
  exact Eq.trans hfrequency
    (congrArg
      (fun z : ℝ =>
        (2 * Real.pi * (-(m : ℝ))) * z /
          Complex.logarithmicPhasePoissonCanonicalWindowRight t m)
      hdifference)

theorem Complex.logarithmicPhaseCanonical_leftReciprocalGap_eq_endpoint_div
    (t : ℝ) (ht : 1 ≤ ‖t‖) {m : ℤ} (hm : m < 0)
    (hleft : 0 < Complex.logarithmicPhasePoissonCanonicalWindowLeft t m) :
    Complex.logarithmicPhaseLeftReciprocalGap t m
        (Complex.logarithmicPhasePoissonCanonicalWindowLeft t m) =
      Complex.logarithmicPhasePoissonCanonicalWindowLeft t m /
        ((2 * Real.pi * (-(m : ℝ))) *
          Complex.logarithmicPhasePoissonCanonicalRadius t m) := by
  unfold Complex.logarithmicPhaseLeftReciprocalGap
  have hderivative :=
    Complex.logarithmicPhaseCanonical_neg_leftDerivative_eq t ht hm hleft
  have hangular :=
    Complex.logarithmicPhaseFourierStationaryPoint_denominator_pos m hm
  have hradius :=
    Complex.logarithmicPhasePoissonCanonicalRadius_pos t ht hm
  have hnumerator :
      (2 * Real.pi * (-(m : ℝ))) *
          Complex.logarithmicPhasePoissonCanonicalRadius t m ≠ 0 :=
    ne_of_gt (mul_pos hangular hradius)
  have hdenominator :
      Complex.logarithmicPhasePoissonCanonicalWindowLeft t m ≠ 0 :=
    ne_of_gt hleft
  exact Eq.trans (congrArg Inv.inv hderivative)
    (Real.inv_div_eq_div hnumerator hdenominator)

theorem Complex.logarithmicPhaseCanonical_rightReciprocalGap_eq_endpoint_div
    (t : ℝ) (ht : 1 ≤ ‖t‖) {m : ℤ} (hm : m < 0) :
    Complex.logarithmicPhaseRightReciprocalGap t m
        (Complex.logarithmicPhasePoissonCanonicalWindowRight t m) =
      Complex.logarithmicPhasePoissonCanonicalWindowRight t m /
        ((2 * Real.pi * (-(m : ℝ))) *
          Complex.logarithmicPhasePoissonCanonicalRadius t m) := by
  unfold Complex.logarithmicPhaseRightReciprocalGap
  have hderivative :=
    Complex.logarithmicPhaseCanonical_rightDerivative_eq t ht hm
  have hangular :=
    Complex.logarithmicPhaseFourierStationaryPoint_denominator_pos m hm
  have hradius :=
    Complex.logarithmicPhasePoissonCanonicalRadius_pos t ht hm
  have hcenter :=
    Complex.logarithmicPhaseFourierStationaryPoint_pos t ht hm
  have hright :
      0 < Complex.logarithmicPhasePoissonCanonicalWindowRight t m :=
    lt_of_lt_of_le hcenter
      (Complex.logarithmicPhasePoissonCanonicalWindowCenter_le_right t m)
  have hnumerator :
      (2 * Real.pi * (-(m : ℝ))) *
          Complex.logarithmicPhasePoissonCanonicalRadius t m ≠ 0 :=
    ne_of_gt (mul_pos hangular hradius)
  have hdenominator :
      Complex.logarithmicPhasePoissonCanonicalWindowRight t m ≠ 0 :=
    ne_of_gt hright
  exact Eq.trans (congrArg Inv.inv hderivative)
    (Real.inv_div_eq_div hnumerator hdenominator)

theorem Complex.logarithmicPhaseCanonical_leftEndpoint_le_norm
    (t : ℝ) (ht : 1 ≤ ‖t‖) {m : ℤ} (hm : m < 0) :
    Complex.logarithmicPhasePoissonCanonicalWindowLeft t m ≤ ‖t‖ := by
  have hradiusNonneg :=
    Complex.logarithmicPhasePoissonCanonicalRadius_nonneg t m
  have hleftCenter :
      Complex.logarithmicPhasePoissonCanonicalWindowLeft t m ≤
        Complex.logarithmicPhaseFourierStationaryPoint t m := by
    exact Complex.logarithmicPhasePoissonCanonicalWindowLeft_le_center t m
  exact le_trans hleftCenter
    (Complex.logarithmicPhase_stationaryCenter_le_norm t ht hm)

theorem Complex.logarithmicPhaseCanonical_rightEndpoint_le_two_norm
    (t : ℝ) (ht : 1 ≤ ‖t‖) {m : ℤ} (hm : m < 0) :
    Complex.logarithmicPhasePoissonCanonicalWindowRight t m ≤
      2 * ‖t‖ := by
  have hcenter := Complex.logarithmicPhase_stationaryCenter_le_norm t ht hm
  have hradius := Complex.logarithmicPhaseCanonicalRadius_le_norm t ht hm
  have hadd := add_le_add hcenter hradius
  unfold Complex.logarithmicPhasePoissonCanonicalWindowRight
  exact le_trans hadd (le_of_eq (two_mul ‖t‖).symm)

theorem Complex.logarithmicPhaseCanonical_leftReciprocalGap_le_radius
    (t : ℝ) (ht : 1 ≤ ‖t‖) {a b m : ℤ} (ha : 1 ≤ a)
    (hm : m ∈ Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b) :
    Complex.logarithmicPhaseLeftReciprocalGap t m
        (Complex.logarithmicPhasePoissonCanonicalWindowLeft t m) ≤
      Complex.logarithmicPhasePoissonCanonicalRadius t m := by
  have hmem :=
    (Complex.mem_logarithmicPhasePoissonCanonicalInteriorModes_iff
      t a b m).mp hm
  have hmNeg := hmem.2.1
  have hleft :=
    Complex.logarithmicPhasePoissonCanonicalWindowLeft_pos_of_mem
      t ht ha hm
  have heq :=
    Complex.logarithmicPhaseCanonical_leftReciprocalGap_eq_endpoint_div
      t ht hmNeg hleft
  have hangular :=
    Complex.logarithmicPhaseFourierStationaryPoint_denominator_pos m hmNeg
  have hradius :=
    Complex.logarithmicPhasePoissonCanonicalRadius_pos t ht hmNeg
  have hdenominator :
      0 < (2 * Real.pi * (-(m : ℝ))) *
        Complex.logarithmicPhasePoissonCanonicalRadius t m :=
    mul_pos hangular hradius
  have hendpoint :=
    Complex.logarithmicPhaseCanonical_leftEndpoint_le_norm t ht hmNeg
  have hproduct :=
    Complex.logarithmicPhaseCanonical_radius_mul_angular_mul_radius_eq_norm
      t ht hmNeg
  have hquotient :
      Complex.logarithmicPhasePoissonCanonicalWindowLeft t m /
          ((2 * Real.pi * (-(m : ℝ))) *
            Complex.logarithmicPhasePoissonCanonicalRadius t m) ≤
        Complex.logarithmicPhasePoissonCanonicalRadius t m := by
    exact (div_le_iff₀ hdenominator).mpr
      (le_trans hendpoint (le_of_eq hproduct.symm))
  exact Eq.subst (motive := fun z : ℝ => z ≤ _)
    heq.symm hquotient

theorem Complex.logarithmicPhaseCanonical_rightReciprocalGap_le_twoRadius
    (t : ℝ) (ht : 1 ≤ ‖t‖) {a b m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b) :
    Complex.logarithmicPhaseRightReciprocalGap t m
        (Complex.logarithmicPhasePoissonCanonicalWindowRight t m) ≤
      2 * Complex.logarithmicPhasePoissonCanonicalRadius t m := by
  have hmem :=
    (Complex.mem_logarithmicPhasePoissonCanonicalInteriorModes_iff
      t a b m).mp hm
  have hmNeg := hmem.2.1
  have heq :=
    Complex.logarithmicPhaseCanonical_rightReciprocalGap_eq_endpoint_div
      t ht hmNeg
  have hangular :=
    Complex.logarithmicPhaseFourierStationaryPoint_denominator_pos m hmNeg
  have hradius :=
    Complex.logarithmicPhasePoissonCanonicalRadius_pos t ht hmNeg
  have hdenominator :
      0 < (2 * Real.pi * (-(m : ℝ))) *
        Complex.logarithmicPhasePoissonCanonicalRadius t m :=
    mul_pos hangular hradius
  have hendpoint :=
    Complex.logarithmicPhaseCanonical_rightEndpoint_le_two_norm t ht hmNeg
  have hproduct :=
    Complex.logarithmicPhaseCanonical_radius_mul_angular_mul_radius_eq_norm
      t ht hmNeg
  have hscaledProduct :
      (2 * Complex.logarithmicPhasePoissonCanonicalRadius t m) *
          ((2 * Real.pi * (-(m : ℝ))) *
            Complex.logarithmicPhasePoissonCanonicalRadius t m) =
        2 * ‖t‖ := by
    exact Eq.trans
      (mul_assoc 2
        (Complex.logarithmicPhasePoissonCanonicalRadius t m)
        ((2 * Real.pi * (-(m : ℝ))) *
          Complex.logarithmicPhasePoissonCanonicalRadius t m))
      (congrArg (fun z : ℝ => 2 * z) hproduct)
  have hquotient :
      Complex.logarithmicPhasePoissonCanonicalWindowRight t m /
          ((2 * Real.pi * (-(m : ℝ))) *
            Complex.logarithmicPhasePoissonCanonicalRadius t m) ≤
        2 * Complex.logarithmicPhasePoissonCanonicalRadius t m := by
    exact (div_le_iff₀ hdenominator).mpr
      (le_trans hendpoint (le_of_eq hscaledProduct.symm))
  exact Eq.subst (motive := fun z : ℝ => z ≤ _)
    heq.symm hquotient

theorem Complex.logarithmicPhasePoissonCanonicalStationaryOnlyBudget_le_eightRadius_of_mem
    (t : ℝ) (ht : 1 ≤ ‖t‖) {a b m : ℤ} (ha : 1 ≤ a)
    (hm : m ∈ Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b) :
    Complex.logarithmicPhasePoissonCanonicalStationaryOnlyBudget t m ≤
      8 * Complex.logarithmicPhasePoissonCanonicalRadius t m := by
  have hleft :=
    Complex.logarithmicPhaseCanonical_leftReciprocalGap_le_radius
      t ht ha hm
  have hright :=
    Complex.logarithmicPhaseCanonical_rightReciprocalGap_le_twoRadius
      t ht hm
  exact
    Complex.logarithmicPhasePoissonCanonicalStationaryOnlyBudget_le_eightRadius
      t m hleft hright

theorem Complex.logarithmicPhasePoissonCanonicalInteriorStationaryBudget_le_sixteen_scale_sqrt
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ) (ha : 1 ≤ a) (N : ℕ)
    (hindex : ∀ m ∈
      Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b,
      Complex.logarithmicPhaseNegativeModeIndex m ≤ N) :
    Complex.logarithmicPhasePoissonCanonicalStationaryOnlyFamilyBudget t
        (Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b) ≤
      16 *
        (Complex.logarithmicPhaseBProcessScale t * Real.sqrt (N : ℝ)) := by
  let M := Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b
  have hMneg : ∀ m ∈ M, m < 0 := by
    intro m hm
    exact
      ((Complex.mem_logarithmicPhasePoissonCanonicalInteriorModes_iff
        t a b m).mp hm).2.1
  have hleft : ∀ m ∈ M,
      Complex.logarithmicPhaseLeftReciprocalGap t m
          (Complex.logarithmicPhasePoissonCanonicalWindowLeft t m) ≤
        Complex.logarithmicPhasePoissonCanonicalRadius t m := by
    intro m hm
    exact
      Complex.logarithmicPhaseCanonical_leftReciprocalGap_le_radius
        t ht ha hm
  have hright : ∀ m ∈ M,
      Complex.logarithmicPhaseRightReciprocalGap t m
          (Complex.logarithmicPhasePoissonCanonicalWindowRight t m) ≤
        2 * Complex.logarithmicPhasePoissonCanonicalRadius t m := by
    intro m hm
    exact
      Complex.logarithmicPhaseCanonical_rightReciprocalGap_le_twoRadius
        t ht hm
  exact
    Complex.logarithmicPhasePoissonCanonicalStationaryOnlyFamilyBudget_le_sixteen_scale_sqrt
      t ht M N hMneg hindex hleft hright

end

end LFunctions
end Boundary
