import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaFiniteMajorants

/-!
# Finite Abel-Plana upper-tail owners

This file owns the upper endpoint log-jump and upper-contour residual estimates.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology
open MeasureTheory

/-- The real coordinate is bounded by the complex norm. -/
theorem Complex.abs_re_le_norm_owner
    (z : ℂ) :
    |z.re| ≤ ‖z‖ := by
  exact RCLike.abs_re_le_norm z

/-- The real part of the upper endpoint line is the endpoint real part. -/
theorem Complex.binetAbelPlana_upperEndpointLine_re
    (w : ℂ)
    (N : ℕ)
    (s : ℝ) :
    (w + (N + 1 : ℂ) + (s : ℂ) * Complex.I).re =
      w.re + (N + 1 : ℝ) := by
  calc
    (w + (N + 1 : ℂ) + (s : ℂ) * Complex.I).re
        =
        (w + (N + 1 : ℂ)).re + ((s : ℂ) * Complex.I).re := by
          exact Complex.add_re (w + (N + 1 : ℂ)) ((s : ℂ) * Complex.I)
    _ = w.re + (N + 1 : ℝ) + ((s : ℂ) * Complex.I).re := by
          exact congrArg
            (fun r : ℝ => r + ((s : ℂ) * Complex.I).re)
            (Complex.add_re w (N + 1 : ℂ))
    _ = w.re + (N + 1 : ℝ) := by
          exact Real.add_right_zero_after_eq_zero
            w.re
            (N + 1 : ℝ)
            (((s : ℂ) * Complex.I).re)
            (Complex.real_cast_mul_I_re s)

/-- The upper endpoint line has norm bounded below by its positive real
coordinate. -/
theorem Complex.upperEndpointLine_endpoint_re_le_norm
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ)
    (s : ℝ) :
    w.re + (N + 1 : ℝ) ≤
      ‖w + (N + 1 : ℂ) + (s : ℂ) * Complex.I‖ := by
  let z : ℂ := w + (N + 1 : ℂ) + (s : ℂ) * Complex.I
  have hN_pos : 0 < (N + 1 : ℝ) := by
    exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg N) zero_lt_one
  have hre_pos : 0 < z.re := by
    have hre :
        z.re = w.re + (N + 1 : ℝ) :=
      Complex.binetAbelPlana_upperEndpointLine_re w N s
    exact hre.symm ▸ add_pos hw hN_pos
  have h_re_abs : z.re = |z.re| :=
    (abs_of_pos hre_pos).symm
  calc
    w.re + (N + 1 : ℝ)
        = z.re := by
          exact
            (Complex.binetAbelPlana_upperEndpointLine_re w N s).symm
    _ = |z.re| :=
          h_re_abs
    _ ≤ ‖z‖ :=
          Complex.abs_re_le_norm_owner z

/-- The upper endpoint vertical line lies in the principal logarithm slit
plane. -/
theorem Complex.binetAbelPlanaUpperEndpointLine_mem_slitPlane
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ)
    (s : ℝ) :
    w + (N + 1 : ℂ) + (s : ℂ) * Complex.I ∈ Complex.slitPlane := by
  have hre_pos :
      0 < (w + (N + 1 : ℂ) + (s : ℂ) * Complex.I).re :=
    Complex.binetAbelPlanaUpperLogJumpSegmentDenominator_re_pos hw N s
  exact Or.inl hre_pos

/-- Real derivative of the principal logarithm along the upper endpoint
vertical line. -/
theorem Complex.hasDerivAt_binetAbelPlanaUpperEndpointLine_log
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ)
    (s : ℝ) :
    HasDerivAt
      (fun u : ℝ =>
        Complex.log (w + (N + 1 : ℂ) + (u : ℂ) * Complex.I))
      (Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s)
      s := by
  exact
    Complex.hasDerivAt_binetAbelPlanaUpperEndpointLine_log_shared
      hw N s

/-- The upper endpoint differential-log integrand is interval-integrable on
every finite segment. -/
theorem Complex.intervalIntegrable_binetAbelPlanaUpperLogJumpSegmentIntegrand
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ)
    (a b : ℝ) :
    IntervalIntegrable
      (fun s : ℝ =>
        Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s)
      volume
      a
      b := by
  exact
    Complex.intervalIntegrable_binetAbelPlanaUpperLogJumpSegmentIntegrand_shared
      hw N a b

/-- Fundamental theorem of calculus for the upper endpoint logarithmic line. -/
theorem Complex.integral_binetAbelPlanaUpperLogJumpSegmentIntegrand_eq_log_sub
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ)
    (a b : ℝ) :
    ∫ s : ℝ in a..b,
        Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s =
      Complex.log (w + (N + 1 : ℂ) + (b : ℂ) * Complex.I) -
        Complex.log (w + (N + 1 : ℂ) + (a : ℂ) * Complex.I) := by
  exact
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _hs =>
        Complex.hasDerivAt_binetAbelPlanaUpperEndpointLine_log hw N s)
      (Complex.intervalIntegrable_binetAbelPlanaUpperLogJumpSegmentIntegrand
        hw N a b)

/-- Differential-log segment estimate for the upper Abel-Plana logarithmic
jump. -/
theorem Complex.binetAbelPlanaFiniteUpperLogJump_eq_segmentIntegral_owner
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
      Complex.binetAbelPlanaFiniteUpperLogJump N w t =
        ∫ s : ℝ in (-t)..t,
          Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s := by
  exact
    Complex.binetAbelPlanaFiniteUpperLogJump_eq_segmentIntegral_shared
      hw N

/-- Pointwise denominator estimate for the upper endpoint differential-log
segment integrand. -/
theorem Complex.norm_binetAbelPlanaUpperLogJumpSegmentIntegrand_le_endpoint_re_inv
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    ∀ s : ℝ,
      ‖Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s‖ ≤
        (w.re + (N + 1 : ℝ))⁻¹ := by
  exact fun s => by
    let z : ℂ := w + (N + 1 : ℂ) + (s : ℂ) * Complex.I
    have hN_pos : 0 < (N + 1 : ℝ) := by
      exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg N) zero_lt_one
    have hendpoint_pos : 0 < w.re + (N + 1 : ℝ) :=
      add_pos hw hN_pos
    have hendpoint_le_norm :
        w.re + (N + 1 : ℝ) ≤ ‖z‖ :=
      Complex.upperEndpointLine_endpoint_re_le_norm hw N s
    have hinv_le :
        ‖z‖⁻¹ ≤ (w.re + (N + 1 : ℝ))⁻¹ :=
      calc
        ‖z‖⁻¹ = (1 : ℝ) / ‖z‖ := by
          exact inv_eq_one_div ‖z‖
        _ ≤ (1 : ℝ) / (w.re + (N + 1 : ℝ)) :=
          one_div_le_one_div_of_le hendpoint_pos hendpoint_le_norm
        _ = (w.re + (N + 1 : ℝ))⁻¹ := by
          exact (inv_eq_one_div (w.re + (N + 1 : ℝ))).symm
    calc
      ‖Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s‖
          = ‖Complex.I / z‖ := by
            rfl
      _ = ‖Complex.I‖ / ‖z‖ := by
            exact norm_div Complex.I z
      _ = ‖z‖⁻¹ := by
            exact Complex.norm_I_div_eq_inv_norm z
      _ ≤ (w.re + (N + 1 : ℝ))⁻¹ :=
            hinv_le

/-- Interval-length integration of the pointwise segment-integrand bound. -/
theorem Complex.norm_binetAbelPlanaUpperLogJumpSegmentIntegral_le_length_mul_endpoint_re_inv
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
      ‖∫ s : ℝ in (-t)..t,
          Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s‖ ≤
        ((2 : ℝ) * t) * (w.re + (N + 1 : ℝ))⁻¹ := by
  exact
    (MeasureTheory.ae_restrict_mem measurableSet_Ioi).mono
      (fun t ht => by
        have ht_nonneg : 0 ≤ t := le_of_lt ht
        have hpoint :
            ∀ s : ℝ,
              ‖Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s‖ ≤
                (w.re + (N + 1 : ℝ))⁻¹ :=
          Complex.norm_binetAbelPlanaUpperLogJumpSegmentIntegrand_le_endpoint_re_inv
            hw N
        have hinterval :
            ‖∫ s : ℝ in (-t)..t,
                Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s‖ ≤
              (w.re + (N + 1 : ℝ))⁻¹ * |t - (-t)| :=
          intervalIntegral.norm_integral_le_of_norm_le_const
            (fun s hs => hpoint s)
        have habs : |t - (-t)| = (2 : ℝ) * t := by
          calc
            |t - (-t)| = |(2 : ℝ) * t| := by
              exact congrArg abs (Real.sub_neg_eq_two_mul t)
            _ = (2 : ℝ) * t := abs_of_nonneg (mul_nonneg (zero_le_two : (0 : ℝ) ≤ 2) ht_nonneg)
        calc
          ‖∫ s : ℝ in (-t)..t,
              Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s‖
              ≤ (w.re + (N + 1 : ℝ))⁻¹ * |t - (-t)| := hinterval
          _ = (w.re + (N + 1 : ℝ))⁻¹ * ((2 : ℝ) * t) := by
                exact congrArg
                  (fun x : ℝ => (w.re + (N + 1 : ℝ))⁻¹ * x)
                  habs
          _ = ((2 : ℝ) * t) * (w.re + (N + 1 : ℝ))⁻¹ := by
                exact mul_comm (w.re + (N + 1 : ℝ))⁻¹ ((2 : ℝ) * t))
    
/-- Norm bound for the differential-log segment integral. -/
theorem Complex.norm_binetAbelPlanaUpperLogJumpSegmentIntegral_le_two_mul_t_div_endpoint_re
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
      ‖∫ s : ℝ in (-t)..t,
          Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s‖ ≤
        ((2 : ℝ) * t) / (w.re + (N + 1 : ℝ)) := by
    have hlength :
        ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
          ‖∫ s : ℝ in (-t)..t,
              Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s‖ ≤
            ((2 : ℝ) * t) * (w.re + (N + 1 : ℝ))⁻¹ :=
      Complex.norm_binetAbelPlanaUpperLogJumpSegmentIntegral_le_length_mul_endpoint_re_inv
        hw N
    exact
      hlength.mono
        (fun t ht =>
          ht.trans_eq
            (div_eq_mul_inv ((2 : ℝ) * t) (w.re + (N + 1 : ℝ))).symm)

/-- Differential-log segment estimate for the upper Abel-Plana logarithmic
jump. -/
theorem Complex.norm_binetAbelPlanaFiniteUpperLogJump_le_two_mul_t_div_endpoint_re
    {w : ℂ}
    (hw : 0 < w.re) :
    ∀ N : ℕ,
      ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
        ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t‖ ≤
          ((2 : ℝ) * t) / (w.re + (N + 1 : ℝ)) := by
  exact fun N => by
    have hidentity :
        ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
          Complex.binetAbelPlanaFiniteUpperLogJump N w t =
            ∫ s : ℝ in (-t)..t,
              Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s :=
      Complex.binetAbelPlanaFiniteUpperLogJump_eq_segmentIntegral_owner hw N
    have hbound :
        ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
          ‖∫ s : ℝ in (-t)..t,
              Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s‖ ≤
            ((2 : ℝ) * t) / (w.re + (N + 1 : ℝ)) :=
      Complex.norm_binetAbelPlanaUpperLogJumpSegmentIntegral_le_two_mul_t_div_endpoint_re
        hw N
    exact
      (hidentity.and hbound).mono
        (fun _t ht_pair => ht_pair.1 ▸ ht_pair.2)

/-- Endpoint real-part comparison for the upper Abel-Plana logarithmic jump. -/
theorem Complex.two_mul_t_div_upperEndpoint_re_le_public_logJump_majorant
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    ∀ t : ℝ,
      t ∈ Set.Ioi (0 : ℝ) →
        ((2 : ℝ) * t) / (w.re + (N + 1 : ℝ)) ≤
          ((4 : ℝ) * (1 + ‖w‖) / (N + 1 : ℝ)) * t := by
  exact fun t ht => by
    have hN_pos : 0 < (N + 1 : ℝ) := by
      exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg N) zero_lt_one
    have hendpoint_pos : 0 < w.re + (N + 1 : ℝ) :=
      add_pos hw hN_pos
    have hone_le : 1 ≤ 1 + ‖w‖ :=
      le_add_of_nonneg_right (norm_nonneg w)
    have hbase :
        (2 : ℝ) / (w.re + (N + 1 : ℝ)) ≤
          (4 : ℝ) * (1 + ‖w‖) / (N + 1 : ℝ) := by
      have hden_le :
          (N + 1 : ℝ) ≤ w.re + (N + 1 : ℝ) :=
        le_add_of_nonneg_left hw.le
      have hrecip :
          (w.re + (N + 1 : ℝ))⁻¹ ≤ (N + 1 : ℝ)⁻¹ := by
        have hdiv :
            (1 : ℝ) / (w.re + (N + 1 : ℝ)) ≤
              1 / (N + 1 : ℝ) :=
          one_div_le_one_div_of_le hN_pos hden_le
        exact
          (inv_eq_one_div (w.re + (N + 1 : ℝ))).trans_le
            (hdiv.trans_eq
              (inv_eq_one_div (N + 1 : ℝ)).symm)
      have htwo :
          (2 : ℝ) / (w.re + (N + 1 : ℝ)) ≤
            2 / (N + 1 : ℝ) := by
        have hmul :
            (2 : ℝ) * (w.re + (N + 1 : ℝ))⁻¹ ≤
              2 * (N + 1 : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_left hrecip (zero_le_two : (0 : ℝ) ≤ 2)
        exact
          (div_eq_mul_inv (2 : ℝ) (w.re + (N + 1 : ℝ))).trans_le
            (hmul.trans_eq (div_eq_mul_inv (2 : ℝ) (N + 1 : ℝ)).symm)
      have htwo_le_four :
          (2 : ℝ) / (N + 1 : ℝ) ≤
            (4 : ℝ) * (1 + ‖w‖) / (N + 1 : ℝ) := by
        have hnum : (2 : ℝ) ≤ (4 : ℝ) * (1 + ‖w‖) := by
          exact Real.two_le_four_mul_of_one_le hone_le
        exact div_le_div_of_nonneg_right hnum hN_pos.le
      exact htwo.trans htwo_le_four
    calc
      ((2 : ℝ) * t) / (w.re + (N + 1 : ℝ))
          = ((2 : ℝ) / (w.re + (N + 1 : ℝ))) * t := by
            exact Real.two_mul_div_eq_div_mul t (w.re + (N + 1 : ℝ))
      _ ≤ ((4 : ℝ) * (1 + ‖w‖) / (N + 1 : ℝ)) * t := by
            exact mul_le_mul_of_nonneg_right hbase ht.le

/-- Upper-endpoint logarithmic jump bound along the finite Abel-Plana
vertical contour. -/
theorem Complex.norm_binetAbelPlanaFiniteUpperLogJump_le_endpoint_kernel
    {w : ℂ}
    (hw : 0 < w.re) :
    ∀ᶠ N : ℕ in Filter.atTop,
      ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
        ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t‖ ≤
          ((4 : ℝ) * (1 + ‖w‖) / (N + 1 : ℝ)) * t := by
  have hsegment :
      ∀ N : ℕ,
        ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
          ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t‖ ≤
            ((2 : ℝ) * t) / (w.re + (N + 1 : ℝ)) :=
    Complex.norm_binetAbelPlanaFiniteUpperLogJump_le_two_mul_t_div_endpoint_re
      hw
  exact
    Filter.Eventually.of_forall
      (fun N =>
        ((hsegment N).and (ae_restrict_mem measurableSet_Ioi)).mono
          (fun t ht_pair =>
            ht_pair.1.trans
              (Complex.two_mul_t_div_upperEndpoint_re_le_public_logJump_majorant
                hw N t ht_pair.2)))

/-- Pointwise majorization of the upper-contour residual integrand. -/
theorem Complex.norm_binetAbelPlanaFiniteUpperContourResidual_integrand_le_majorant
    {w : ℂ}
    (hw : 0 < w.re) :
    ∀ᶠ N : ℕ in Filter.atTop,
      ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
        ‖Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t‖ ≤
          ((4 : ℝ) * (1 + ‖w‖) / (N + 1 : ℝ)) *
            Complex.binetAbelPlanaVerticalKernelMajorant t := by
  have hjump :
      ∀ᶠ N : ℕ in Filter.atTop,
        ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
          ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t‖ ≤
            ((4 : ℝ) * (1 + ‖w‖) / (N + 1 : ℝ)) * t :=
    Complex.norm_binetAbelPlanaFiniteUpperLogJump_le_endpoint_kernel hw
  exact
    hjump.mono
      (fun N hN =>
        (hN.and (ae_restrict_mem measurableSet_Ioi)).mono
          (fun t ht_pair =>
            by
              have ht_jump :
                  ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t‖ ≤
                    ((4 : ℝ) * (1 + ‖w‖) / (N + 1 : ℝ)) * t :=
                ht_pair.1
              have ht_pos : 0 < t := ht_pair.2
              have hden_pos :
                  0 < Real.exp ((2 : ℝ) * Real.pi * t) - 1 :=
                Real.binetSecondFormula_exp_denominator_pos ht_pos
              have hintegrand_unfold :
                  Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t =
                    Complex.I *
                      (Complex.binetAbelPlanaFiniteUpperLogJump N w t /
                        (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)) :=
                Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand_unfold N w t
              calc
                    ‖Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t‖ =
                      ‖Complex.I *
                        (Complex.binetAbelPlanaFiniteUpperLogJump N w t /
                          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))‖ := by
                        exact congrArg norm hintegrand_unfold
                  _ =
                      ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t‖ /
                        (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
                        calc
                          ‖Complex.I *
                              (Complex.binetAbelPlanaFiniteUpperLogJump N w t /
                                (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))‖
                              = ‖Complex.I‖ *
                                  ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t /
                                    (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ := by
                                exact norm_mul _ _
                          _ = ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t /
                                (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ := by
                                calc
                                  ‖Complex.I‖ *
                                      ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t /
                                        (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ =
                                      1 *
                                        ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t /
                                          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ := by
                                    exact congrArg
                                      (fun r : ℝ =>
                                        r *
                                          ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t /
                                            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖)
                                      Complex.norm_I
                                  _ =
                                      ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t /
                                        (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ :=
                                    one_mul _
                          _ = ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t‖ /
                                ‖Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1‖ := by
                                exact norm_div _ _
                          _ = ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t‖ /
                                ‖Real.exp ((2 : ℝ) * Real.pi * t) - 1‖ := by
                                exact congrArg (fun x : ℝ => ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t‖ / x)
                                  (Complex.binetSecondFormula_exp_denominator_norm_eq t)
                          _ = ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t‖ /
                                (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
                                exact congrArg
                                  (fun x : ℝ => ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t‖ / x)
                                  (Real.binetSecondFormula_exp_denominator_norm_eq ht_pos)
                  _ ≤
                      (((4 : ℝ) * (1 + ‖w‖) / (N + 1 : ℝ)) * t) /
                        (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
                        exact div_le_div_of_nonneg_right ht_jump hden_pos.le
                  _ =
                      ((4 : ℝ) * (1 + ‖w‖) / (N + 1 : ℝ)) *
                        Complex.binetAbelPlanaVerticalKernelMajorant t := by
                        exact
                          Eq.trans
                            (Real.mul_mul_div_eq_mul_div
                              ((4 : ℝ) * (1 + ‖w‖) / (N + 1 : ℝ))
                              t
                              (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
                              (congrArg
                                (fun x : ℝ =>
                                  ((4 : ℝ) * (1 + ‖w‖) / (N + 1 : ℝ)) * x)
                                (Complex.binetAbelPlanaVerticalKernelMajorant_unfold t).symm)))

/-- Integral transport from a pointwise upper-contour integrand majorant to
the vertical-kernel mass. -/
theorem Complex.integral_norm_binetAbelPlanaFiniteUpperContourResidualIntegrand_le_kernelMass
    {w : ℂ}
    {N : ℕ}
    (hmajorant :
      ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
        ‖Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t‖ ≤
          ((4 : ℝ) * (1 + ‖w‖) / (N + 1 : ℝ)) *
            Complex.binetAbelPlanaVerticalKernelMajorant t) :
    ∫ t : ℝ in Set.Ioi (0 : ℝ),
        ‖Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t‖ ≤
      ((4 : ℝ) * (1 + ‖w‖) / (N + 1 : ℝ)) *
        Complex.binetAbelPlanaVerticalKernelMass := by
  have hcoef_nonneg :
      0 ≤ (4 : ℝ) * (1 + ‖w‖) / (N + 1 : ℝ) := by
    have hN_pos : 0 < (N + 1 : ℝ) := by
      exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg N) zero_lt_one
    have hfour_nonneg : (0 : ℝ) ≤ 4 := by
      exact le_trans zero_le_two Real.two_le_four
    exact div_nonneg
      (mul_nonneg hfour_nonneg
        (le_trans zero_le_one
          (le_add_of_nonneg_right (norm_nonneg w))))
      hN_pos.le
  have hmajorant_integrable :
      IntegrableOn
        (fun t : ℝ =>
          ((4 : ℝ) * (1 + ‖w‖) / (N + 1 : ℝ)) *
            Complex.binetAbelPlanaVerticalKernelMajorant t)
        (Set.Ioi (0 : ℝ)) :=
    Complex.binetAbelPlanaVerticalKernelMajorant_integrableOn.const_mul
      ((4 : ℝ) * (1 + ‖w‖) / (N + 1 : ℝ))
  have hintegrable :
      IntegrableOn
        (fun t : ℝ =>
          ‖Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t‖)
        (Set.Ioi (0 : ℝ)) :=
    Complex.integrableOn_norm_binetAbelPlanaFiniteUpperContourResidualIntegrand_of_majorant
      (w := w)
      (N := N)
      hmajorant
  have hmono :
      ∫ t : ℝ in Set.Ioi (0 : ℝ),
          ‖Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t‖ ≤
        ∫ t : ℝ in Set.Ioi (0 : ℝ),
          ((4 : ℝ) * (1 + ‖w‖) / (N + 1 : ℝ)) *
            Complex.binetAbelPlanaVerticalKernelMajorant t :=
    setIntegral_mono_ae_restrict
      hintegrable
      hmajorant_integrable
      hmajorant
  have hconst :
      ∫ t : ℝ in Set.Ioi (0 : ℝ),
          ((4 : ℝ) * (1 + ‖w‖) / (N + 1 : ℝ)) *
            Complex.binetAbelPlanaVerticalKernelMajorant t =
        ((4 : ℝ) * (1 + ‖w‖) / (N + 1 : ℝ)) *
          Complex.binetAbelPlanaVerticalKernelMass := by
    exact
      Eq.trans
        (integral_smul
          ((4 : ℝ) * (1 + ‖w‖) / (N + 1 : ℝ))
          (fun t : ℝ => Complex.binetAbelPlanaVerticalKernelMajorant t))
        (congrArg
          (fun x : ℝ => ((4 : ℝ) * (1 + ‖w‖) / (N + 1 : ℝ)) * x)
          Complex.binetAbelPlanaVerticalKernelMass_unfold.symm)
  exact hmono.trans_eq hconst

/-- Fixed-index integral comparison for the upper-contour residual. -/
theorem Complex.norm_binetAbelPlanaFiniteUpperContourResidual_le_kernelMass_of_integrand_majorant
    {w : ℂ}
    {N : ℕ}
    (hmajorant :
      ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
        ‖Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t‖ ≤
          ((4 : ℝ) * (1 + ‖w‖) / (N + 1 : ℝ)) *
            Complex.binetAbelPlanaVerticalKernelMajorant t) :
    ‖Complex.binetAbelPlanaFiniteUpperContourResidual N w‖ ≤
      ((4 : ℝ) * (1 + ‖w‖) / (N + 1 : ℝ)) *
        Complex.binetAbelPlanaVerticalKernelMass := by
  have hnorm_integral :
      ‖Complex.binetAbelPlanaFiniteUpperContourResidual N w‖ ≤
        ∫ t : ℝ in Set.Ioi (0 : ℝ),
          ‖Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t‖ := by
    calc
      ‖Complex.binetAbelPlanaFiniteUpperContourResidual N w‖ =
          ‖∫ t : ℝ in Set.Ioi (0 : ℝ),
              Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t‖ := by
        exact congrArg norm
          (Complex.binetAbelPlanaFiniteUpperContourResidual_eq_integral_integrand
            (N := N) (w := w))
      _ ≤ ∫ t : ℝ in Set.Ioi (0 : ℝ),
          ‖Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t‖ :=
        norm_integral_le_integral_norm _
  have hkernel_integral :
      ∫ t : ℝ in Set.Ioi (0 : ℝ),
          ‖Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t‖ ≤
        ((4 : ℝ) * (1 + ‖w‖) / (N + 1 : ℝ)) *
          Complex.binetAbelPlanaVerticalKernelMass :=
    Complex.integral_norm_binetAbelPlanaFiniteUpperContourResidualIntegrand_le_kernelMass
      (w := w)
      (N := N)
      hmajorant
  exact hnorm_integral.trans hkernel_integral

/-- Integral-level upper-contour residual estimate in terms of the vertical
kernel mass. -/
theorem Complex.norm_binetAbelPlanaFiniteUpperContourResidual_le_kernelMass_owner
    {w : ℂ}
    (hw : 0 < w.re) :
    ∀ᶠ N : ℕ in Filter.atTop,
      ‖Complex.binetAbelPlanaFiniteUpperContourResidual N w‖ ≤
        ((4 : ℝ) * (1 + ‖w‖) / (N + 1 : ℝ)) *
          Complex.binetAbelPlanaVerticalKernelMass := by
  have hpointwise :
      ∀ᶠ N : ℕ in Filter.atTop,
        ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
          ‖Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t‖ ≤
            ((4 : ℝ) * (1 + ‖w‖) / (N + 1 : ℝ)) *
              Complex.binetAbelPlanaVerticalKernelMajorant t :=
    Complex.norm_binetAbelPlanaFiniteUpperContourResidual_integrand_le_majorant
      hw
  exact
    hpointwise.mono
      (fun N hN =>
        Complex.norm_binetAbelPlanaFiniteUpperContourResidual_le_kernelMass_of_integrand_majorant
          (w := w)
          (N := N)
          hN)

/-- The kernel-mass bound is dominated by the upper-residual majorant. -/
theorem Complex.binetAbelPlanaFiniteUpperContourResidual_kernelMass_bound_le_majorant
    (w : ℂ)
    (N : ℕ) :
    ((4 : ℝ) * (1 + ‖w‖) / (N + 1 : ℝ)) *
        Complex.binetAbelPlanaVerticalKernelMass ≤
      Complex.binetAbelPlanaFiniteUpperContourResidualMajorant w N := by
  have hden_pos : 0 < (N + 1 : ℝ) := by
    exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg N) zero_lt_one
  have hone_le_scale : 1 ≤ 1 + ‖w‖ := by
    exact le_add_of_nonneg_right (norm_nonneg w)
  have hmass_le :
      Complex.binetAbelPlanaVerticalKernelMass ≤
        1 + |Complex.binetAbelPlanaVerticalKernelMass| := by
    exact
      (le_abs_self Complex.binetAbelPlanaVerticalKernelMass).trans
        (le_add_of_nonneg_left zero_le_one)
  have hcoef_nonneg :
      0 ≤ (4 : ℝ) * (1 + ‖w‖) / (N + 1 : ℝ) := by
    have hfour_nonneg : (0 : ℝ) ≤ 4 := by
      exact le_trans zero_le_two Real.two_le_four
    exact div_nonneg
      (mul_nonneg hfour_nonneg
        (le_trans zero_le_one hone_le_scale))
      hden_pos.le
  have hcoef_le :
      (4 : ℝ) * (1 + ‖w‖) ≤ 8 * (1 + ‖w‖) ^ 2 := by
    exact Real.four_mul_le_eight_mul_sq_of_one_le hone_le_scale
  have hscaled_mass :
      ((4 : ℝ) * (1 + ‖w‖) / (N + 1 : ℝ)) *
          Complex.binetAbelPlanaVerticalKernelMass ≤
        ((4 : ℝ) * (1 + ‖w‖) / (N + 1 : ℝ)) *
          (1 + |Complex.binetAbelPlanaVerticalKernelMass|) :=
    mul_le_mul_of_nonneg_left hmass_le hcoef_nonneg
  have hscaled_coef :
      ((4 : ℝ) * (1 + ‖w‖) / (N + 1 : ℝ)) *
          (1 + |Complex.binetAbelPlanaVerticalKernelMass|) ≤
        (8 * (1 + ‖w‖) ^ 2 / (N + 1 : ℝ)) *
          (1 + |Complex.binetAbelPlanaVerticalKernelMass|) := by
    have hdiv :
        (4 : ℝ) * (1 + ‖w‖) / (N + 1 : ℝ) ≤
          8 * (1 + ‖w‖) ^ 2 / (N + 1 : ℝ) :=
      div_le_div_of_nonneg_right hcoef_le hden_pos.le
    exact
      mul_le_mul_of_nonneg_right hdiv
        (add_nonneg zero_le_one (abs_nonneg _))
  exact
    hscaled_mass.trans
      (hscaled_coef.trans
        (le_of_eq
          (calc
            (8 * (1 + ‖w‖) ^ 2 / (N + 1 : ℝ)) *
                (1 + |Complex.binetAbelPlanaVerticalKernelMass|) =
                (8 * (1 + ‖w‖) ^ 2 * (N + 1 : ℝ)⁻¹) *
                  (1 + |Complex.binetAbelPlanaVerticalKernelMass|) := by
              exact congrArg
                (fun x : ℝ => x * (1 + |Complex.binetAbelPlanaVerticalKernelMass|))
                (div_eq_mul_inv (8 * (1 + ‖w‖) ^ 2) (N + 1 : ℝ))
            _ =
                8 * (1 + ‖w‖) ^ 2 *
                  ((N + 1 : ℝ)⁻¹ *
                    (1 + |Complex.binetAbelPlanaVerticalKernelMass|)) := by
              exact mul_assoc
                (8 * (1 + ‖w‖) ^ 2)
                (N + 1 : ℝ)⁻¹
                (1 + |Complex.binetAbelPlanaVerticalKernelMass|)
            _ =
                8 * (1 + ‖w‖) ^ 2 *
                  ((1 + |Complex.binetAbelPlanaVerticalKernelMass|) *
                    (N + 1 : ℝ)⁻¹) := by
              exact congrArg
                (fun x : ℝ => 8 * (1 + ‖w‖) ^ 2 * x)
                (mul_comm
                  (N + 1 : ℝ)⁻¹
                  (1 + |Complex.binetAbelPlanaVerticalKernelMass|))
            _ =
                8 * (1 + ‖w‖) ^ 2 *
                  ((1 + |Complex.binetAbelPlanaVerticalKernelMass|) /
                    (N + 1 : ℝ)) := by
              exact congrArg
                (fun x : ℝ => 8 * (1 + ‖w‖) ^ 2 * x)
                (div_eq_mul_inv
                  (1 + |Complex.binetAbelPlanaVerticalKernelMass|)
                  (N + 1 : ℝ)).symm
            _ =
                8 * (1 + ‖w‖) ^ 2 *
                  (1 + |Complex.binetAbelPlanaVerticalKernelMass|) /
                    (N + 1 : ℝ) := by
              exact
                (mul_div_assoc
                  (8 * (1 + ‖w‖) ^ 2)
                  (1 + |Complex.binetAbelPlanaVerticalKernelMass|)
                  (N + 1 : ℝ)).symm
            _ = Complex.binetAbelPlanaFiniteUpperContourResidualMajorant w N :=
              (Complex.binetAbelPlanaFiniteUpperContourResidualMajorant_unfold
                w N).symm)))

/-- Owner upper-contour residual estimate in majorant form. -/
theorem Complex.norm_binetAbelPlanaFiniteUpperContourResidual_le_majorant_owner
    {w : ℂ}
    (hw : 0 < w.re) :
    ∀ᶠ N : ℕ in Filter.atTop,
      ‖Complex.binetAbelPlanaFiniteUpperContourResidual N w‖ ≤
        Complex.binetAbelPlanaFiniteUpperContourResidualMajorant w N := by
  have hkernel :
      ∀ᶠ N : ℕ in Filter.atTop,
        ‖Complex.binetAbelPlanaFiniteUpperContourResidual N w‖ ≤
          (4 * (1 + ‖w‖) / (N + 1 : ℝ)) *
            Complex.binetAbelPlanaVerticalKernelMass :=
    Complex.norm_binetAbelPlanaFiniteUpperContourResidual_le_kernelMass_owner
      hw
  exact
    hkernel.mono
      (fun N hN =>
        hN.trans
          (Complex.binetAbelPlanaFiniteUpperContourResidual_kernelMass_bound_le_majorant
            w N))

end

end LFunctions
end Boundary
