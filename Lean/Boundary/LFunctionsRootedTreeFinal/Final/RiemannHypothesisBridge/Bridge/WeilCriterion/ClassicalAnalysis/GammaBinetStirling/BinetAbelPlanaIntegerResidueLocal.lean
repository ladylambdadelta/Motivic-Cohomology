import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaFiniteHeightSides

/-!
# Local integer residues for finite-height Abel-Plana

This file owns the normalized small-circle integral, removable residue
extension, residue-isolation radius, and local small-circle residue limit.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Normalized small-circle integral around an integer cotangent pole.

The factor `(2πi)⁻¹` records the residue-theorem normalization, so the
shrinking-circle limit is the local residue itself rather than `2πi` times the
residue. -/
noncomputable def Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral
    (w : ℂ)
    (c : ℂ)
    (ρ : ℝ) : ℂ :=
  ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
    circleIntegral
      (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
      c
      ρ

/-- Removable numerator for the logarithmic cotangent pole at the integer
`n`.

Away from the integer pole this is `(z-n) * rectangleIntegrand`; at the pole
it is filled by the already-owned local residue.  This is the object to which
the Cauchy integral formula applies in the small-circle residue calculation. -/
noncomputable def Complex.finiteAbelPlanaLogIntegerResidueExtension
    (w : ℂ)
    (n : ℕ)
    (z : ℂ) : ℂ :=
  if z = (n : ℂ) then
    Complex.finiteAbelPlanaLogIntegerResidue w n
  else
    (z - (n : ℂ)) *
      Complex.finiteAbelPlanaLogRectangleIntegrand w z

/-- Away from the integer pole, the removable numerator is the literal
centered rectangle integrand. -/
theorem Complex.finiteAbelPlana_log_integerResidueExtension_eq_centered_off_pole
    (w : ℂ)
    (n : ℕ)
    {z : ℂ}
    (hz : z ≠ (n : ℂ)) :
    Complex.finiteAbelPlanaLogIntegerResidueExtension w n z =
      (z - (n : ℂ)) *
        Complex.finiteAbelPlanaLogRectangleIntegrand w z := by
  dsimp [Complex.finiteAbelPlanaLogIntegerResidueExtension]
  exact if_neg hz

/-- At the integer pole, the removable numerator is filled by the local
residue. -/
theorem Complex.finiteAbelPlana_log_integerResidueExtension_at_pole
    (w : ℂ)
    (n : ℕ) :
    Complex.finiteAbelPlanaLogIntegerResidueExtension w n (n : ℂ) =
      Complex.finiteAbelPlanaLogIntegerResidue w n := by
  dsimp [Complex.finiteAbelPlanaLogIntegerResidueExtension]
  exact if_pos rfl

/-- Unfolding of the residue extension away from the pole. -/
theorem Complex.finiteAbelPlana_log_integerResidueExtension_unfold
    (w : ℂ)
    (n : ℕ)
    {z : ℂ}
    (hz : z ≠ (n : ℂ)) :
    Complex.finiteAbelPlanaLogIntegerResidueExtension w n z =
      (z - (n : ℂ)) *
        Complex.finiteAbelPlanaLogRectangleIntegrand w z := by
  exact Complex.finiteAbelPlana_log_integerResidueExtension_eq_centered_off_pole
    w n hz

/-- Unfolding of the residue extension at the pole. -/
theorem Complex.finiteAbelPlana_log_integerResidueExtension_unfold_at_pole
    (w : ℂ)
    (n : ℕ) :
    Complex.finiteAbelPlanaLogIntegerResidueExtension w n (n : ℂ) =
      Complex.finiteAbelPlanaLogIntegerResidue w n := by
  exact Complex.finiteAbelPlana_log_integerResidueExtension_at_pole w n

/-- The removable numerator tends to the local residue at the integer pole.

This is just the existing local residue theorem rewritten through the
removable-extension definition. -/
theorem Complex.finiteAbelPlana_log_integerResidueExtension_tendsto_at_pole
    {w : ℂ}
    (hw : 0 < w.re)
    (n : ℕ) :
    Tendsto
      (fun z : ℂ =>
        Complex.finiteAbelPlanaLogIntegerResidueExtension w n z)
      (𝓝[≠] (n : ℂ))
      (𝓝 (Complex.finiteAbelPlanaLogIntegerResidue w n)) := by
  have hraw :
      Tendsto
        (fun z : ℂ =>
          (z - (n : ℂ)) *
            Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (𝓝[≠] (n : ℂ))
        (𝓝 (Complex.finiteAbelPlanaLogIntegerResidue w n)) :=
    Complex.finiteAbelPlanaLogRectangleIntegrand_integerResidue_at_nat
      hw n
  have heq :
      (fun z : ℂ =>
        Complex.finiteAbelPlanaLogIntegerResidueExtension w n z) =ᶠ[𝓝[≠] (n : ℂ)]
      (fun z : ℂ =>
        (z - (n : ℂ)) *
          Complex.finiteAbelPlanaLogRectangleIntegrand w z) := by
    filter_upwards [eventually_mem_nhdsWithin] with z hz
    exact
      Complex.finiteAbelPlana_log_integerResidueExtension_eq_centered_off_pole
        w n hz
  exact hraw.congr' heq.symm

/-- Canonical small radius isolating the integer cotangent pole and keeping
`w+z` in the principal logarithm slit plane. -/
noncomputable def Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius
    (w : ℂ)
    (n : ℕ) : ℝ :=
  min ((1 : ℝ) / 2) ((w.re + (n : ℝ)) / 2)

/-- The canonical residue-isolation radius is positive in the right
half-plane. -/
theorem Complex.finiteAbelPlana_log_integerResidueIsolationRadius_pos
    {w : ℂ}
    (hw : 0 < w.re)
    (n : ℕ) :
    0 < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n := by
  have hhalf : 0 < (1 : ℝ) / 2 := by norm_num
  have hcenter : 0 < (w.re + (n : ℝ)) / 2 := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    exact half_pos (add_pos_of_pos_of_nonneg hw hn)
  exact lt_min hhalf hcenter

/-- The canonical residue-isolation radius is at most `1/2`, so it cannot
contain two distinct integer cotangent poles. -/
theorem Complex.finiteAbelPlana_log_integerResidueIsolationRadius_le_half
    (w : ℂ)
    (n : ℕ) :
    Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n ≤
      (1 : ℝ) / 2 := by
  exact min_le_left ((1 : ℝ) / 2) ((w.re + (n : ℝ)) / 2)

/-- Inside the residue-isolation disk, `w+z` stays in the principal slit
plane. -/
theorem Complex.finiteAbelPlana_log_mem_slitPlane_of_mem_integerResidueIsolationBall
    {w z : ℂ}
    (hw : 0 < w.re)
    (n : ℕ)
    (hz : z ∈ Metric.ball (n : ℂ)
      (Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)) :
    w + z ∈ Complex.slitPlane := by
  have hdist :
      ‖z - (n : ℂ)‖ <
        Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n := by
    simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hz
  have hre_dist : |z.re - (n : ℝ)| ≤ ‖z - (n : ℂ)‖ := by
    have hre_abs :
        |(z - (n : ℂ)).re| ≤ ‖z - (n : ℂ)‖ := by
      calc
        |(z - (n : ℂ)).re| ≤ Complex.abs (z - (n : ℂ)) :=
          Complex.abs_re_le_abs (z - (n : ℂ))
        _ = ‖z - (n : ℂ)‖ := by
          exact (Complex.norm_eq_abs (z - (n : ℂ))).symm
    have hre_eq : (z - (n : ℂ)).re = z.re - (n : ℝ) := by
      exact Complex.sub_re z (n : ℂ)
    exact hre_eq ▸ hre_abs
  have hlt_center :
      ‖z - (n : ℂ)‖ < (w.re + (n : ℝ)) / 2 :=
    lt_of_lt_of_le hdist (min_le_right _ _)
  have hreal_lower :
      -(‖z - (n : ℂ)‖) ≤ z.re - (n : ℝ) :=
    neg_le.mp (abs_le.mp hre_dist).1
  have hzre_lower :
      (n : ℝ) - ‖z - (n : ℂ)‖ ≤ z.re := by
    linarith
  have hsum_pos : 0 < w.re + z.re := by
    have hmain : 0 < w.re + ((n : ℝ) - ‖z - (n : ℂ)‖) := by
      have htwice : ‖z - (n : ℂ)‖ < w.re + (n : ℝ) := by
        linarith
      linarith
    exact lt_of_lt_of_le hmain (add_le_add_left hzre_lower w.re)
  exact Complex.mem_slitPlane_iff_not_le_zero.2 <| by
    exact Complex.not_le_zero_iff.2 <| Or.inl <| by
      calc
        0 < w.re + z.re := hsum_pos
        _ = (w + z).re := by
          exact (Complex.add_re w z).symm

/-- An integer point inside the residue-isolation disk centered at `n` is the
center integer itself. -/
theorem Complex.finiteAbelPlana_log_integer_eq_center_of_mem_integerResidueIsolationBall
    {w z : ℂ}
    (n : ℕ)
    {k : ℤ}
    (hz_int : z = (k : ℂ))
    (hz : z ∈ Metric.ball (n : ℂ)
      (Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)) :
    z = (n : ℂ) := by
  have hdist_radius :
      ‖z - (n : ℂ)‖ <
        Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n := by
    simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hz
  have hdist_half :
      ‖z - (n : ℂ)‖ < (1 : ℝ) / 2 :=
    lt_of_lt_of_le hdist_radius
      (Complex.finiteAbelPlana_log_integerResidueIsolationRadius_le_half w n)
  have hint_dist_half :
      ‖(k : ℂ) - (n : ℂ)‖ < (1 : ℝ) / 2 := by
    exact hz_int ▸ hdist_half
  have hint_dist_eq_abs :
      ‖(k : ℂ) - (n : ℂ)‖ = |(k : ℝ) - (n : ℝ)| := by
    have hcast :
        (k : ℂ) - (n : ℂ) = (((k : ℝ) - (n : ℝ)) : ℂ) := by
      norm_num
    calc
      ‖(k : ℂ) - (n : ℂ)‖ = ‖(((k : ℝ) - (n : ℝ)) : ℂ)‖ := by
        exact congrArg norm hcast
      _ = |(k : ℝ) - (n : ℝ)| := RCLike.norm_ofReal _
  have habs_half : |(k : ℝ) - (n : ℝ)| < (1 : ℝ) / 2 := by
    exact hint_dist_eq_abs ▸ hint_dist_half
  have hdiff_lt_one : |(k : ℝ) - (n : ℝ)| < (1 : ℝ) := by
    linarith
  have hdiff_zero : (k : ℤ) - (n : ℤ) = 0 := by
    by_contra hne
    have hnat_abs_pos : 0 < Int.natAbs ((k : ℤ) - (n : ℤ)) :=
      Int.natAbs_pos.mpr hne
    have hone_le_abs_int : (1 : ℝ) ≤ |(((k : ℤ) - (n : ℤ) : ℤ) : ℝ)| := by
      have hone_le_nat : 1 ≤ Int.natAbs ((k : ℤ) - (n : ℤ)) :=
        Nat.succ_le_of_lt hnat_abs_pos
      have hnat_abs_eq :
          |(((k : ℤ) - (n : ℤ) : ℤ) : ℝ)| =
            (Int.natAbs ((k : ℤ) - (n : ℤ)) : ℝ) := by
        exact (Int.cast_natAbs ((k : ℤ) - (n : ℤ)) (R := ℝ)).symm
      calc
        (1 : ℝ) ≤ (Int.natAbs ((k : ℤ) - (n : ℤ)) : ℝ) := by
          exact_mod_cast hone_le_nat
        _ = |(((k : ℤ) - (n : ℤ) : ℤ) : ℝ)| := hnat_abs_eq.symm
    have hcast_diff :
        (((k : ℤ) - (n : ℤ) : ℤ) : ℝ) = (k : ℝ) - (n : ℝ) := by
      norm_num
    have hone_le_abs : (1 : ℝ) ≤ |(k : ℝ) - (n : ℝ)| := by
      exact hcast_diff ▸ hone_le_abs_int
    exact not_lt_of_ge hone_le_abs hdiff_lt_one
  have hk_eq_n : (k : ℂ) = (n : ℂ) := by
    have hk_int_eq : (k : ℤ) = (n : ℤ) := sub_eq_zero.mp hdiff_zero
    exact_mod_cast hk_int_eq
  exact hz_int.trans hk_eq_n

/-- If `sin (πz)=0` inside the residue-isolation disk around `n`, then the
point is the center pole. -/
theorem Complex.finiteAbelPlana_log_eq_center_of_sin_pi_mul_eq_zero_of_mem_integerResidueIsolationBall
    {w z : ℂ}
    (n : ℕ)
    (hz : z ∈ Metric.ball (n : ℂ)
      (Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n))
    (hzero : Complex.sin ((Real.pi : ℂ) * z) = 0) :
    z = (n : ℂ) := by
  rcases Complex.sin_eq_zero_iff.mp hzero with ⟨k, hk⟩
  have hpi_ne : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hz_eq_int : z = (k : ℂ) := by
    have hmul :
        (Real.pi : ℂ) * z = (Real.pi : ℂ) * (k : ℂ) := by
      calc
        (Real.pi : ℂ) * z = (k : ℂ) * (Real.pi : ℂ) := hk
        _ = (Real.pi : ℂ) * (k : ℂ) := mul_comm (k : ℂ) (Real.pi : ℂ)
    exact mul_left_cancel₀ hpi_ne hmul
  exact
    Complex.finiteAbelPlana_log_integer_eq_center_of_mem_integerResidueIsolationBall
      n hz_eq_int hz

/-- In the residue-isolation disk, the only cotangent pole is the center
integer. -/
theorem Complex.finiteAbelPlana_log_sin_pi_mul_ne_zero_of_mem_integerResidueIsolationBall
    {w z : ℂ}
    (hw : 0 < w.re)
    (n : ℕ)
    (hz : z ∈ Metric.ball (n : ℂ)
      (Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n))
    (hzn : z ≠ (n : ℂ)) :
    Complex.sin ((Real.pi : ℂ) * z) ≠ 0 := by
  intro hzero
  exact hzn
    (Complex.finiteAbelPlana_log_eq_center_of_sin_pi_mul_eq_zero_of_mem_integerResidueIsolationBall
      n hz hzero)

/-- Off the integer pole, the removable residue extension is differentiable
because it agrees locally with the centered rectangle integrand. -/
theorem Complex.differentiableAt_finiteAbelPlanaLogIntegerResidueExtension_of_ne
    {w z : ℂ}
    (hw : 0 < w.re)
    (n : ℕ)
    (hzball : z ∈ Metric.ball (n : ℂ)
      (Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n))
    (hzn : z ≠ (n : ℂ)) :
    DifferentiableAt ℂ
      (fun z : ℂ =>
        Complex.finiteAbelPlanaLogIntegerResidueExtension w n z)
      z := by
  have hslit :
      w + z ∈ Complex.slitPlane :=
    Complex.finiteAbelPlana_log_mem_slitPlane_of_mem_integerResidueIsolationBall
      hw n hzball
  have hcot :
      Complex.sin ((Real.pi : ℂ) * z) ≠ 0 :=
    Complex.finiteAbelPlana_log_sin_pi_mul_ne_zero_of_mem_integerResidueIsolationBall
      hw n hzball hzn
  have hcentered :
      DifferentiableAt ℂ
        (fun z : ℂ =>
          (z - (n : ℂ)) *
            Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        z := by
    have hconst :
        DifferentiableAt ℂ (fun _z : ℂ => (n : ℂ)) z :=
      differentiableAt_const (c := (n : ℂ))
    exact
      ((differentiableAt_id.sub hconst).mul
        (Complex.differentiableAt_finiteAbelPlanaLogRectangleIntegrand
          hslit hcot))
  have heq :
      (fun z : ℂ =>
        Complex.finiteAbelPlanaLogIntegerResidueExtension w n z) =ᶠ[𝓝 z]
      (fun z : ℂ =>
        (z - (n : ℂ)) *
          Complex.finiteAbelPlanaLogRectangleIntegrand w z) := by
    filter_upwards [isOpen_ne.mem_nhds hzn] with y hy
    exact
      Complex.finiteAbelPlana_log_integerResidueExtension_eq_centered_off_pole
        w n hy
  exact hcentered.congr_of_eventuallyEq heq.symm

/-- The removable residue extension is continuous at the integer pole. -/
theorem Complex.continuousAt_finiteAbelPlanaLogIntegerResidueExtension_at_pole
    {w : ℂ}
    (hw : 0 < w.re)
    (n : ℕ) :
    ContinuousAt
      (fun z : ℂ =>
        Complex.finiteAbelPlanaLogIntegerResidueExtension w n z)
      (n : ℂ) := by
  have hpunctured :
      Tendsto
        (fun z : ℂ =>
          Complex.finiteAbelPlanaLogIntegerResidueExtension w n z)
        (𝓝[≠] (n : ℂ))
        (𝓝 (Complex.finiteAbelPlanaLogIntegerResidue w n)) :=
    Complex.finiteAbelPlana_log_integerResidueExtension_tendsto_at_pole
      hw n
  have hcenter :
      Complex.finiteAbelPlanaLogIntegerResidueExtension w n (n : ℂ) =
        Complex.finiteAbelPlanaLogIntegerResidue w n :=
    Complex.finiteAbelPlana_log_integerResidueExtension_at_pole w n
  rw [ContinuousAt]
  rw [hcenter]
  exact tendsto_nhds_of_tendsto_nhdsWithin hpunctured tendsto_const_nhds

/-- The removable residue extension is differentiable throughout a punctured
neighborhood of the integer pole. -/
theorem Complex.eventually_differentiableAt_finiteAbelPlanaLogIntegerResidueExtension_punctured
    {w : ℂ}
    (hw : 0 < w.re)
    (n : ℕ) :
    ∀ᶠ z in 𝓝[≠] (n : ℂ),
      DifferentiableAt ℂ
        (fun z : ℂ =>
          Complex.finiteAbelPlanaLogIntegerResidueExtension w n z)
        z := by
  have hR :
      0 < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n :=
    Complex.finiteAbelPlana_log_integerResidueIsolationRadius_pos hw n
  filter_upwards
    [self_mem_nhdsWithin,
      (Metric.ball_mem_nhds (n : ℂ) hR).filter_mono nhdsWithin_le_nhds] with z hzne hzball
  exact
    Complex.differentiableAt_finiteAbelPlanaLogIntegerResidueExtension_of_ne
      hw n hzball hzne

/-- At the integer pole, the removable residue extension is differentiable by
the removable-singularity theorem applied to the centered rectangle
integrand. -/
theorem Complex.differentiableAt_finiteAbelPlanaLogIntegerResidueExtension_at_pole
    {w : ℂ}
    (hw : 0 < w.re)
    (n : ℕ) :
    DifferentiableAt ℂ
      (fun z : ℂ =>
        Complex.finiteAbelPlanaLogIntegerResidueExtension w n z)
      (n : ℂ) := by
  exact
    (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      (Complex.eventually_differentiableAt_finiteAbelPlanaLogIntegerResidueExtension_punctured
        hw n)
      (Complex.continuousAt_finiteAbelPlanaLogIntegerResidueExtension_at_pole
        hw n)).differentiableAt

/-- The removable residue extension is differentiable on the residue
isolation disk.

This is the local removable-singularity theorem for the cotangent pole.  Away
from the center it is the centered rectangle integrand; at the center it is
filled by the local residue, and the existing local residue limit supplies
continuity at the center. -/
theorem Complex.differentiableOn_finiteAbelPlanaLogIntegerResidueExtension_isolationBall
    {w : ℂ}
    (hw : 0 < w.re)
    (n : ℕ) :
    DifferentiableOn ℂ
      (fun z : ℂ =>
        Complex.finiteAbelPlanaLogIntegerResidueExtension w n z)
      (Metric.ball (n : ℂ)
        (Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)) := by
  intro z hz
  by_cases hzn : z = (n : ℂ)
  · exact hzn ▸
      (Complex.differentiableAt_finiteAbelPlanaLogIntegerResidueExtension_at_pole
        hw n).differentiableWithinAt
  · exact
      (Complex.differentiableAt_finiteAbelPlanaLogIntegerResidueExtension_of_ne
        hw n hz hzn).differentiableWithinAt

/-- On a positive circle around the integer pole, the rectangle integrand is
the Cauchy kernel times the removable residue extension. -/
theorem Complex.finiteAbelPlana_log_rectangleIntegrand_eq_sub_inv_mul_residueExtension_on_circle
    (w : ℂ)
    (n : ℕ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    {z : ℂ}
    (hz : z ∈ Metric.sphere (n : ℂ) ρ) :
    Complex.finiteAbelPlanaLogRectangleIntegrand w z =
      (z - (n : ℂ))⁻¹ *
        Complex.finiteAbelPlanaLogIntegerResidueExtension w n z := by
  have hzne : z ≠ (n : ℂ) := by
    intro h
    have hdist_zero : dist z (n : ℂ) = 0 := by
      exact h ▸ dist_self (n : ℂ)
    have hdist_radius : dist z (n : ℂ) = ρ := by
      simpa [Metric.mem_sphere] using hz
    exact ne_of_gt hρ (hdist_radius ▸ hdist_zero)
  have hoff :
      Complex.finiteAbelPlanaLogIntegerResidueExtension w n z =
        (z - (n : ℂ)) *
          Complex.finiteAbelPlanaLogRectangleIntegrand w z :=
    Complex.finiteAbelPlana_log_integerResidueExtension_eq_centered_off_pole
      w n hzne
  calc
    Complex.finiteAbelPlanaLogRectangleIntegrand w z =
        (z - (n : ℂ))⁻¹ *
          ((z - (n : ℂ)) *
            Complex.finiteAbelPlanaLogRectangleIntegrand w z) := by
      have hsub : z - (n : ℂ) ≠ 0 := sub_ne_zero.2 hzne
      calc
        Complex.finiteAbelPlanaLogRectangleIntegrand w z =
            1 * Complex.finiteAbelPlanaLogRectangleIntegrand w z := by
          exact (one_mul _).symm
        _ =
            ((z - (n : ℂ))⁻¹ * (z - (n : ℂ))) *
              Complex.finiteAbelPlanaLogRectangleIntegrand w z := by
          exact congrArg
            (fun u : ℂ => u * Complex.finiteAbelPlanaLogRectangleIntegrand w z)
            (inv_mul_cancel₀ hsub).symm
        _ =
            (z - (n : ℂ))⁻¹ *
              ((z - (n : ℂ)) *
                Complex.finiteAbelPlanaLogRectangleIntegrand w z) := by
          exact mul_assoc _ _ _
    _ =
        (z - (n : ℂ))⁻¹ *
          Complex.finiteAbelPlanaLogIntegerResidueExtension w n z := by
      exact congrArg (fun u : ℂ => (z - (n : ℂ))⁻¹ * u) hoff.symm

/-- Positive radii small enough for the residue-isolation disk occur
eventually at `𝓝[>] 0`. -/
theorem Complex.eventually_pos_lt_finiteAbelPlanaLogIntegerResidueIsolationRadius
    {w : ℂ}
    (hw : 0 < w.re)
    (n : ℕ) :
    ∀ᶠ ρ : ℝ in 𝓝[>] (0 : ℝ),
      0 < ρ ∧
        ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n := by
  have hR :
      0 < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n :=
    Complex.finiteAbelPlana_log_integerResidueIsolationRadius_pos hw n
  exact
    (Ioo_mem_nhdsWithin_Ioi ⟨by linarith, hR⟩).mono
      (fun ρ hρ => ⟨hρ.1, hρ.2⟩)

/-- For every sufficiently small positive radius, the normalized small-circle
integral is exactly the residue. -/
theorem Complex.finiteAbelPlana_log_normalizedSmallCircleIntegral_eq_residue_of_pos_lt_isolation
    {w : ℂ}
    (hw : 0 < w.re)
    (n : ℕ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hρR : ρ <
      Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n) :
    Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w (n : ℂ) ρ =
      Complex.finiteAbelPlanaLogIntegerResidue w n := by
  let F : ℂ → ℂ :=
    fun z : ℂ => Complex.finiteAbelPlanaLogIntegerResidueExtension w n z
  have hclosed :
      Metric.closedBall (n : ℂ) ρ ⊆
        Metric.ball (n : ℂ)
          (Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n) :=
    Metric.closedBall_subset_ball hρR
  have hdiff_closed : DifferentiableOn ℂ F (Metric.closedBall (n : ℂ) ρ) :=
    (Complex.differentiableOn_finiteAbelPlanaLogIntegerResidueExtension_isolationBall
      hw n).mono hclosed
  have hcauchy :
      (∮ z in C((n : ℂ), ρ), (z - (n : ℂ))⁻¹ • F z) =
        (2 * ↑Real.pi * Complex.I : ℂ) • F (n : ℂ) :=
    hdiff_closed.circleIntegral_sub_inv_smul (Metric.mem_ball_self hρ)
  have hcircle :
      circleIntegral
          (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
          (n : ℂ)
          ρ =
        ∮ z in C((n : ℂ), ρ), (z - (n : ℂ))⁻¹ • F z := by
    exact
      circleIntegral.integral_congr hρ.le
        (fun z hz => by
          have hrewrite :
              Complex.finiteAbelPlanaLogRectangleIntegrand w z =
                (z - (n : ℂ))⁻¹ *
                  Complex.finiteAbelPlanaLogIntegerResidueExtension w n z :=
            Complex.finiteAbelPlana_log_rectangleIntegrand_eq_sub_inv_mul_residueExtension_on_circle
              w n hρ hz
          dsimp [F]
          simpa [smul_eq_mul] using hrewrite)
  have hcenter :
      F (n : ℂ) = Complex.finiteAbelPlanaLogIntegerResidue w n := by
    dsimp [F]
    exact Complex.finiteAbelPlana_log_integerResidueExtension_at_pole w n
  dsimp [Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral]
  calc
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        circleIntegral
          (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
          (n : ℂ)
          ρ =
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          (∮ z in C((n : ℂ), ρ), (z - (n : ℂ))⁻¹ • F z) := by
      exact congrArg
        (fun u : ℂ => ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ * u)
        hcircle
    _ =
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          ((2 * ↑Real.pi * Complex.I : ℂ) • F (n : ℂ)) := by
      exact congrArg
        (fun u : ℂ => ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ * u)
        hcauchy
    _ = F (n : ℂ) := by
      have htwo_pi_I_ne : ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
        refine mul_ne_zero ?_ Complex.I_ne_zero
        refine mul_ne_zero ?_ ?_
        · norm_num
        · exact_mod_cast Real.pi_ne_zero
      simpa [smul_eq_mul, mul_assoc] using
        (inv_mul_cancel₀ htwo_pi_I_ne : ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) = 1)
    _ = Complex.finiteAbelPlanaLogIntegerResidue w n := hcenter

/-- Local Cauchy-residue formula for a small circle around the integer pole.

This is the standard removable-singularity step in the cotangent residue
proof: after replacing `(z-n) * integrand` by its removable extension, Cauchy's
formula gives the normalized circle integral as the residue. -/
theorem Complex.finiteAbelPlana_log_normalizedSmallCircleIntegral_eq_residue_of_isolated
    {w : ℂ}
    (hw : 0 < w.re)
    (n : ℕ) :
    ∀ᶠ ρ : ℝ in 𝓝[>] (0 : ℝ),
      Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w (n : ℂ) ρ =
        Complex.finiteAbelPlanaLogIntegerResidue w n := by
  filter_upwards
    [Complex.eventually_pos_lt_finiteAbelPlanaLogIntegerResidueIsolationRadius
      hw n] with ρ hρ
  exact
    Complex.finiteAbelPlana_log_normalizedSmallCircleIntegral_eq_residue_of_pos_lt_isolation
      hw n hρ.1 hρ.2

/-- Sum of normalized small-circle integrals around all integer poles in the
finite Abel-Plana rectangle. -/
noncomputable def Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegralSum
    (N : ℕ)
    (w : ℂ)
    (ρ : ℝ) : ℂ :=
  ∑ n in Finset.range (N + 2),
    Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w (n : ℂ) ρ

/-- A single normalized small-circle integral converges to its local integer
residue. -/
theorem Complex.finiteAbelPlana_log_normalizedSmallCircleIntegral_tendsto_residue
    {w : ℂ}
    (hw : 0 < w.re)
    (n : ℕ) :
    Tendsto
      (fun ρ : ℝ =>
        Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w (n : ℂ) ρ)
      (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.finiteAbelPlanaLogIntegerResidue w n)) := by
  exact
    tendsto_const_nhds.congr'
      (Complex.finiteAbelPlana_log_normalizedSmallCircleIntegral_eq_residue_of_isolated
        hw n).symm

/-- Radius bound guaranteeing that the small circles around `0, ..., N+1`

end

end LFunctions
end Boundary
