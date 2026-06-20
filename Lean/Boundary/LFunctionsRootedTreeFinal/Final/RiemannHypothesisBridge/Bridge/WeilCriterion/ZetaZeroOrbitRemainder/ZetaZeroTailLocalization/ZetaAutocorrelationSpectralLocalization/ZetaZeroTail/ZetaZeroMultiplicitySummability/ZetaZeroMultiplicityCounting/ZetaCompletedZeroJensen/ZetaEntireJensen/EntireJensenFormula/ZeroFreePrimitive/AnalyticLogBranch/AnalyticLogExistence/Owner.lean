import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.ZeroFreePrimitive.AnalyticLogBranch.ExpReconstruction.Owner

/-!
# Analytic logarithm branch for zero-free Jensen disks

This owner layer was split from `ZeroFreePrimitive.AnalyticLogBranch.Owner` without changing public declaration names.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- The logarithmic derivative of a zero-free holomorphic function on a Jensen
closed disk has a primitive on that disk, normalized at the disk center.

This is the analytic integration step in the simply-connected disk proof:
on the convex disk, the closed holomorphic one-form `(G' / G) dz` has a
single-valued primitive.  Cf. Titchmarsh, *The Theory of Functions*, §5. -/
theorem entireFunction_zeroFreeOnClosedDisk_exists_logDerivPrimitive
    (G : ℂ → ℂ)
    {ρ : ℝ}
    (hρ : 1 ≤ ρ)
    (hG : ∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ G z)
    (hzero :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        G z ≠ 0) :
    ∃ P : ℂ → ℂ,
      (∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ P z) ∧
      (∀ z : ℂ, ‖z‖ ≤ ρ → deriv P z = deriv G z * (G z)⁻¹) ∧
      P 0 = 0 := by
  have hρ_nonneg : 0 ≤ ρ :=
    le_trans zero_le_one hρ
  have hstar :
      StarConvex ℝ (0 : ℂ) (Metric.closedBall (0 : ℂ) ρ) :=
    entireFunction_jensenClosedDisk_starConvex_center hρ_nonneg
  have hrecip :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        AnalyticAt ℂ (fun w : ℂ => (G w)⁻¹) z :=
    fun z hz =>
      entireFunction_zeroFreeOnClosedDisk_reciprocal_analyticAt
        G hG hzero hz
  exact
    entireFunction_convexClosedDisk_exists_logDerivPrimitive
      G hρ_nonneg hG hstar hrecip

/-- A normalized primitive of `G' / G` reconstructs the zero-free holomorphic
function by exponentiating and multiplying by the center value. -/
theorem entireFunction_zeroFreeOnClosedDisk_exp_logDerivPrimitive_reconstruct
    (G P : ℂ → ℂ)
    {ρ : ℝ}
    (hρ : 1 ≤ ρ)
    (hG : ∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ G z)
    (hzero :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        G z ≠ 0)
    (hP_an :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        AnalyticAt ℂ P z)
    (hP_deriv :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        deriv P z = deriv G z * (G z)⁻¹)
    (hP_zero : P 0 = 0) :
    ∀ z : ℂ,
      ‖z‖ ≤ ρ →
      G z = G 0 * Complex.exp (P z) := by
  have hρ_nonneg : 0 ≤ ρ :=
    le_trans zero_le_one hρ
  have hconvex : Convex ℝ (Metric.closedBall (0 : ℂ) ρ) :=
    entireFunction_jensenClosedDisk_convex ρ
  exact
    entireFunction_convexClosedDisk_exp_logDerivPrimitive_reconstruct
      G P hρ_nonneg hG hconvex hzero hP_an hP_deriv hP_zero

/-- A normalized primitive of the logarithmic derivative gives an analytic
logarithm branch after adding one logarithm of the nonzero center value. -/
theorem entireFunction_zeroFreeOnClosedDisk_exists_analyticLogBranch_of_logDerivPrimitive
    (G P : ℂ → ℂ)
    {ρ : ℝ}
    (hρ : 1 ≤ ρ)
    (hzero :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        G z ≠ 0)
    (hP_an :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        AnalyticAt ℂ P z)
    (hP_reconstruct :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        G z = G 0 * Complex.exp (P z)) :
    ∃ L : ℂ → ℂ,
      (∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ L z) ∧
      (∀ z : ℂ, ‖z‖ ≤ ρ → G z = Complex.exp (L z)) := by
  have hρ_nonneg : 0 ≤ ρ :=
    le_trans zero_le_one hρ
  have hzero_mem : ‖(0 : ℂ)‖ ≤ ρ :=
    Eq.subst
      (motive := fun x : ℝ => x ≤ ρ)
      (norm_zero : ‖(0 : ℂ)‖ = 0).symm
      hρ_nonneg
  have hG_zero_ne : G 0 ≠ 0 :=
    hzero 0 hzero_mem
  let L : ℂ → ℂ := fun z => Complex.log (G 0) + P z
  have hL_an :
      ∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ L z :=
    fun z hz =>
      analyticAt_const.add (hP_an z hz)
  have hL_log :
      ∀ z : ℂ, ‖z‖ ≤ ρ → G z = Complex.exp (L z) := by
    intro z hz
    have hrec : G z = G 0 * Complex.exp (P z) :=
      hP_reconstruct z hz
    have hcenter_exp : Complex.exp (Complex.log (G 0)) = G 0 :=
      Complex.exp_log hG_zero_ne
    calc
      G z = G 0 * Complex.exp (P z) :=
        hrec
      _ = Complex.exp (Complex.log (G 0)) * Complex.exp (P z) :=
        congrArg (fun w : ℂ => w * Complex.exp (P z)) hcenter_exp.symm
      _ = Complex.exp (Complex.log (G 0) + P z) :=
        (Complex.exp_add (Complex.log (G 0)) (P z)).symm
      _ = Complex.exp (L z) :=
        congrArg Complex.exp rfl
  exact ⟨L, hL_an, hL_log⟩

/-- Holomorphic logarithm existence on a zero-free simply connected Jensen disk.

This is the canonical analytic-log construction used by Jensen's formula: a
holomorphic zero-free map from the disk to `ℂˣ` lifts through
`Complex.exp : ℂ → ℂˣ`.  Cf. Titchmarsh, *The Theory of Functions*, §5. -/
theorem entireFunction_zeroFreeOnClosedDisk_exists_analyticLogBranch_from_simplyConnectedDisk
    (G : ℂ → ℂ)
    {ρ : ℝ}
    (hρ : 1 ≤ ρ)
    (hG : ∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ G z)
    (hzero :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        G z ≠ 0) :
    ∃ L : ℂ → ℂ,
      (∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ L z) ∧
      (∀ z : ℂ, ‖z‖ ≤ ρ → G z = Complex.exp (L z)) := by
  exact
    match entireFunction_zeroFreeOnClosedDisk_exists_logDerivPrimitive
        G hρ hG hzero with
    | Exists.intro P hP_data =>
        match hP_data with
        | And.intro hP_an hP_tail =>
            match hP_tail with
            | And.intro hP_deriv hP_zero =>
                have hP_reconstruct :
                    ∀ z : ℂ,
                      ‖z‖ ≤ ρ →
                        G z = G 0 * Complex.exp (P z) :=
                  entireFunction_zeroFreeOnClosedDisk_exp_logDerivPrimitive_reconstruct
                    G P hρ hG hzero hP_an hP_deriv hP_zero
                entireFunction_zeroFreeOnClosedDisk_exists_analyticLogBranch_of_logDerivPrimitive
                  G P hρ hzero hP_an hP_reconstruct

/-- The real part of any chosen analytic logarithm is the logarithm of the
norm of the original zero-free function. -/
theorem entireFunction_analyticLogBranch_re_eq_log_norm
    (G L : ℂ → ℂ)
    {ρ : ℝ}
    {z : ℂ}
    (hz : ‖z‖ ≤ ρ)
    (hlog :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        G w = Complex.exp (L w)) :
    (L z).re = Real.log ‖G z‖ := by
  have hzlog : G z = Complex.exp (L z) :=
    hlog z hz
  have hnorm_log :
      Real.log ‖G z‖ = Real.log ‖Complex.exp (L z)‖ := by
    exact congrArg (fun w : ℂ => Real.log ‖w‖) hzlog
  have hexp_log :
      Real.log ‖Complex.exp (L z)‖ = (L z).re :=
    complex_log_norm_exp_eq_re (L z)
  exact (Eq.trans hnorm_log hexp_log).symm

/-- The analytic logarithm branch supplied on a Jensen disk is automatically
normalized in real part at the center. -/
theorem entireFunction_analyticLogBranch_center_re_eq_log_norm
    (G L : ℂ → ℂ)
    {ρ : ℝ}
    (hρ : 1 ≤ ρ)
    (hlog :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        G w = Complex.exp (L w)) :
    (L 0).re = Real.log ‖G 0‖ := by
  have hρ_nonneg : 0 ≤ ρ :=
    le_trans zero_le_one hρ
  have hzero_mem : ‖(0 : ℂ)‖ ≤ ρ :=
    Eq.subst
      (motive := fun x : ℝ => x ≤ ρ)
      (norm_zero : ‖(0 : ℂ)‖ = 0).symm
      hρ_nonneg
  exact
    entireFunction_analyticLogBranch_re_eq_log_norm
      G L hzero_mem hlog

/-- Analytic-log existence on a simply connected Jensen disk.

This is the exact topological/complex-analytic owner root needed by Jensen's
formula: a holomorphic zero-free function on a neighborhood of the closed disk
has a holomorphic logarithm on that disk, with the real part normalized at the
center.  The intended proof is the classical lifting of `G : D → ℂˣ` through
`Complex.exp : ℂ → ℂˣ` on the simply connected disk, followed by the identity
`Real.log ‖Complex.exp w‖ = w.re`.  Cf. Titchmarsh, *The Theory of
Functions*, §5. -/
theorem entireFunction_zeroFreeOnClosedDisk_exists_analyticLog_from_simplyConnectedDisk
    (G : ℂ → ℂ)
    {ρ : ℝ}
    (hρ : 1 ≤ ρ)
    (hG : ∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ G z)
    (hzero :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        G z ≠ 0) :
    ∃ L : ℂ → ℂ,
    (∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ L z) ∧
    (∀ z : ℂ, ‖z‖ ≤ ρ → G z = Complex.exp (L z)) ∧
    (L 0).re = Real.log ‖G 0‖ := by
  exact
    match entireFunction_zeroFreeOnClosedDisk_exists_analyticLogBranch_from_simplyConnectedDisk
        G hρ hG hzero with
    | Exists.intro L hL_data =>
        match hL_data with
        | And.intro hL_an hL_log =>
            have hcenter :
                (L 0).re = Real.log ‖G 0‖ :=
              entireFunction_analyticLogBranch_center_re_eq_log_norm
                G L hρ hL_log
            Exists.intro L (And.intro hL_an (And.intro hL_log hcenter))

/-- A zero-free holomorphic function on a closed disk admits a holomorphic
logarithm on a neighborhood of that disk, normalized at the center.

This is the analytic-log existence step in Jensen's proof.  It follows by
applying the holomorphic logarithm construction to the zero-free image of the
simply connected disk; cf. Titchmarsh, *The Theory of Functions*, §5. -/
theorem entireFunction_zeroFreeOnClosedDisk_exists_analyticLog
    (G : ℂ → ℂ)
    (hG : ∀ z : ℂ, AnalyticAt ℂ G z)
    {ρ : ℝ}
    (hρ : 1 ≤ ρ)
    (hzero :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        G z ≠ 0) :
    ∃ L : ℂ → ℂ,
      (∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ L z) ∧
      (∀ z : ℂ, ‖z‖ ≤ ρ → G z = Complex.exp (L z)) ∧
      (L 0).re = Real.log ‖G 0‖ := by
  exact
    entireFunction_zeroFreeOnClosedDisk_exists_analyticLog_from_simplyConnectedDisk
      G hρ (fun z _hz => hG z) hzero



end
end LFunctions
end Boundary
