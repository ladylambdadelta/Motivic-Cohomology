import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.ZeroFreePrimitive.RadialFTC.Owner

/-!
# Analytic logarithm branch for zero-free Jensen disks

This owner layer was split from `ZeroFreePrimitive.AnalyticLogBranch.Owner` without changing public declaration names.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Canonical closed-ball logarithmic-derivative primitive theorem.

For a holomorphic zero-free function on a star-convex closed ball, the
logarithmic derivative has a normalized primitive on the ball.  The classical
construction is the path integral of `G' / G` along line segments, with
path-independence supplied by Cauchy's theorem on star-convex domains; cf.
Conway, *Functions of One Complex Variable I*, Ch. V, and Rudin, *Real and
Complex Analysis*, Ch. 10. -/
theorem complex_starConvexClosedBall_exists_logDerivPrimitive
    (G : ℂ → ℂ)
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (hG : ∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ G z)
    (hstar :
      StarConvex ℝ (0 : ℂ) (Metric.closedBall (0 : ℂ) ρ))
    (hrecip :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        AnalyticAt ℂ (fun w : ℂ => (G w)⁻¹) z) :
    ∃ P : ℂ → ℂ,
      (∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ P z) ∧
      (∀ z : ℂ, ‖z‖ ≤ ρ → deriv P z = deriv G z * (G z)⁻¹) ∧
      P 0 = 0 := by
  have hlog_an :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        AnalyticAt ℂ (fun w : ℂ => deriv G w * (G w)⁻¹) z :=
    complex_starConvexClosedBall_logDeriv_analyticAt G hG hrecip
  exact
    holomorphicOn_starConvexClosedBall_hasPrimitive
      (fun w : ℂ => deriv G w * (G w)⁻¹)
      hρ
      hstar
      hlog_an

/-- Primitive theorem for the logarithmic derivative on Jensen's convex disk.

The mathematical construction is the path integral
`P z = ∫_[0,z] G'(w) / G(w) dw` over the radial segment in the disk. Convexity
keeps every segment in the disk, analyticity of `G⁻¹` makes the logarithmic
derivative holomorphic there, and Cauchy's theorem on the convex domain gives
path independence. The normalization is the empty path at the center. Cf.
Titchmarsh, *The Theory of Functions*, §5. -/
theorem entireFunction_convexClosedDisk_exists_logDerivPrimitive
    (G : ℂ → ℂ)
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (hG : ∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ G z)
    (hstar :
      StarConvex ℝ (0 : ℂ) (Metric.closedBall (0 : ℂ) ρ))
    (hrecip :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        AnalyticAt ℂ (fun w : ℂ => (G w)⁻¹) z) :
    ∃ P : ℂ → ℂ,
      (∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ P z) ∧
      (∀ z : ℂ, ‖z‖ ≤ ρ → deriv P z = deriv G z * (G z)⁻¹) ∧
      P 0 = 0 := by
  exact
    complex_starConvexClosedBall_exists_logDerivPrimitive
      G hρ hG hstar hrecip

/-- Center-value comparison for the exponential reconstruction model. -/
theorem entireFunction_exp_logDerivPrimitive_reconstruct_center
    (G P : ℂ → ℂ)
    (hP_zero : P 0 = 0) :
    G 0 = G 0 * Complex.exp (P 0) := by
  calc
    G 0 = G 0 * 1 :=
      (mul_one (G 0)).symm
    _ = G 0 * Complex.exp 0 :=
      congrArg (fun w : ℂ => G 0 * w) (Complex.exp_zero.symm)
    _ = G 0 * Complex.exp (P 0) :=
      congrArg (fun w : ℂ => G 0 * Complex.exp w) hP_zero.symm

/-- Derivative of the exponential model attached to a primitive. -/
theorem entireFunction_exp_logDerivPrimitive_model_deriv_formula
    (G P : ℂ → ℂ)
    {ρ : ℝ}
    (hP_an :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        AnalyticAt ℂ P z)
    (hP_deriv :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        deriv P z = deriv G z * (G z)⁻¹) :
    ∀ z : ℂ,
      ‖z‖ ≤ ρ →
      deriv (fun w : ℂ => G 0 * Complex.exp (P w)) z =
        G 0 * (Complex.exp (P z) * (deriv G z * (G z)⁻¹)) := by
  intro z hz
  have hP_diff : DifferentiableAt ℂ P z :=
    (hP_an z hz).differentiableAt
  have hP_deriv_at :
      HasDerivAt P (deriv P z) z :=
    hP_diff.hasDerivAt
  have hexp_deriv_at :
      HasDerivAt
        (fun w : ℂ => Complex.exp (P w))
        (Complex.exp (P z) * deriv P z)
        z :=
    hP_deriv_at.cexp
  have hmodel_deriv_at :
      HasDerivAt
        (fun w : ℂ => G 0 * Complex.exp (P w))
        (G 0 * (Complex.exp (P z) * deriv P z))
        z :=
    hexp_deriv_at.const_mul (G 0)
  have hmodel_deriv :
      deriv (fun w : ℂ => G 0 * Complex.exp (P w)) z =
        G 0 * (Complex.exp (P z) * deriv P z) :=
    hmodel_deriv_at.deriv
  have hprimitive_deriv :
      deriv P z = deriv G z * (G z)⁻¹ :=
    hP_deriv z hz
  exact
    Eq.trans hmodel_deriv
      (congrArg
        (fun u : ℂ => G 0 * (Complex.exp (P z) * u))
        hprimitive_deriv)

/-- Pointwise algebra turning the logarithmic-derivative equation into equality
with the exponential model, once reconstruction of the value is known. -/
theorem entireFunction_exp_logDerivPrimitive_model_deriv_algebra
    (G P : ℂ → ℂ)
    {z : ℂ}
    (hzero_z : G z ≠ 0)
    (hreconstruct_z : G z = G 0 * Complex.exp (P z)) :
    deriv G z =
      G 0 * (Complex.exp (P z) * (deriv G z * (G z)⁻¹)) := by
  calc
    deriv G z = deriv G z * 1 :=
      (mul_one (deriv G z)).symm
    _ = deriv G z * (G z * (G z)⁻¹) :=
      congrArg (fun u : ℂ => deriv G z * u)
        (Eq.symm (mul_inv_cancel₀ hzero_z))
    _ = deriv G z * (G 0 * Complex.exp (P z) * (G z)⁻¹) :=
      congrArg
        (fun u : ℂ => deriv G z * (u * (G z)⁻¹))
        hreconstruct_z
    _ = deriv G z * (G 0 * (Complex.exp (P z) * (G z)⁻¹)) :=
      congrArg
        (fun u : ℂ => deriv G z * u)
        (mul_assoc (G 0) (Complex.exp (P z)) (G z)⁻¹)
    _ = (deriv G z * G 0) * (Complex.exp (P z) * (G z)⁻¹) :=
      (mul_assoc (deriv G z) (G 0) (Complex.exp (P z) * (G z)⁻¹)).symm
    _ = (G 0 * deriv G z) * (Complex.exp (P z) * (G z)⁻¹) :=
      congrArg
        (fun u : ℂ => u * (Complex.exp (P z) * (G z)⁻¹))
        (mul_comm (deriv G z) (G 0))
    _ = G 0 * (deriv G z * (Complex.exp (P z) * (G z)⁻¹)) :=
      mul_assoc (G 0) (deriv G z) (Complex.exp (P z) * (G z)⁻¹)
    _ = G 0 * ((deriv G z * Complex.exp (P z)) * (G z)⁻¹) :=
      congrArg
        (fun u : ℂ => G 0 * u)
        (mul_assoc (deriv G z) (Complex.exp (P z)) (G z)⁻¹).symm
    _ = G 0 * ((Complex.exp (P z) * deriv G z) * (G z)⁻¹) :=
      congrArg
        (fun u : ℂ => G 0 * (u * (G z)⁻¹))
        (mul_comm (deriv G z) (Complex.exp (P z)))
    _ = G 0 * (Complex.exp (P z) * (deriv G z * (G z)⁻¹)) :=
      congrArg
        (fun u : ℂ => G 0 * u)
        (mul_assoc (Complex.exp (P z)) (deriv G z) (G z)⁻¹)

/-- Core quotient derivative-zero calculation for exponential reconstruction
from a logarithmic-derivative primitive.

The quotient `G / (G 0 * exp P)` has zero derivative wherever the primitive
identity `P' = G'/G` holds and `G` is zero-free on the disk.  This is the
radial FTC input before any endpoint reconstruction is used. -/
theorem entireFunction_convexClosedDisk_exp_logDerivPrimitive_quotient_deriv_zero_and_center_core
    (G P : ℂ → ℂ)
    {ρ : ℝ}
    (hG :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        AnalyticAt ℂ G z)
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
    (hP_zero : P 0 = 0)
    {z : ℂ}
    (hz : ‖z‖ ≤ ρ) :
    deriv (fun w : ℂ => G w / (G 0 * Complex.exp (P w))) z = 0 ∧
      (fun w : ℂ => G w / (G 0 * Complex.exp (P w))) 0 = 1 := by
  have hρ_nonneg : 0 ≤ ρ :=
    le_trans (norm_nonneg z) hz
  have hzero_mem : ‖(0 : ℂ)‖ ≤ ρ := by
    calc
      ‖(0 : ℂ)‖ = 0 := norm_zero
      _ ≤ ρ := hρ_nonneg
  have hG0_ne : G 0 ≠ 0 :=
    hzero 0 hzero_mem
  have hGz_ne : G z ≠ 0 :=
    hzero z hz
  have hden_ne : G 0 * Complex.exp (P z) ≠ 0 := by
    exact mul_ne_zero hG0_ne (Complex.exp_ne_zero (P z))
  have hdiffG : DifferentiableAt ℂ G z :=
    (hG z hz).differentiableAt
  have hdiffP : DifferentiableAt ℂ P z :=
    (hP_an z hz).differentiableAt
  have hdiffExp : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (P w)) z :=
    hdiffP.cexp
  have hdiffModel : DifferentiableAt ℂ (fun w : ℂ => G 0 * Complex.exp (P w)) z :=
    hdiffExp.const_mul (G 0)
  have hlogExp : logDeriv (fun w : ℂ => Complex.exp (P w)) z = deriv P z := by
    calc
      logDeriv (fun w : ℂ => Complex.exp (P w)) z =
          logDeriv (Complex.exp) (P z) * deriv P z := by
            exact
              logDeriv_comp (f := Complex.exp) (g := P) (x := z)
                Complex.differentiableAt_exp hdiffP
      _ = 1 * deriv P z := by
            exact congrArg (fun t : ℂ => t * deriv P z)
              (congrArg (fun f : ℂ → ℂ => f (P z)) Complex.LogDeriv_exp)
      _ = deriv P z := by
            exact one_mul (deriv P z)
  have hlogModel : logDeriv (fun w : ℂ => G 0 * Complex.exp (P w)) z =
      deriv G z * (G z)⁻¹ := by
    calc
      logDeriv (fun w : ℂ => G 0 * Complex.exp (P w)) z =
          logDeriv (fun w : ℂ => Complex.exp (P w)) z := by
            exact logDeriv_const_mul (f := fun w : ℂ => Complex.exp (P w)) z (G 0) hG0_ne
      _ = deriv P z := hlogExp
      _ = deriv G z * (G z)⁻¹ := hP_deriv z hz
  have hlogG : logDeriv G z = deriv G z * (G z)⁻¹ := by
    calc
      logDeriv G z = deriv G z / G z := rfl
      _ = deriv G z * (G z)⁻¹ := by
            exact (div_eq_mul_inv _ _).symm
  have hsame :
      logDeriv G z = logDeriv (fun w : ℂ => G 0 * Complex.exp (P w)) z := by
    calc
      logDeriv G z = deriv G z * (G z)⁻¹ := hlogG
      _ = logDeriv (fun w : ℂ => G 0 * Complex.exp (P w)) z := hlogModel.symm
  have hlogQ :
      logDeriv (fun w : ℂ => G w / (G 0 * Complex.exp (P w))) z = 0 := by
    calc
      logDeriv (fun w : ℂ => G w / (G 0 * Complex.exp (P w))) z =
          logDeriv G z -
            logDeriv (fun w : ℂ => G 0 * Complex.exp (P w)) z := by
              exact
                logDeriv_div z hGz_ne hden_ne hdiffG hdiffModel
      _ = 0 := by
            exact sub_eq_zero.mpr hsame
  have hderiv_zero :
      deriv (fun w : ℂ => G w / (G 0 * Complex.exp (P w))) z = 0 := by
    have hquot_ne :
        G z / (G 0 * Complex.exp (P z)) ≠ 0 := by
      exact div_ne_zero hGz_ne hden_ne
    have hdiv_zero :
        deriv (fun w : ℂ => G w / (G 0 * Complex.exp (P w))) z /
          (G z / (G 0 * Complex.exp (P z))) = 0 := by
      calc
        deriv (fun w : ℂ => G w / (G 0 * Complex.exp (P w))) z /
            (G z / (G 0 * Complex.exp (P z))) =
          logDeriv (fun w : ℂ => G w / (G 0 * Complex.exp (P w))) z := by
            rfl
        _ = 0 := hlogQ
    exact
      match div_eq_zero_iff.mp hdiv_zero with
      | Or.inl hnum_zero => hnum_zero
      | Or.inr hden_zero => False.elim (hquot_ne hden_zero)
  have hcenter :
      (fun w : ℂ => G w / (G 0 * Complex.exp (P w))) 0 = 1 := by
    have hden0 : G 0 * Complex.exp (P 0) = G 0 := by
      calc
        G 0 * Complex.exp (P 0) = G 0 * Complex.exp 0 := by
          exact congrArg (fun t : ℂ => G 0 * Complex.exp t) hP_zero
        _ = G 0 * 1 := by
          exact congrArg (fun t : ℂ => G 0 * t) Complex.exp_zero
        _ = G 0 := by
          exact mul_one (G 0)
    calc
      (fun w : ℂ => G w / (G 0 * Complex.exp (P w))) 0 =
          G 0 / (G 0 * Complex.exp (P 0)) := rfl
      _ = G 0 / G 0 := by
          exact congrArg (fun t : ℂ => G 0 / t) hden0
      _ = 1 := by
          exact div_self hG0_ne
  exact ⟨hderiv_zero, hcenter⟩

/-- Analyticity of the exponential reconstruction quotient on the zero-free
closed disk. -/
theorem entireFunction_convexClosedDisk_exp_logDerivPrimitive_quotient_analyticAt
    (G P : ℂ → ℂ)
    {ρ : ℝ}
    (hG :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        AnalyticAt ℂ G z)
    (hzero :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        G z ≠ 0)
    (hP_an :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        AnalyticAt ℂ P z)
    (hρ : 0 ≤ ρ) :
    ∀ z : ℂ,
      ‖z‖ ≤ ρ →
      AnalyticAt ℂ (fun w : ℂ => G w / (G 0 * Complex.exp (P w))) z := by
  intro z hz
  have hzero_mem : ‖(0 : ℂ)‖ ≤ ρ := by
    calc
      ‖(0 : ℂ)‖ = 0 := norm_zero
      _ ≤ ρ := hρ
  have hG0_ne : G 0 ≠ 0 :=
    hzero 0 hzero_mem
  have hden_ne : G 0 * Complex.exp (P z) ≠ 0 := by
    exact mul_ne_zero hG0_ne (Complex.exp_ne_zero (P z))
  have hden_an : AnalyticAt ℂ (fun w : ℂ => G 0 * Complex.exp (P w)) z :=
    let hden_const_an : AnalyticAt ℂ (fun _w : ℂ => G 0) z :=
      analyticAt_const
    let hden_exp_an : AnalyticAt ℂ (fun w : ℂ => Complex.exp (P w)) z :=
      (hP_an z hz).cexp
    hden_const_an.mul hden_exp_an
  exact (hG z hz).div hden_an hden_ne

/-- Real interval derivative-zero constant theorem on `[0,1]`, in endpoint
form.

This is the one-dimensional FTC input used by the radial segment argument:
continuity on the closed interval plus right-derivative zero on `Ico 0 1`
forces the endpoint values to agree. -/
theorem complex_interval_endpoint_eq_of_hasDerivWithinAt_zero
    (φ : ℝ → ℂ)
    (hcont : ContinuousOn φ (Set.Icc (0 : ℝ) 1))
    (hderiv :
      ∀ t : ℝ,
        t ∈ Set.Ico (0 : ℝ) 1 →
        HasDerivWithinAt φ 0 (Set.Ici t) t) :
    φ 1 = φ 0 :=
  constant_of_has_deriv_right_zero hcont hderiv 1
    (Set.right_mem_Icc.mpr zero_le_one)

/-- The radial closed-disk difference function attached to two analytic
functions. -/
def entireFunction_convexClosedDisk_radialDifference
    (F H : ℂ → ℂ)
    (z : ℂ) :
    ℝ → ℂ :=
  fun t : ℝ => F ((t : ℂ) • z) - H ((t : ℂ) • z)

/-- The real affine segment from `0` to `z` is the same parametrization as
complex scalar multiplication by the real parameter. -/
theorem complex_lineMap_zero_eq_ofReal_smul
    (z : ℂ)
    (t : ℝ) :
    AffineMap.lineMap (0 : ℂ) z t = ((t : ℂ) • z) := by
  calc
    AffineMap.lineMap (0 : ℂ) z t =
        (1 - t) • (0 : ℂ) + t • z :=
      AffineMap.lineMap_apply_module (0 : ℂ) z t
    _ = 0 + t • z :=
      congrArg
        (fun u : ℂ => u + t • z)
        (show (1 - t : ℝ) • (0 : ℂ) = 0 from smul_zero (1 - t : ℝ))
    _ = t • z :=
      zero_add (t • z)
    _ = ((t : ℂ) • z) :=
      (algebraMap_smul ℂ t z).symm

/-- Convexity keeps the radial segment from the center to `z` inside the
closed disk. -/
theorem entireFunction_convexClosedDisk_radialSegment_mem
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (hconvex : Convex ℝ (Metric.closedBall (0 : ℂ) ρ))
    {z : ℂ}
    (hz : ‖z‖ ≤ ρ)
    {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ((t : ℂ) • z) ∈ Metric.closedBall (0 : ℂ) ρ := by
  have hzero_mem : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) ρ :=
    Metric.mem_closedBall_self hρ
  have hz_mem : z ∈ Metric.closedBall (0 : ℂ) ρ :=
    mem_closedBall_zero_iff.mpr hz
  have hline :
      AffineMap.lineMap (0 : ℂ) z t ∈ Metric.closedBall (0 : ℂ) ρ :=
    hconvex.mapsTo_lineMap hzero_mem hz_mem ht
  exact
    Eq.subst
      (motive := fun w : ℂ => w ∈ Metric.closedBall (0 : ℂ) ρ)
      (complex_lineMap_zero_eq_ofReal_smul z t)
      hline

/-- The radial parametrization is continuous on `[0,1]`. -/
theorem complex_radialSegment_continuousOn
    (z : ℂ) :
    ContinuousOn (fun t : ℝ => ((t : ℂ) • z)) (Set.Icc (0 : ℝ) 1) :=
  (Complex.continuous_ofReal.smul continuous_const).continuousOn

/-- Analyticity on the closed disk gives continuity of a function along a
radial segment in that disk. -/
theorem entireFunction_convexClosedDisk_radial_comp_continuousOn
    (F : ℂ → ℂ)
    {ρ : ℝ}
    (hF : ∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ F z)
    (hρ : 0 ≤ ρ)
    (hconvex : Convex ℝ (Metric.closedBall (0 : ℂ) ρ))
    {z : ℂ}
    (hz : ‖z‖ ≤ ρ) :
    ContinuousOn (fun t : ℝ => F ((t : ℂ) • z)) (Set.Icc (0 : ℝ) 1) := by
  have hF_cont :
      ContinuousOn F (Metric.closedBall (0 : ℂ) ρ) := by
    intro w hw
    exact (hF w (mem_closedBall_zero_iff.mp hw)).continuousAt.continuousWithinAt
  have hpath_cont :
      ContinuousOn (fun t : ℝ => ((t : ℂ) • z)) (Set.Icc (0 : ℝ) 1) :=
    complex_radialSegment_continuousOn z
  have hpath_mem :
      Set.MapsTo
        (fun t : ℝ => ((t : ℂ) • z))
        (Set.Icc (0 : ℝ) 1)
        (Metric.closedBall (0 : ℂ) ρ) := by
    intro t ht
    exact
      entireFunction_convexClosedDisk_radialSegment_mem hρ hconvex hz ht
  exact hF_cont.comp' hpath_cont hpath_mem

/-- The radial difference is continuous on `[0,1]`. -/
theorem entireFunction_convexClosedDisk_radialDifference_continuousOn
    (F H : ℂ → ℂ)
    {ρ : ℝ}
    (hF : ∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ F z)
    (hH : ∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ H z)
    (hρ : 0 ≤ ρ)
    (hconvex : Convex ℝ (Metric.closedBall (0 : ℂ) ρ))
    {z : ℂ}
    (hz : ‖z‖ ≤ ρ) :
    ContinuousOn
      (entireFunction_convexClosedDisk_radialDifference F H z)
      (Set.Icc (0 : ℝ) 1) := by
  have hF_cont :
      ContinuousOn (fun t : ℝ => F ((t : ℂ) • z)) (Set.Icc (0 : ℝ) 1) :=
    entireFunction_convexClosedDisk_radial_comp_continuousOn
      F hF hρ hconvex hz
  have hH_cont :
      ContinuousOn (fun t : ℝ => H ((t : ℂ) • z)) (Set.Icc (0 : ℝ) 1) :=
    entireFunction_convexClosedDisk_radial_comp_continuousOn
      H hH hρ hconvex hz
  exact hF_cont.sub hH_cont

/-- The radial path `t ↦ (t : ℂ) • z` has real derivative `z`. -/
theorem complex_radialSegment_hasDerivWithinAt
    (z : ℂ)
    (t : ℝ) :
    HasDerivWithinAt
      (fun s : ℝ => ((s : ℂ) • z))
      z
      (Set.Ici t)
      t := by
  have hmul_complex :
      HasDerivAt (fun w : ℂ => w * z) z (t : ℂ) :=
    hasDerivAt_mul_const z
  have hmul_real :
      HasDerivAt (fun s : ℝ => (s : ℂ) * z) z t :=
    hmul_complex.comp_ofReal
  have hradial_real :
      HasDerivAt (fun s : ℝ => ((s : ℂ) • z)) z t := by
    exact hmul_real
  exact hradial_real.hasDerivWithinAt

/-- Complex differentiability of `F` at a radial point, viewed as a real
Fréchet derivative. -/
theorem entireFunction_convexClosedDisk_radialPoint_hasFDerivAt_real
    (F : ℂ → ℂ)
    {ρ : ℝ}
    (hF : ∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ F z)
    (hρ : 0 ≤ ρ)
    (hconvex : Convex ℝ (Metric.closedBall (0 : ℂ) ρ))
    {z : ℂ}
    (hz : ‖z‖ ≤ ρ)
    {t : ℝ}
    (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    HasFDerivAt
      F
      ((deriv F ((t : ℂ) • z)) • (1 : ℂ →L[ℝ] ℂ))
      ((t : ℂ) • z) := by
  have hpoint_mem :
      ((t : ℂ) • z) ∈ Metric.closedBall (0 : ℂ) ρ :=
    entireFunction_convexClosedDisk_radialSegment_mem
      hρ hconvex hz (Set.Ico_subset_Icc_self ht)
  have hpoint_norm : ‖((t : ℂ) • z)‖ ≤ ρ :=
    mem_closedBall_zero_iff.mp hpoint_mem
  have hcomplex :
      HasDerivAt F (deriv F ((t : ℂ) • z)) ((t : ℂ) • z) :=
    (hF ((t : ℂ) • z) hpoint_norm).differentiableAt.hasDerivAt
  exact hcomplex.complexToReal_fderiv

/-- Chain rule for one analytic function restricted to a radial segment.

The derivative is the complex derivative paired with the radial tangent `z`.
This is the ordinary calculus bridge from complex differentiability at the
radial point to a right-derivative in the real parameter. -/
theorem entireFunction_convexClosedDisk_radial_comp_hasDerivWithinAt
    (F : ℂ → ℂ)
    {ρ : ℝ}
    (hF : ∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ F z)
    (hρ : 0 ≤ ρ)
    (hconvex : Convex ℝ (Metric.closedBall (0 : ℂ) ρ))
    {z : ℂ}
    (hz : ‖z‖ ≤ ρ)
    {t : ℝ}
    (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    HasDerivWithinAt
      (fun s : ℝ => F ((s : ℂ) • z))
      (deriv F ((t : ℂ) • z) * z)
      (Set.Ici t)
      t := by
  have hF_real :
      HasFDerivAt
        F
        ((deriv F ((t : ℂ) • z)) • (1 : ℂ →L[ℝ] ℂ))
        ((t : ℂ) • z) :=
    entireFunction_convexClosedDisk_radialPoint_hasFDerivAt_real
      F hF hρ hconvex hz ht
  have hpath :
      HasDerivWithinAt
        (fun s : ℝ => ((s : ℂ) • z))
        z
        (Set.Ici t)
        t :=
    complex_radialSegment_hasDerivWithinAt z t
  have hcomp :
      HasDerivWithinAt
        (fun s : ℝ => F ((s : ℂ) • z))
        (((deriv F ((t : ℂ) • z)) • (1 : ℂ →L[ℝ] ℂ)) z)
        (Set.Ici t)
        t :=
    hF_real.comp_hasDerivWithinAt t hpath
  have htangent :
      ((deriv F ((t : ℂ) • z)) • (1 : ℂ →L[ℝ] ℂ)) z =
        deriv F ((t : ℂ) • z) * z := by
    exact rfl
  exact
    Eq.subst
      (motive := fun u : ℂ =>
        HasDerivWithinAt
          (fun s : ℝ => F ((s : ℂ) • z))
          u
          (Set.Ici t)
          t)
      htangent
      hcomp

/-- Chain-rule derivative calculation for the radial difference.

This is the only remaining ordinary-calculus sink in the radial FTC branch:
differentiate `t ↦ F ((t : ℂ) • z) - H ((t : ℂ) • z)` from the right and use
`deriv F = deriv H` at the radial point. -/
theorem entireFunction_convexClosedDisk_radialDifference_hasDerivWithinAt_zero
    (F H : ℂ → ℂ)
    {ρ : ℝ}
    (hF : ∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ F z)
    (hH : ∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ H z)
    (hρ : 0 ≤ ρ)
    (hconvex : Convex ℝ (Metric.closedBall (0 : ℂ) ρ))
    (hderiv :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        deriv F z = deriv H z)
    {z : ℂ}
    (hz : ‖z‖ ≤ ρ)
    {t : ℝ}
    (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    HasDerivWithinAt
      (entireFunction_convexClosedDisk_radialDifference F H z)
      0
      (Set.Ici t)
      t := by
  have hF_radial :
      HasDerivWithinAt
        (fun s : ℝ => F ((s : ℂ) • z))
        (deriv F ((t : ℂ) • z) * z)
        (Set.Ici t)
        t :=
    entireFunction_convexClosedDisk_radial_comp_hasDerivWithinAt
      F hF hρ hconvex hz ht
  have hH_radial :
      HasDerivWithinAt
        (fun s : ℝ => H ((s : ℂ) • z))
        (deriv H ((t : ℂ) • z) * z)
        (Set.Ici t)
        t :=
    entireFunction_convexClosedDisk_radial_comp_hasDerivWithinAt
      H hH hρ hconvex hz ht
  have hsub :
      HasDerivWithinAt
        (entireFunction_convexClosedDisk_radialDifference F H z)
        (deriv F ((t : ℂ) • z) * z - deriv H ((t : ℂ) • z) * z)
        (Set.Ici t)
        t :=
    hF_radial.sub hH_radial
  have hpoint_mem :
      ((t : ℂ) • z) ∈ Metric.closedBall (0 : ℂ) ρ :=
    entireFunction_convexClosedDisk_radialSegment_mem
      hρ hconvex hz (Set.Ico_subset_Icc_self ht)
  have hpoint_norm : ‖((t : ℂ) • z)‖ ≤ ρ :=
    mem_closedBall_zero_iff.mp hpoint_mem
  have hderiv_eq :
      deriv F ((t : ℂ) • z) = deriv H ((t : ℂ) • z) :=
    hderiv ((t : ℂ) • z) hpoint_norm
  have hradial_deriv_zero :
      deriv F ((t : ℂ) • z) * z - deriv H ((t : ℂ) • z) * z = 0 :=
    sub_eq_zero.mpr (congrArg (fun u : ℂ => u * z) hderiv_eq)
  exact
    Eq.subst
      (motive := fun u : ℂ =>
        HasDerivWithinAt
          (entireFunction_convexClosedDisk_radialDifference F H z)
          u
          (Set.Ici t)
          t)
      hradial_deriv_zero
      hsub

/-- Center value of the radial difference. -/
theorem entireFunction_convexClosedDisk_radialDifference_zero
    (F H : ℂ → ℂ)
    (hcenter : F 0 = H 0)
    (z : ℂ) :
    entireFunction_convexClosedDisk_radialDifference F H z 0 = 0 := by
  calc
    entireFunction_convexClosedDisk_radialDifference F H z 0 =
        F ((0 : ℂ) • z) - H ((0 : ℂ) • z) := rfl
    _ = F 0 - H 0 :=
      congrArg₂ (fun u v : ℂ => F u - H v) (zero_smul ℂ z) (zero_smul ℂ z)
    _ = H 0 - H 0 :=
      congrArg (fun u : ℂ => u - H 0) hcenter
    _ = 0 :=
      sub_self (H 0)

/-- Endpoint value of the radial difference. -/
theorem entireFunction_convexClosedDisk_radialDifference_one
    (F H : ℂ → ℂ)
    (z : ℂ) :
    entireFunction_convexClosedDisk_radialDifference F H z 1 = F z - H z := by
  calc
    entireFunction_convexClosedDisk_radialDifference F H z 1 =
        F ((1 : ℂ) • z) - H ((1 : ℂ) • z) := rfl
    _ = F z - H z :=
      congrArg₂ (fun u v : ℂ => F u - H v) (one_smul ℂ z) (one_smul ℂ z)

/-- Turning constancy of the radial difference into endpoint equality. -/
theorem entireFunction_convexClosedDisk_endpoint_eq_of_radialDifference_endpoint_eq
    (F H : ℂ → ℂ)
    (hcenter : F 0 = H 0)
    {z : ℂ}
    (hdiff_endpoint :
      entireFunction_convexClosedDisk_radialDifference F H z 1 =
        entireFunction_convexClosedDisk_radialDifference F H z 0) :
    F z = H z := by
  have hleft :
      entireFunction_convexClosedDisk_radialDifference F H z 1 = F z - H z :=
    entireFunction_convexClosedDisk_radialDifference_one F H z
  have hright :
      entireFunction_convexClosedDisk_radialDifference F H z 0 = 0 :=
    entireFunction_convexClosedDisk_radialDifference_zero F H hcenter z
  have hsub_zero : F z - H z = 0 := by
    exact Eq.trans (Eq.symm hleft) (Eq.trans hdiff_endpoint hright)
  exact sub_eq_zero.mp hsub_zero

/-- Real-interval calculus package for a radial segment difference.

The missing analytic work in the FTC branch is exactly to show that the radial
difference is continuous on `[0,1]` and has right-derivative zero on `Ico 0 1`.
That proof is the complex chain rule along `t ↦ t • z`, plus convexity of the
disk segment and the hypothesis `deriv F = deriv H`. -/
theorem entireFunction_convexClosedDisk_radialDifference_intervalCalculus
    (F H : ℂ → ℂ)
    {ρ : ℝ}
    (hF : ∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ F z)
    (hH : ∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ H z)
    (hρ : 0 ≤ ρ)
    (hconvex : Convex ℝ (Metric.closedBall (0 : ℂ) ρ))
    (hderiv :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        deriv F z = deriv H z)
    {z : ℂ}
    (hz : ‖z‖ ≤ ρ) :
    ContinuousOn
        (entireFunction_convexClosedDisk_radialDifference F H z)
        (Set.Icc (0 : ℝ) 1) ∧
      (∀ t : ℝ,
        t ∈ Set.Ico (0 : ℝ) 1 →
        HasDerivWithinAt
          (entireFunction_convexClosedDisk_radialDifference F H z)
          0
          (Set.Ici t)
          t) := by
  have hcont :
      ContinuousOn
        (entireFunction_convexClosedDisk_radialDifference F H z)
        (Set.Icc (0 : ℝ) 1) :=
    entireFunction_convexClosedDisk_radialDifference_continuousOn
      F H hF hH hρ hconvex hz
  have hderiv_zero :
      ∀ t : ℝ,
        t ∈ Set.Ico (0 : ℝ) 1 →
        HasDerivWithinAt
          (entireFunction_convexClosedDisk_radialDifference F H z)
          0
          (Set.Ici t)
          t := by
    intro t ht
    exact
      entireFunction_convexClosedDisk_radialDifference_hasDerivWithinAt_zero
        F H hF hH hρ hconvex hderiv hz ht
  exact ⟨hcont, hderiv_zero⟩

/-- Constancy of the radial difference on `[0,1]` from the interval calculus
package. -/
theorem entireFunction_convexClosedDisk_radialDifference_endpoint_eq
    (F H : ℂ → ℂ)
    {ρ : ℝ}
    (hF : ∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ F z)
    (hH : ∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ H z)
    (hρ : 0 ≤ ρ)
    (hconvex : Convex ℝ (Metric.closedBall (0 : ℂ) ρ))
    (hderiv :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        deriv F z = deriv H z)
    {z : ℂ}
    (hz : ‖z‖ ≤ ρ) :
    entireFunction_convexClosedDisk_radialDifference F H z 1 =
      entireFunction_convexClosedDisk_radialDifference F H z 0 := by
  have hcalc :
      ContinuousOn
          (entireFunction_convexClosedDisk_radialDifference F H z)
          (Set.Icc (0 : ℝ) 1) ∧
        (∀ t : ℝ,
          t ∈ Set.Ico (0 : ℝ) 1 →
          HasDerivWithinAt
            (entireFunction_convexClosedDisk_radialDifference F H z)
            0
            (Set.Ici t)
            t) :=
    entireFunction_convexClosedDisk_radialDifference_intervalCalculus
      F H hF hH hρ hconvex hderiv hz
  exact
    complex_interval_endpoint_eq_of_hasDerivWithinAt_zero
      (entireFunction_convexClosedDisk_radialDifference F H z)
      hcalc.1
      hcalc.2

/-- Deep real-interval FTC core for radial equality propagation on a convex
Jensen disk.

This is the reusable radial theorem underneath both generic derivative-equality
propagation and quotient reconstruction: restrict to `t ↦ t • z`, use convexity
to stay in the disk, and apply the real derivative-zero constant theorem on
`[0,1]`. -/
theorem entireFunction_convexClosedDisk_radialSegment_endpoint_eq_of_deriv_eq_and_center_ftc_core
    (F H : ℂ → ℂ)
    {ρ : ℝ}
    (hF : ∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ F z)
    (hH : ∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ H z)
    (hρ : 0 ≤ ρ)
    (hconvex : Convex ℝ (Metric.closedBall (0 : ℂ) ρ))
    (hderiv :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        deriv F z = deriv H z)
    (hcenter : F 0 = H 0)
    {z : ℂ}
    (hz : ‖z‖ ≤ ρ) :
    F z = H z := by
  have hdiff_endpoint :
      entireFunction_convexClosedDisk_radialDifference F H z 1 =
        entireFunction_convexClosedDisk_radialDifference F H z 0 :=
    entireFunction_convexClosedDisk_radialDifference_endpoint_eq
      F H hF hH hρ hconvex hderiv hz
  exact
    entireFunction_convexClosedDisk_endpoint_eq_of_radialDifference_endpoint_eq
      F H hcenter hdiff_endpoint

/-- Radial FTC owner root for exponential reconstruction from a logarithmic
derivative primitive.

For a fixed endpoint `z`, restrict to the segment `t ↦ t • z` and apply the
real interval derivative-zero constant theorem to
`t ↦ G (t • z) / (G 0 * exp (P (t • z)))`.  Convexity keeps the segment in the
closed disk, the chain rule and `P' = G'/G` make the real derivative vanish,
and the normalization `P 0 = 0` fixes the center value. -/
theorem entireFunction_convexClosedDisk_exp_logDerivPrimitive_radialSegment_endpoint_eq
    (G P : ℂ → ℂ)
    {ρ : ℝ}
    (hG :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        AnalyticAt ℂ G z)
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
    (hP_zero : P 0 = 0)
    {z : ℂ}
    (hz : ‖z‖ ≤ ρ) :
    G z = G 0 * Complex.exp (P z) := by
  have hρ : 0 ≤ ρ :=
    le_trans (norm_nonneg z) hz
  have hquot_an :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        AnalyticAt ℂ (fun u : ℂ => G u / (G 0 * Complex.exp (P u))) w :=
    entireFunction_convexClosedDisk_exp_logDerivPrimitive_quotient_analyticAt
      G P hG hzero hP_an hρ
  have hquot_deriv :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        deriv (fun u : ℂ => G u / (G 0 * Complex.exp (P u))) w =
          deriv (fun _ : ℂ => (1 : ℂ)) w := by
    intro w hw
    have hcore :
        deriv (fun u : ℂ => G u / (G 0 * Complex.exp (P u))) w = 0 ∧
          (fun u : ℂ => G u / (G 0 * Complex.exp (P u))) 0 = 1 :=
      entireFunction_convexClosedDisk_exp_logDerivPrimitive_quotient_deriv_zero_and_center_core
        G P hG hzero hP_an hP_deriv hP_zero hw
    have hconst_deriv_fun :
        deriv (fun _ : ℂ => (1 : ℂ)) = fun _ : ℂ => 0 :=
      deriv_const' (𝕜 := ℂ) (c := (1 : ℂ))
    have hconst_deriv_at :
        deriv (fun _ : ℂ => (1 : ℂ)) w = 0 :=
      congrArg (fun f : ℂ → ℂ => f w) hconst_deriv_fun
    exact Eq.trans hcore.1 (Eq.symm hconst_deriv_at)
  have hquot_center :
      (fun u : ℂ => G u / (G 0 * Complex.exp (P u))) 0 =
        (fun _ : ℂ => (1 : ℂ)) 0 :=
    (entireFunction_convexClosedDisk_exp_logDerivPrimitive_quotient_deriv_zero_and_center_core
      G P hG hzero hP_an hP_deriv hP_zero hz).2
  have hquot_endpoint :
      (fun u : ℂ => G u / (G 0 * Complex.exp (P u))) z =
        (fun _ : ℂ => (1 : ℂ)) z :=
    entireFunction_convexClosedDisk_radialSegment_endpoint_eq_of_deriv_eq_and_center_ftc_core
      (fun u : ℂ => G u / (G 0 * Complex.exp (P u)))
      (fun _ : ℂ => (1 : ℂ))
      hquot_an
      (fun _ _ => analyticAt_const)
      hρ
      (entireFunction_jensenClosedDisk_convex ρ)
      hquot_deriv
      hquot_center
      hz
  have hzero_mem : ‖(0 : ℂ)‖ ≤ ρ := by
    calc
      ‖(0 : ℂ)‖ = 0 := norm_zero
      _ ≤ ρ := hρ
  have hden_ne : G 0 * Complex.exp (P z) ≠ 0 := by
    exact mul_ne_zero (hzero 0 hzero_mem) (Complex.exp_ne_zero (P z))
  exact (div_eq_one_iff_eq hden_ne).mp hquot_endpoint

end
end LFunctions
end Boundary
