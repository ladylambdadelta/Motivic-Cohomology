import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.FixedCutoffHolomorphic
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.ParameterDerivativeMajorant

/-!
# Fixed-cutoff Bernoulli holomorphicity

This file owns dominated differentiation for the fixed lower-limit Bernoulli
integral and the resulting fixed-cutoff defect holomorphicity theorem.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
open MeasureTheory
local notation "π" => Real.pi

/-- Fixed lower-limit dominated differentiation for an improper parameter
integral over a positive tail.

This is the measure-theoretic owner API needed by the Euler-Maclaurin
Bernoulli kernel: the lower limit is fixed, the measure is
`volume.restrict (Ioi N)`, and the hypotheses are pointwise parameter
derivatives plus a local integrable majorant for those derivatives. -/
theorem hasDerivAt_integral_Ioi_of_local_integrable_derivative_majorant
    (N : ℕ)
    (F F' : ℂ → ℝ → ℂ)
    (z : ℂ)
    (r : ℝ)
    (hr : 0 < r)
    (g : ℝ → ℝ)
    (hF_meas :
      ∀ᶠ w in 𝓝 z,
        AEStronglyMeasurable
          (F w)
          (volume.restrict (Set.Ioi (((N : ℕ) : ℝ)))))
    (hF_int :
      Integrable
        (F z)
        (volume.restrict (Set.Ioi (((N : ℕ) : ℝ)))))
    (hF'_meas :
      AEStronglyMeasurable
        (F' z)
        (volume.restrict (Set.Ioi (((N : ℕ) : ℝ)))))
    (hg :
      IntegrableOn g (Set.Ioi (((N : ℕ) : ℝ)))
        volume)
    (hbound :
      ∀ᵐ x ∂volume.restrict (Set.Ioi (((N : ℕ) : ℝ))),
        ∀ w ∈ Metric.ball z r, ‖F' w x‖ ≤ g x)
    (hderiv :
      ∀ᵐ x ∂volume.restrict (Set.Ioi (((N : ℕ) : ℝ))),
        ∀ w ∈ Metric.ball z r,
          HasDerivAt (fun u : ℂ => F u x) (F' w x) w) :
    HasDerivAt
      (fun w : ℂ =>
        ∫ x in Set.Ioi (((N : ℕ) : ℝ)), F w x)
      (∫ x in Set.Ioi (((N : ℕ) : ℝ)), F' z x)
      z := by
  have hg_restrict :
      Integrable g (volume.restrict (Set.Ioi (((N : ℕ) : ℝ)))) :=
    hg
  have hparam :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Set.Ioi (((N : ℕ) : ℝ))))
      (F := F)
      (F' := F')
      (x₀ := z)
      (bound := g)
      hr
      hF_meas
      hF_int
      hF'_meas
      hbound
      hg_restrict
      hderiv
  exact hparam.2

/-- Dominated differentiation for the fixed-cutoff Bernoulli kernel, using
the local integrable majorant and the pointwise parameter differentiability
already owned above.

This is the reusable parameter-integral theorem for the Euler-Maclaurin
Bernoulli kernel with fixed lower limit.  It is deliberately separated from
the zeta defect so the remaining analytic work is the dominated-differentiation
API, not an endpoint-shaped holomorphicity assertion. -/
theorem eulerMaclaurinZetaBernoulliIntegralCoreWithCutoff_differentiable_under_integral_from_local_majorant
  (N : ℕ)
  (hN : 0 < N) :
  DifferentiableOn ℂ
    (eulerMaclaurinZetaBernoulliIntegralCoreWithCutoff N)
  ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
  intro z hz
  let hdata :=
    eulerMaclaurinBernoulliKernel_parameterDerivative_local_integrable_majorant_on_puncturedStrip
      N hN z hz
  let ⟨r, hr_pos, haux_data⟩ := hdata
  let ⟨g, hg_integrable_data, hmajorant_data⟩ := haux_data
  have hg_integrable : IntegrableOn g (Set.Ioi (((N : ℕ) : ℝ))) :=
    hg_integrable_data
  have hmajorant :
      ∀ᵐ x ∂volume.restrict (Set.Ioi (((N : ℕ) : ℝ))),
        ∀ w ∈ Metric.ball z r,
          ‖eulerMaclaurinBernoulliKernel_realTailParameterDerivative x w‖ ≤ g x :=
    hmajorant_data
  let F : ℂ → ℝ → ℂ := fun (w : ℂ) (x : ℝ) =>
    ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
      (((x : ℝ) : ℂ) ^ (-(w + 1)))
  let F' : ℂ → ℝ → ℂ :=
    fun (w : ℂ) (x : ℝ) =>
      eulerMaclaurinBernoulliKernel_realTailParameterDerivative x w
  have hderiv :
      ∀ᵐ x ∂volume.restrict (Set.Ioi (((N : ℕ) : ℝ))),
        ∀ w ∈ Metric.ball z r,
          HasDerivAt (fun u : ℂ => F u x) (F' w x) w := by
    exact ae_restrict_of_forall_mem measurableSet_Ioi
      (fun x hx_tail w hw => by
        have hx_pos : 0 < x := by
          exact lt_of_lt_of_le zero_lt_one
            (eulerMaclaurin_one_le_of_mem_Ioi_nat_cast N hN hx_tail)
        exact eulerMaclaurinBernoulliKernel_hasDerivAt_parameter x hx_pos w)
  have hbound :
      ∀ᵐ x ∂volume.restrict (Set.Ioi (((N : ℕ) : ℝ))),
        ∀ w ∈ Metric.ball z r, ‖F' w x‖ ≤ g x := by
    exact hmajorant.mono
      (fun x hx w hw => hx w hw)
  have hF_meas :
      ∀ᶠ w in 𝓝 z,
        AEStronglyMeasurable
          (F w)
          (volume.restrict (Set.Ioi (((N : ℕ) : ℝ)))) := by
    exact Filter.Eventually.of_forall
      (fun w : ℂ =>
        eulerMaclaurinBernoulliKernel_aestronglyMeasurable N hN w)
  have hF_int :
      Integrable
        (F z)
        (volume.restrict (Set.Ioi (((N : ℕ) : ℝ)))) := by
    let hdata₀ :=
      eulerMaclaurinBernoulliKernel_local_integrable_majorant_on_puncturedStrip
        N hN z hz
    let ⟨r₀, hr₀_pos, haux₀_data⟩ := hdata₀
    let ⟨g₀, hg₀_integrable_data, hmajorant₀_data⟩ := haux₀_data
    have hg₀_integrable : IntegrableOn g₀ (Set.Ioi (((N : ℕ) : ℝ))) :=
      hg₀_integrable_data
    have hmajorant₀ :
        ∀ w : ℂ, w ∈ Metric.ball z r₀ →
          ∀ᵐ x ∂volume.restrict (Set.Ioi (((N : ℕ) : ℝ))),
            ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((x : ℝ) : ℂ) ^ (-(w + 1)))‖ ≤ g₀ x :=
      hmajorant₀_data
    have hz_ball₀ : z ∈ Metric.ball z r₀ :=
      Metric.mem_ball_self hr₀_pos
    have hbound₀ :
        ∀ᵐ x ∂volume.restrict (Set.Ioi (((N : ℕ) : ℝ))),
          ‖F z x‖ ≤ g₀ x := by
      exact (hmajorant₀ z hz_ball₀).mono
        (fun x hx => hx)
    have hg₀ :
        Integrable g₀ (volume.restrict (Set.Ioi (((N : ℕ) : ℝ)))) :=
      hg₀_integrable
    have hmeas :
        AEStronglyMeasurable
          (F z)
          (volume.restrict (Set.Ioi (((N : ℕ) : ℝ)))) := by
      exact eulerMaclaurinBernoulliKernel_aestronglyMeasurable N hN z
    exact Integrable.mono' hg₀ hmeas hbound₀
  have hF'_meas :
      AEStronglyMeasurable
        (F' z)
        (volume.restrict (Set.Ioi (((N : ℕ) : ℝ)))) := by
    exact
      eulerMaclaurinBernoulliKernel_parameterDerivative_aestronglyMeasurable
        N hN z
  have hhasDeriv :
      HasDerivAt
        (fun w : ℂ =>
          ∫ x in Set.Ioi (((N : ℕ) : ℝ)), F w x)
        (∫ x in Set.Ioi (((N : ℕ) : ℝ)), F' z x)
        z :=
    hasDerivAt_integral_Ioi_of_local_integrable_derivative_majorant
      N F F' z r hr_pos g hF_meas hF_int hF'_meas
      hg_integrable hbound hderiv
  have hsame :
      (fun w : ℂ =>
        ∫ x in Set.Ioi (((N : ℕ) : ℝ)), F w x) =
        eulerMaclaurinZetaBernoulliIntegralCoreWithCutoff N := by
    funext w
    rfl
  exact
    (Eq.subst
      (motive := fun H : ℂ → ℂ => DifferentiableAt ℂ H z)
      hsame
      hhasDeriv.differentiableAt).differentiableWithinAt

/-- Differentiation under the fixed lower-limit Bernoulli improper integral in
the complex parameter. -/
theorem eulerMaclaurinZetaBernoulliIntegralCoreWithCutoff_differentiable_under_integral
    (N : ℕ)
    (hN : 0 < N) :
    DifferentiableOn ℂ
      (eulerMaclaurinZetaBernoulliIntegralCoreWithCutoff N)
      ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
  exact
    eulerMaclaurinZetaBernoulliIntegralCoreWithCutoff_differentiable_under_integral_from_local_majorant
      N hN

/-- Fixed lower-limit Bernoulli integral core is holomorphic in the complex
parameter on the punctured strip.

This is the standard parameter-integral theorem: the lower limit is fixed, the
Bernoulli factor is bounded, and the complex-power kernel has locally uniform
integrable majorants on vertical compacta. -/
theorem eulerMaclaurinZetaBernoulliIntegralCoreWithCutoff_parameter_holomorphic_standard
    (N : ℕ)
    (hN : 0 < N) :
    DifferentiableOn ℂ
      (eulerMaclaurinZetaBernoulliIntegralCoreWithCutoff N)
      ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
  exact
    eulerMaclaurinZetaBernoulliIntegralCoreWithCutoff_differentiable_under_integral
      N hN

/-- Fixed lower-limit Bernoulli integral core is holomorphic in the complex
parameter on the punctured strip. -/
theorem eulerMaclaurinZetaBernoulliIntegralCoreWithCutoff_holomorphicOn_puncturedStrip
    (N : ℕ)
    (hN : 0 < N) :
    DifferentiableOn ℂ
      (eulerMaclaurinZetaBernoulliIntegralCoreWithCutoff N)
      ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
  exact
    eulerMaclaurinZetaBernoulliIntegralCoreWithCutoff_parameter_holomorphic_standard
      N hN

/-- Fixed-cutoff Bernoulli remainder is holomorphic on the punctured strip. -/
theorem eulerMaclaurinZetaBernoulliIntegralRemainderWithCutoff_holomorphicOn_puncturedStrip
    (N : ℕ)
    (hN : 0 < N) :
    DifferentiableOn ℂ
      (eulerMaclaurinZetaBernoulliIntegralRemainderWithCutoff N)
      ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
  unfold eulerMaclaurinZetaBernoulliIntegralRemainderWithCutoff
  have hid :
      DifferentiableOn ℂ
        (fun z : ℂ => z)
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    differentiableOn_id
  have hneg_id :
      DifferentiableOn ℂ
        (fun z : ℂ => -z)
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    hid.neg
  have hcore :
      DifferentiableOn ℂ
        (eulerMaclaurinZetaBernoulliIntegralCoreWithCutoff N)
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    eulerMaclaurinZetaBernoulliIntegralCoreWithCutoff_holomorphicOn_puncturedStrip
      N hN
  exact hneg_id.mul hcore

/-- Fixed-cutoff defect is holomorphic on the punctured vertical strip. -/
theorem eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect_holomorphicOn_puncturedStrip_standard
    (N : ℕ)
    (hN : 0 < N) :
    DifferentiableOn ℂ
      (eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect N)
      ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
  unfold eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect
  have hzeta :
      DifferentiableOn ℂ
        riemannZeta
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    eulerMaclaurin_riemannZeta_holomorphicOn_fixedCutoff_puncturedStrip
  have hfinite :
      DifferentiableOn ℂ
        (eulerMaclaurinZetaFinitePartWithCutoff N)
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    eulerMaclaurinZetaFinitePartWithCutoff_holomorphicOn_puncturedStrip N
  have hmain :
      DifferentiableOn ℂ
        (eulerMaclaurinZetaMainTermWithCutoff N)
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    eulerMaclaurinZetaMainTermWithCutoff_holomorphicOn_puncturedStrip N hN
  have hendpoint :
      DifferentiableOn ℂ
        (eulerMaclaurinZetaEndpointTermWithCutoff N)
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    eulerMaclaurinZetaEndpointTermWithCutoff_holomorphicOn_puncturedStrip N hN
  have hremainder :
      DifferentiableOn ℂ
        (eulerMaclaurinZetaBernoulliIntegralRemainderWithCutoff N)
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    eulerMaclaurinZetaBernoulliIntegralRemainderWithCutoff_holomorphicOn_puncturedStrip
      N hN
  exact (hzeta.sub hfinite).sub ((hmain.add hendpoint).add hremainder)

end

end LFunctions
end Boundary
