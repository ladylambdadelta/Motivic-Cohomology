import Mathlib.Order.Filter.Tendsto
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.AbelTransport.Dirichlet.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.ReciprocalDensity.Owner

/-!
# Abel transport: boundary point and analytic continuation

This file owns the theorems for boundary-point properties and the analytic
continuation of the Dirichlet series to the boundary-line zeta value.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

/-- The boundary point `1 + it` is away from the zeta pole when `|t| ≥ 1`. -/
theorem boundaryLineOnePointRealParam_ne_one_of_one_le_norm
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    boundaryLineOnePointRealParam t ≠ (1 : ℂ) := by
  intro hpoint
  have him_eq :
      t = 0 :=
    Eq.trans (boundaryLineOnePointRealParam_im t).symm
      (Eq.trans (congrArg Complex.im hpoint) rfl)
  have hnorm_eq :
      ‖t‖ = 0 :=
    norm_eq_zero.mpr him_eq
  have hone_le_zero :
      (1 : ℝ) ≤ 0 :=
    Eq.subst
      (motive := fun x : ℝ => (1 : ℝ) ≤ x)
      hnorm_eq
      ht
  exact not_lt_of_ge hone_le_zero zero_lt_one

/-- Analytic-continuation continuity of `ζ` at the boundary point `1 + it`, away
from the pole. -/
theorem boundaryLineOnePointRealParam_riemannZeta_continuousAt
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    ContinuousAt riemannZeta (boundaryLineOnePointRealParam t) := by
  exact
    (differentiableAt_riemannZeta
      (boundaryLineOnePointRealParam_ne_one_of_one_le_norm t ht)).continuousAt

/-- The right-half-plane Abel family approaching the boundary point `1 + it`. -/
def boundaryLineOnePointRealParam_abscissaShift
    (σ t : ℝ) : ℂ :=
  (σ : ℂ) + (t : ℂ) * Complex.I

theorem boundaryLineOnePointRealParam_abscissaShift_oscillator_re
    (t : ℝ) :
    (((t : ℂ) * Complex.I).re) = 0 := by
  calc
    (((t : ℂ) * Complex.I).re) =
        (t : ℂ).re * Complex.I.re - (t : ℂ).im * Complex.I.im :=
      Complex.mul_re (t : ℂ) Complex.I
    _ = t * 0 - 0 * 1 :=
      congrArg₂
        (fun x y : ℝ => x - y)
        (congrArg₂
          (fun x y : ℝ => x * y)
          (Complex.ofReal_re t)
          Complex.I_re)
        (congrArg₂
          (fun x y : ℝ => x * y)
          (Complex.ofReal_im t)
          Complex.I_im)
    _ = 0 - 0 * 1 :=
      congrArg (fun x : ℝ => x - 0 * 1) (mul_zero t)
    _ = 0 - 0 :=
      congrArg (fun x : ℝ => 0 - x) (zero_mul (1 : ℝ))
    _ = 0 :=
      sub_zero 0

theorem boundaryLineOnePointRealParam_abscissaShift_oscillator_im
    (t : ℝ) :
    (((t : ℂ) * Complex.I).im) = t := by
  calc
    (((t : ℂ) * Complex.I).im) =
        (t : ℂ).re * Complex.I.im + (t : ℂ).im * Complex.I.re :=
      Complex.mul_im (t : ℂ) Complex.I
    _ = t * 1 + 0 * 0 :=
      congrArg₂
        (fun x y : ℝ => x + y)
        (congrArg₂
          (fun x y : ℝ => x * y)
          (Complex.ofReal_re t)
          Complex.I_im)
        (congrArg₂
          (fun x y : ℝ => x * y)
          (Complex.ofReal_im t)
          Complex.I_re)
    _ = t + 0 * 0 :=
      congrArg (fun x : ℝ => x + 0 * 0) (mul_one t)
    _ = t + 0 :=
      congrArg (fun x : ℝ => t + x) (zero_mul (0 : ℝ))
    _ = t :=
      add_zero t

theorem boundaryLineOnePointRealParam_abscissaShift_re
    (σ t : ℝ) :
    (boundaryLineOnePointRealParam_abscissaShift σ t).re = σ := by
  calc
    (boundaryLineOnePointRealParam_abscissaShift σ t).re =
        (σ : ℂ).re + (((t : ℂ) * Complex.I).re) :=
      Complex.add_re (σ : ℂ) ((t : ℂ) * Complex.I)
    _ = σ + 0 :=
      congrArg₂
        (fun x y : ℝ => x + y)
        (Complex.ofReal_re σ)
        (boundaryLineOnePointRealParam_abscissaShift_oscillator_re t)
    _ = σ :=
      add_zero σ

theorem boundaryLineOnePointRealParam_abscissaShift_im
    (σ t : ℝ) :
    (boundaryLineOnePointRealParam_abscissaShift σ t).im = t := by
  calc
    (boundaryLineOnePointRealParam_abscissaShift σ t).im =
        (σ : ℂ).im + (((t : ℂ) * Complex.I).im) :=
      Complex.add_im (σ : ℂ) ((t : ℂ) * Complex.I)
    _ = 0 + t :=
      congrArg₂
        (fun x y : ℝ => x + y)
        (Complex.ofReal_im σ)
        (boundaryLineOnePointRealParam_abscissaShift_oscillator_im t)
    _ = t :=
      zero_add t

theorem boundaryLineOnePointRealParam_abscissaShift_one
    (t : ℝ) :
    boundaryLineOnePointRealParam_abscissaShift 1 t =
      boundaryLineOnePointRealParam t :=
  Complex.ext
    (Eq.trans
      (boundaryLineOnePointRealParam_abscissaShift_re 1 t)
      (boundaryLineOnePointRealParam_re t).symm)
    (Eq.trans
      (boundaryLineOnePointRealParam_abscissaShift_im 1 t)
      (boundaryLineOnePointRealParam_im t).symm)

/-- Abel continuation of the half-plane Dirichlet identity to the boundary point
`1 + it`.

The ordinary boundary series `∑ n^{-1-it}` is not asserted to converge.  The
correct owner statement is the Abel-limit theorem: the half-plane sums
`∑ n^{-σ-it}` tend to the analytic-continuation value of `ζ` as
`σ ↓ 1`. -/
theorem boundaryLineOnePointRealParam_dirichlet_series_abel_tendsto_riemannZeta
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    Filter.Tendsto
      (fun σ : ℝ =>
        ∑' n : ℕ,
          (1 : ℂ) /
            ((n : ℂ) ^
              boundaryLineOnePointRealParam_abscissaShift σ t))
      (𝓝[>] (1 : ℝ))
      (𝓝 (riemannZeta (boundaryLineOnePointRealParam t))) := by
  have habscissa_path_continuousAt :
      ContinuousAt
        (fun σ : ℝ => boundaryLineOnePointRealParam_abscissaShift σ t)
        (1 : ℝ) := by
    show ContinuousAt (fun σ : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I) (1 : ℝ)
    exact
      Complex.continuous_ofReal.continuousAt.add
        continuousAt_const
  have habscissa_path_tendsto_raw :
      Filter.Tendsto
        (fun σ : ℝ => boundaryLineOnePointRealParam_abscissaShift σ t)
        (𝓝[>] (1 : ℝ))
        (𝓝 (boundaryLineOnePointRealParam_abscissaShift 1 t)) :=
    habscissa_path_continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have habscissa_path_endpoint :
      boundaryLineOnePointRealParam_abscissaShift 1 t =
        boundaryLineOnePointRealParam t := by
    exact boundaryLineOnePointRealParam_abscissaShift_one t
  have habscissa_path_tendsto_boundary :
      Filter.Tendsto
        (fun σ : ℝ => boundaryLineOnePointRealParam_abscissaShift σ t)
        (𝓝[>] (1 : ℝ))
        (𝓝 (boundaryLineOnePointRealParam t)) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Filter.Tendsto
          (fun σ : ℝ => boundaryLineOnePointRealParam_abscissaShift σ t)
          (𝓝[>] (1 : ℝ))
          (𝓝 z))
      habscissa_path_endpoint
      habscissa_path_tendsto_raw
  have hzeta_path_tendsto :
      Filter.Tendsto
        (fun σ : ℝ =>
          riemannZeta (boundaryLineOnePointRealParam_abscissaShift σ t))
        (𝓝[>] (1 : ℝ))
        (𝓝 (riemannZeta (boundaryLineOnePointRealParam t))) :=
    (boundaryLineOnePointRealParam_riemannZeta_continuousAt t ht).tendsto.comp
      habscissa_path_tendsto_boundary
  have hdirichlet_eq_eventually :
      (fun σ : ℝ =>
        ∑' n : ℕ,
          (1 : ℂ) /
            ((n : ℂ) ^
              boundaryLineOnePointRealParam_abscissaShift σ t)) =ᶠ[𝓝[>] (1 : ℝ)]
        (fun σ : ℝ =>
          riemannZeta (boundaryLineOnePointRealParam_abscissaShift σ t)) := by
    exact
      Filter.Eventually.mono
        self_mem_nhdsWithin
        (fun σ hσ => by
          have hσ_re :
              (boundaryLineOnePointRealParam_abscissaShift σ t).re = σ := by
            exact boundaryLineOnePointRealParam_abscissaShift_re σ t
          have hhalf_plane :
              1 < (boundaryLineOnePointRealParam_abscissaShift σ t).re :=
            Eq.subst
              (motive := fun x : ℝ => 1 < x)
              hσ_re.symm
              hσ
          exact (zeta_eq_tsum_one_div_nat_cpow hhalf_plane).symm)
  exact Filter.Tendsto.congr' hdirichlet_eq_eventually.symm hzeta_path_tendsto

/-- The Abel boundary value of the Dirichlet presentation is the analytic
continuation value of `ζ(1 + it)`. -/
theorem boundaryLineOnePointRealParam_dirichlet_series_abel_boundaryValue_eq_riemannZeta
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    ∃ V : ℂ,
      Filter.Tendsto
        (fun σ : ℝ =>
          ∑' n : ℕ,
            (1 : ℂ) /
              ((n : ℂ) ^
                boundaryLineOnePointRealParam_abscissaShift σ t))
        (𝓝[>] (1 : ℝ))
        (𝓝 V) ∧
      V = riemannZeta (boundaryLineOnePointRealParam t) := by
  exact
    ⟨riemannZeta (boundaryLineOnePointRealParam t),
      boundaryLineOnePointRealParam_dirichlet_series_abel_tendsto_riemannZeta
        t ht,
      rfl⟩
end

end LFunctions
end Boundary
