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

    (t : ℝ)
    (N : ℕ)
    (hζ :
      HasSum
        (fun n : ℕ =>
          (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t))
        (riemannZeta (boundaryLineOnePointRealParam t))) :
    HasSum
        (fun n : ℕ =>
          if N < n then
            (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)
          else
            0)
        (riemannZeta (boundaryLineOnePointRealParam t) -
          ∑ n ∈ Finset.Icc 1 N,
            (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)) := by
  have htail_compl :
      HasSum
        (fun x : {n : ℕ // n ∉ Finset.Icc 1 N} =>
          (1 : ℂ) / (((x : ℕ) : ℂ) ^ boundaryLineOnePointRealParam t))
        (riemannZeta (boundaryLineOnePointRealParam t) -
          ∑ n ∈ Finset.Icc 1 N,
            (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)) :=
    ((Finset.Icc 1 N).hasSum_iff_compl).mp hζ
  have htail_indicator :
      HasSum
        ({n : ℕ | n ∉ Finset.Icc 1 N}.indicator
          (fun n : ℕ =>
            (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)))
        (riemannZeta (boundaryLineOnePointRealParam t) -
          ∑ n ∈ Finset.Icc 1 N,
            (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)) := by
    exact
      (hasSum_subtype_iff_indicator
        (s := {n : ℕ | n ∉ Finset.Icc 1 N})
        (f := fun n : ℕ =>
          (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t))).mp
        htail_compl
  exact htail_indicator.congr_fun
    (fun n : ℕ =>
      (boundaryLineOnePointRealParam_dirichlet_tail_indicator_eq_cutoff_if
        t N n).symm)

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

/-- Abel continuation of the half-plane Dirichlet identity to the boundary point
`1 + it`.

The ordinary boundary series `∑ n^{-1-it}` is not asserted to converge.  The
correct owner statement is the Abel-limit theorem: the half-plane sums
`∑ n^{-σ-it}` tend to the analytic-continuation value of `ζ` as
`σ ↓ 1`. -/
theorem boundaryLineOnePointRealParam_dirichlet_series_abel_tendsto_riemannZeta
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    Tendsto
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
      Tendsto
        (fun σ : ℝ => boundaryLineOnePointRealParam_abscissaShift σ t)
        (𝓝[>] (1 : ℝ))
        (𝓝 (boundaryLineOnePointRealParam_abscissaShift 1 t)) :=
    habscissa_path_continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have habscissa_path_endpoint :
      boundaryLineOnePointRealParam_abscissaShift 1 t =
        boundaryLineOnePointRealParam t := by
    exact Complex.ext rfl rfl
  have habscissa_path_tendsto_boundary :
      Tendsto
        (fun σ : ℝ => boundaryLineOnePointRealParam_abscissaShift σ t)
        (𝓝[>] (1 : ℝ))
        (𝓝 (boundaryLineOnePointRealParam t)) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun σ : ℝ => boundaryLineOnePointRealParam_abscissaShift σ t)
          (𝓝[>] (1 : ℝ))
          (𝓝 z))
      habscissa_path_endpoint
      habscissa_path_tendsto_raw
  have hzeta_path_tendsto :
      Tendsto
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
            rfl
          have hhalf_plane :
              1 < (boundaryLineOnePointRealParam_abscissaShift σ t).re :=
            Eq.subst
              (motive := fun x : ℝ => 1 < x)
              hσ_re.symm
              hσ
          exact (zeta_eq_tsum_one_div_nat_cpow hhalf_plane).symm)
  exact Tendsto.congr' hdirichlet_eq_eventually hzeta_path_tendsto

/-- The Abel boundary value of the Dirichlet presentation is the analytic
continuation value of `ζ(1 + it)`. -/
theorem boundaryLineOnePointRealParam_dirichlet_series_abel_boundaryValue_eq_riemannZeta
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    ∃ V : ℂ,
      Tendsto
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

/-- The Abel-damped finite cutoff prefix. -/
def abelBoundary_logarithmicPhase_dampedPrefix

end

end LFunctions
end Boundary
