import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.AbelTail.DirichletLimit

/-!
# Abel continuation for boundary tails

This file owns the public one-sided Abel-continuation lemmas that bridge the
Dirichlet half-plane series to the boundary-line zeta remainder.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
open Filter

/-- One-sided Abel boundary value of the zeta Dirichlet series on `1 + it`.

This is the owner statement for the analytic-continuation boundary passage; it
does not assert ordinary convergence of the Dirichlet series on `re = 1`. -/
theorem Complex.boundaryLineOnePointRealParam_boundaryDirichletSeries_abel_tendsto_riemannZeta_from_dirichletContinuation
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    Tendsto
      (fun σ : ℝ =>
        ∑' n : ℕ,
          ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹)
      (𝓝[>] (1 : ℝ))
      (𝓝 (riemannZeta (Complex.boundaryLineOnePointRealParam t))) := by
  exact
    Complex.boundaryLineOnePointRealParam_boundaryDirichletSeries_abel_tendsto_riemannZeta_for_tail
      t ht

/-- Abel boundary value of the boundary-line Dirichlet series at `1 + it`.

This is deliberately a one-sided Abel limit, not ordinary convergence of the
Dirichlet series on `re = 1`. -/
theorem Complex.boundaryLineOnePointRealParam_boundaryDirichletSeries_abel_tendsto_riemannZeta
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    Tendsto
      (fun σ : ℝ =>
        ∑' n : ℕ,
          ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹)
      (𝓝[>] (1 : ℝ))
      (𝓝 (riemannZeta (Complex.boundaryLineOnePointRealParam t))) := by
  exact
    Complex.boundaryLineOnePointRealParam_boundaryDirichletSeries_abel_tendsto_riemannZeta_from_dirichletContinuation
      t ht

/-- Absolute convergence of the Abel-damped boundary Dirichlet series in the
open half-plane `σ > 1`. -/
theorem Complex.boundaryLineOnePointRealParam_abelDirichletSeries_summable
    (t σ : ℝ)
    (hσ : 1 < σ) :
    Summable
      (fun n : ℕ =>
        ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹) := by
  exact
    Complex.boundaryLineOnePointRealParam_abelDirichletSeries_summable_for_tail
      t σ hσ

/-- A summable Nat series whose zeroth term vanishes splits as a finite
`Icc 1 N` block plus the strict post-`N` tail. -/
theorem Complex.summable_nat_tail_eq_tsum_sub_Icc_of_zero
    {f : ℕ → ℂ}
    (hf : Summable f)
    (hf_zero : f 0 = 0)
    (N : ℕ)
    (hN : 1 ≤ N) :
    (∑' n : ℕ, if N < n then f n else 0) =
      (∑' n : ℕ, f n) - ∑ n ∈ Finset.Icc 1 N, f n := by
  exact
    Complex.summable_nat_tail_eq_tsum_sub_Icc_of_zero_for_abel_boundary
      hf hf_zero N hN

/-- Pointwise finite-truncation identity for Abel-damped boundary Dirichlet
series.  The tail is the full Abel series minus its Abel-damped finite block. -/
theorem Complex.boundaryLineOnePointRealParam_abelDampedTail_eq_series_sub_truncation
    (t σ : ℝ)
    (hσ : 1 < σ)
    (N : ℕ)
    (hN : 1 ≤ N) :
    (∑' n : ℕ,
      if N < n then
        ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹
      else
        0) =
      (∑' n : ℕ,
        ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹) -
        ∑ n ∈ Finset.Icc 1 N,
          ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹ := by
  exact
    Complex.boundaryLineOnePointRealParam_abelDampedTail_eq_series_sub_truncation_for_tail
      t σ hσ N hN

/-- The Abel-damped finite block tends to the boundary-line finite truncation
as `σ → 1+`. -/
theorem Complex.boundaryLineOnePointRealParam_abelFiniteTruncation_tendsto_boundaryTruncation
    (t : ℝ)
    (N : ℕ) :
    Tendsto
      (fun σ : ℝ =>
        ∑ n ∈ Finset.Icc 1 N,
          ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹)
      (𝓝[>] (1 : ℝ))
      (𝓝 (Complex.riemannZetaBoundaryLineTruncation t N)) := by
  exact
    Complex.boundaryLineOnePointRealParam_abelFiniteTruncation_tendsto_boundaryTruncation_for_tail
      t N

/-- Removing the first `N` terms from a one-sided Abel-damped Dirichlet series
is compatible with the Abel boundary limit. -/
theorem Complex.boundaryLineOnePointRealParam_abelDampedTail_tendsto_zeta_remainder_from_series
    (t : ℝ)
    (_ht : 1 ≤ ‖t‖)
    (N : ℕ)
    (hN : 1 ≤ N)
    (hseries :
      Tendsto
        (fun σ : ℝ =>
          ∑' n : ℕ,
            ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹)
        (𝓝[>] (1 : ℝ))
        (𝓝 (riemannZeta (Complex.boundaryLineOnePointRealParam t)))) :
    Tendsto
      (fun σ : ℝ =>
        ∑' n : ℕ,
          if N < n then
            ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹
          else
            0)
      (𝓝[>] (1 : ℝ))
      (𝓝
        (riemannZeta (Complex.boundaryLineOnePointRealParam t) -
          Complex.riemannZetaBoundaryLineTruncation t N)) := by
  have htail_eq :
      (fun σ : ℝ =>
        ∑' n : ℕ,
          if N < n then
            ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹
          else
            0) =ᶠ[𝓝[>] (1 : ℝ)]
        (fun σ : ℝ =>
          (∑' n : ℕ,
            ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹) -
            ∑ n ∈ Finset.Icc 1 N,
              ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹) := by
    exact (eventually_mem_nhdsWithin :
      ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ), σ ∈ Set.Ioi (1 : ℝ)).mono
      (fun σ hσ =>
        Complex.boundaryLineOnePointRealParam_abelDampedTail_eq_series_sub_truncation
          t σ hσ N hN)
  have hfinite :
      Tendsto
        (fun σ : ℝ =>
          ∑ n ∈ Finset.Icc 1 N,
            ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹)
        (𝓝[>] (1 : ℝ))
        (𝓝 (Complex.riemannZetaBoundaryLineTruncation t N)) :=
    Complex.boundaryLineOnePointRealParam_abelFiniteTruncation_tendsto_boundaryTruncation
      t N
  exact
    (tendsto_congr' htail_eq).mpr
      (hseries.sub hfinite)

/-- Removing a finite truncation from the Abel-damped Dirichlet series leaves
the Abel-damped post-cutoff tail. -/
theorem Complex.boundaryLineOnePointRealParam_abelDampedTail_tendsto_zeta_remainder_of_series
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (N : ℕ)
    (hN : 1 ≤ N) :
    Tendsto
      (fun σ : ℝ =>
        ∑' n : ℕ,
          if N < n then
            ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹
          else
            0)
      (𝓝[>] (1 : ℝ))
      (𝓝
        (riemannZeta (Complex.boundaryLineOnePointRealParam t) -
          Complex.riemannZetaBoundaryLineTruncation t N)) := by
  exact
    Complex.boundaryLineOnePointRealParam_abelDampedTail_tendsto_zeta_remainder_from_series
      t ht N hN
      (Complex.boundaryLineOnePointRealParam_boundaryDirichletSeries_abel_tendsto_riemannZeta
        t ht)

/-- The Abel boundary tail has the zeta-remainder boundary value. -/
theorem Complex.boundaryLineOnePointRealParam_boundaryDirichletTail_abel_tendsto_zeta_remainder
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (N : ℕ)
    (hN : 1 ≤ N) :
    Tendsto
      (fun σ : ℝ =>
        ∑' n : ℕ,
          if N < n then
            ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹
          else
            0)
      (𝓝[>] (1 : ℝ))
      (𝓝
        (riemannZeta (Complex.boundaryLineOnePointRealParam t) -
          Complex.riemannZetaBoundaryLineTruncation t N)) := by
  exact
    Complex.boundaryLineOnePointRealParam_abelDampedTail_tendsto_zeta_remainder_of_series
      t ht N hN

end

end LFunctions
end Boundary
