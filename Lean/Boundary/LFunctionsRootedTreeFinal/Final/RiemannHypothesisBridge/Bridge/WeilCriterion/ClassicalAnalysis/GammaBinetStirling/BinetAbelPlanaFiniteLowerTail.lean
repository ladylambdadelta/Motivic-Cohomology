import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaFiniteAlgebra

/-!
# Lower-tail owners for the finite Abel-Plana asymptotic estimate

This file owns the lower vertical tail estimates used by the finite
Abel-Plana contour remainder bound.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology
open MeasureTheory

/-- The lower finite Abel-Plana tail integrand equals twice the principal
Binet arctangent kernel on its positive vertical contour. -/
theorem Complex.binetAbelPlanaFiniteLowerContourTail_integrand_eq_two_arctanKernel
    {w : ℂ}
    (hw : 0 < w.re) :
    ∀ N : ℕ,
      ∀ᵐ (t : ℝ) ∂volume.restrict (Set.Ioi (N : ℝ)),
        (-Complex.I) *
          ((Complex.log (w + (t : ℂ) * Complex.I) -
              Complex.log (w - (t : ℂ) * Complex.I)) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)) =
          2 *
            (Complex.arctan ((t : ℂ) / w) /
              (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)) := by
  exact fun N =>
    (ae_restrict_mem measurableSet_Ioi).mono
      (fun (t : ℝ) ht =>
        by
          have ht_pos : 0 < t :=
            lt_of_le_of_lt (Nat.cast_nonneg N) ht
          exact
            Complex.binetAbelPlana_logJump_integrand_eq_two_arctanKernel
              hw ht_pos)

/-- Pointwise lower-tail domination by twice the Binet vertical kernel
majorant. -/
theorem Complex.norm_binetAbelPlanaFiniteLowerContourTail_integrand_le_majorant
    {w : ℂ}
    (hw : 0 < w.re) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ N : ℕ in Filter.atTop,
          ∀ᵐ (t : ℝ) ∂volume.restrict (Set.Ioi (N : ℝ)),
            ‖(-Complex.I) *
              ((Complex.log (w + (t : ℂ) * Complex.I) -
                  Complex.log (w - (t : ℂ) * Complex.I)) /
                (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))‖ ≤
              C * Complex.binetAbelPlanaVerticalKernelMajorant t := by
  match
    Complex.binetSecondFormula_arctanKernel_tail_norm_le_majorant_owner
      hw with
  | ⟨C, hC_nonneg, hC⟩ =>
    have htwoC_nonneg : 0 ≤ 2 * C :=
      mul_nonneg (zero_le_two : (0 : ℝ) ≤ 2) hC_nonneg
    have htail_eventually :
        ∀ᶠ N : ℕ in Filter.atTop,
          ∀ᵐ (t : ℝ) ∂volume.restrict (Set.Ioi (N : ℝ)),
            ‖(-Complex.I) *
              ((Complex.log (w + (t : ℂ) * Complex.I) -
                  Complex.log (w - (t : ℂ) * Complex.I)) /
                (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))‖ ≤
              (2 * C) * Complex.binetAbelPlanaVerticalKernelMajorant t := by
      match exists_nat_gt (‖w‖ / 2) with
      | ⟨N₀, hN₀⟩ =>
        exact
          (Filter.eventually_ge_atTop N₀).mono
            (fun N hN =>
              ((Complex.binetAbelPlanaFiniteLowerContourTail_integrand_eq_two_arctanKernel
                hw N).and (ae_restrict_mem measurableSet_Ioi)).mono
                (fun (t : ℝ) ht_pair =>
                  by
                    have ht_eq :
                        (-Complex.I) *
                          ((Complex.log (w + (t : ℂ) * Complex.I) -
                              Complex.log (w - (t : ℂ) * Complex.I)) /
                            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)) =
                          2 *
                            (Complex.arctan ((t : ℂ) / w) /
                              (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)) :=
                      ht_pair.1
                    have ht_mem : t ∈ Set.Ioi (N : ℝ) :=
                      ht_pair.2
                    have hN₀_le_N : (N₀ : ℝ) ≤ (N : ℝ) :=
                      Nat.cast_le.mpr hN
                    have ht_tail : t ∈ Set.Ioi (‖w‖ / 2) :=
                      lt_of_lt_of_le hN₀ (le_trans hN₀_le_N (le_of_lt ht_mem))
                    have hkernel :
                        ‖Complex.arctan ((t : ℂ) / w) /
                            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ ≤
                          C * Complex.binetAbelPlanaVerticalKernelMajorant t :=
                      hC t ht_tail
                    calc
                      ‖(-Complex.I) *
                          ((Complex.log (w + (t : ℂ) * Complex.I) -
                              Complex.log (w - (t : ℂ) * Complex.I)) /
                            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))‖ =
                          ‖2 *
                            (Complex.arctan ((t : ℂ) / w) /
                              (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))‖ := by
                        exact congrArg norm ht_eq
                      _ =
                          2 *
                            ‖Complex.arctan ((t : ℂ) / w) /
                              (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ := by
                        have htwo : ‖(2 : ℂ)‖ = (2 : ℝ) :=
                          Complex.norm_two_natCast
                        calc
                          ‖2 *
                            (Complex.arctan ((t : ℂ) / w) /
                              (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))‖ =
                              ‖(2 : ℂ)‖ *
                                ‖Complex.arctan ((t : ℂ) / w) /
                                  (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ := by
                            exact norm_mul _ _
                          _ =
                              2 *
                                ‖Complex.arctan ((t : ℂ) / w) /
                                  (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ := by
                            exact congrArg
                              (fun x : ℝ =>
                                x *
                                  ‖Complex.arctan ((t : ℂ) / w) /
                                    (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖)
                              htwo
                      _ ≤ 2 * (C * Complex.binetAbelPlanaVerticalKernelMajorant t) := by
                        exact mul_le_mul_of_nonneg_left hkernel zero_le_two
                      _ = (2 * C) * Complex.binetAbelPlanaVerticalKernelMajorant t := by
                        exact Real.two_mul_assoc C
                          (Complex.binetAbelPlanaVerticalKernelMajorant t)
                )
            )
    exact Exists.intro (2 * C) (And.intro htwoC_nonneg htail_eventually)

/-- The lower finite Abel-Plana tail positive vertical line is measurable. -/
theorem Complex.measurable_binetAbelPlanaFiniteLowerContourTail_plusLine
    (w : ℂ) :
    Measurable
      (fun t : ℝ => w + (t : ℂ) * Complex.I) := by
  exact
    measurable_const.add
      ((Complex.measurable_ofReal.comp measurable_id).mul measurable_const)

/-- The lower finite Abel-Plana tail negative vertical line is measurable. -/
theorem Complex.measurable_binetAbelPlanaFiniteLowerContourTail_minusLine
    (w : ℂ) :
    Measurable
      (fun t : ℝ => w - (t : ℂ) * Complex.I) := by
  exact
    measurable_const.sub
      ((Complex.measurable_ofReal.comp measurable_id).mul measurable_const)

/-- The lower finite Abel-Plana tail logarithmic jump is measurable. -/
theorem Complex.measurable_binetAbelPlanaFiniteLowerContourTail_logJump
    (w : ℂ) :
    Measurable
      (fun t : ℝ =>
        Complex.log (w + (t : ℂ) * Complex.I) -
          Complex.log (w - (t : ℂ) * Complex.I)) := by
  exact
    (Complex.measurable_binetAbelPlanaFiniteLowerContourTail_plusLine w).clog.sub
      (Complex.measurable_binetAbelPlanaFiniteLowerContourTail_minusLine w).clog

/-- The lower finite Abel-Plana tail exponential denominator is measurable. -/
theorem Complex.measurable_binetAbelPlanaFiniteLowerContourTail_denominator :
    Measurable
      (fun t : ℝ =>
        Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) :=
  Complex.binetSecondFormula_exp_denominator_measurable

/-- The lower finite Abel-Plana tail integrand is measurable. -/
theorem Complex.measurable_binetAbelPlanaFiniteLowerContourTail_integrand
    (w : ℂ) :
    Measurable
      (fun t : ℝ =>
        (-Complex.I) *
          ((Complex.log (w + (t : ℂ) * Complex.I) -
              Complex.log (w - (t : ℂ) * Complex.I)) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))) := by
  exact
    measurable_const.mul
      ((Complex.measurable_binetAbelPlanaFiniteLowerContourTail_logJump w).div
        Complex.measurable_binetAbelPlanaFiniteLowerContourTail_denominator)

/-- The norm of the lower finite Abel-Plana tail integrand is measurable. -/
theorem Complex.measurable_norm_binetAbelPlanaFiniteLowerContourTail_integrand
    (w : ℂ) :
    Measurable
      (fun t : ℝ =>
        ‖(-Complex.I) *
          ((Complex.log (w + (t : ℂ) * Complex.I) -
              Complex.log (w - (t : ℂ) * Complex.I)) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))‖) := by
  exact
    (Complex.measurable_binetAbelPlanaFiniteLowerContourTail_integrand w).norm

/-- The norm of the lower finite Abel-Plana tail integrand is strongly
measurable on every lower tail. -/
theorem Complex.aestronglyMeasurable_norm_binetAbelPlanaFiniteLowerContourTail_integrand
    (N : ℕ)
    (w : ℂ) :
    AEStronglyMeasurable
      (fun t : ℝ =>
        ‖(-Complex.I) *
          ((Complex.log (w + (t : ℂ) * Complex.I) -
              Complex.log (w - (t : ℂ) * Complex.I)) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))‖)
      (volume.restrict (Set.Ioi (N : ℝ))) := by
  exact
    (Complex.measurable_norm_binetAbelPlanaFiniteLowerContourTail_integrand
      w).aestronglyMeasurable

/-- Integral comparison for the omitted lower Abel-Plana tail. -/
theorem Complex.norm_binetAbelPlanaFiniteLowerContourTail_le_tailKernelMass
    {w : ℂ}
    (hw : 0 < w.re) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ N : ℕ in Filter.atTop,
          ‖Complex.binetAbelPlanaFiniteLowerContourTail N w‖ ≤
            C * ∫ t : ℝ in Set.Ioi (N : ℝ),
              Complex.binetAbelPlanaVerticalKernelMajorant t := by
  match
    Complex.norm_binetAbelPlanaFiniteLowerContourTail_integrand_le_majorant
      hw with
  | ⟨C, hC_nonneg, hC⟩ =>
    have hbound :
        ∀ᶠ N : ℕ in Filter.atTop,
          ‖Complex.binetAbelPlanaFiniteLowerContourTail N w‖ ≤
            C * ∫ t : ℝ in Set.Ioi (N : ℝ),
              Complex.binetAbelPlanaVerticalKernelMajorant t := by
      exact
        hC.mono
          (fun N hN =>
            by
              have htail_subset :
                  Set.Ioi (N : ℝ) ⊆ Set.Ioi (0 : ℝ) := by
                exact fun _t ht => lt_of_le_of_lt (Nat.cast_nonneg N) ht
              have hCK_integrable :
                  IntegrableOn
                    (fun t : ℝ =>
                      C * Complex.binetAbelPlanaVerticalKernelMajorant t)
                    (Set.Ioi (N : ℝ)) :=
                (Complex.binetAbelPlanaVerticalKernelMajorant_integrableOn.mono_set
                  htail_subset).const_mul C
              have hnorm_meas :
                  AEStronglyMeasurable
                    (fun t : ℝ =>
                      ‖(-Complex.I) *
                        ((Complex.log (w + (t : ℂ) * Complex.I) -
                            Complex.log (w - (t : ℂ) * Complex.I)) /
                          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))‖)
                    (volume.restrict (Set.Ioi (N : ℝ))) :=
                Complex.aestronglyMeasurable_norm_binetAbelPlanaFiniteLowerContourTail_integrand
                  N w
              have hnorm_integrable :
                  IntegrableOn
                    (fun t : ℝ =>
                      ‖(-Complex.I) *
                        ((Complex.log (w + (t : ℂ) * Complex.I) -
                            Complex.log (w - (t : ℂ) * Complex.I)) /
                          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))‖)
                    (Set.Ioi (N : ℝ)) := by
                have hpointwise :
                    ∀ᵐ (t : ℝ) ∂volume.restrict (Set.Ioi (N : ℝ)),
                      ‖‖(-Complex.I) *
                        ((Complex.log (w + (t : ℂ) * Complex.I) -
                            Complex.log (w - (t : ℂ) * Complex.I)) /
                          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))‖‖ ≤
                        C * Complex.binetAbelPlanaVerticalKernelMajorant t := by
                  exact
                    hN.mono
                      (fun (t : ℝ) ht =>
                        by
                          have hnorm_nonneg :
                              0 ≤
                                ‖(-Complex.I) *
                                  ((Complex.log (w + (t : ℂ) * Complex.I) -
                                      Complex.log (w - (t : ℂ) * Complex.I)) /
                                    (Complex.exp
                                        (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) -
                                      1))‖ :=
                            norm_nonneg _
                          exact (Real.norm_of_nonneg hnorm_nonneg).symm ▸ ht)
                exact hCK_integrable.mono' hnorm_meas hpointwise
              have hmono :
                  ∫ t : ℝ in Set.Ioi (N : ℝ),
                      ‖(-Complex.I) *
                        ((Complex.log (w + (t : ℂ) * Complex.I) -
                            Complex.log (w - (t : ℂ) * Complex.I)) /
                          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))‖ ≤
                    ∫ t : ℝ in Set.Ioi (N : ℝ),
                      C * Complex.binetAbelPlanaVerticalKernelMajorant t :=
                setIntegral_mono_ae_restrict
                  hnorm_integrable
                  hCK_integrable
                  hN
              have hconst :
                  ∫ t : ℝ in Set.Ioi (N : ℝ),
                      C * Complex.binetAbelPlanaVerticalKernelMajorant t =
                    C * ∫ t : ℝ in Set.Ioi (N : ℝ),
                      Complex.binetAbelPlanaVerticalKernelMajorant t := by
                exact integral_smul C
                  Complex.binetAbelPlanaVerticalKernelMajorant
              have hnorm_integral :
                  ‖Complex.binetAbelPlanaFiniteLowerContourTail N w‖ ≤
                    ∫ t : ℝ in Set.Ioi (N : ℝ),
                      ‖(-Complex.I) *
                        ((Complex.log (w + (t : ℂ) * Complex.I) -
                            Complex.log (w - (t : ℂ) * Complex.I)) /
                          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))‖ := by
                have htail_unfold :
                    Complex.binetAbelPlanaFiniteLowerContourTail N w =
                      ∫ t : ℝ in Set.Ioi (N : ℝ),
                        (-Complex.I) *
                          ((Complex.log (w + (t : ℂ) * Complex.I) -
                              Complex.log (w - (t : ℂ) * Complex.I)) /
                            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)) :=
                  Complex.binetAbelPlanaFiniteLowerContourTail_core_unfold N w
                calc
                  ‖Complex.binetAbelPlanaFiniteLowerContourTail N w‖ =
                      ‖∫ t : ℝ in Set.Ioi (N : ℝ),
                        (-Complex.I) *
                          ((Complex.log (w + (t : ℂ) * Complex.I) -
                              Complex.log (w - (t : ℂ) * Complex.I)) /
                            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))‖ := by
                    exact congrArg norm htail_unfold
                  _ ≤ ∫ t : ℝ in Set.Ioi (N : ℝ),
                      ‖(-Complex.I) *
                        ((Complex.log (w + (t : ℂ) * Complex.I) -
                            Complex.log (w - (t : ℂ) * Complex.I)) /
                          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))‖ :=
                    norm_integral_le_integral_norm _
              exact hnorm_integral.trans (hmono.trans_eq hconst))
    exact Exists.intro C (And.intro hC_nonneg hbound)

/-- Owner lower-tail estimate in fixed-ray kernel-tail form. -/
theorem Complex.exists_norm_binetAbelPlanaFiniteLowerContourTail_le_kernelTail_owner
    {w : ℂ}
    (hw : 0 < w.re) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ N : ℕ in Filter.atTop,
          ‖Complex.binetAbelPlanaFiniteLowerContourTail N w‖ ≤
            C * ∫ t : ℝ in Set.Ioi (N : ℝ),
              Complex.binetAbelPlanaVerticalKernelMajorant t := by
  exact
    Complex.norm_binetAbelPlanaFiniteLowerContourTail_le_tailKernelMass
      hw

end

end LFunctions
end Boundary
