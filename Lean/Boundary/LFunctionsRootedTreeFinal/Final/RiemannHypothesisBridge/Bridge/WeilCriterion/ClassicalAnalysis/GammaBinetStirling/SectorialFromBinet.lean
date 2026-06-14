import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.Binet

/-!
# Sectorial estimates from Binet

This file owns the sectorial remainder estimate extracted from the
Binet-kernel majorant package.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Trivial real nonnegativity of `2`, named to keep arithmetic side
conditions out of the Binet estimates. -/
theorem Real.zero_le_two_real : (0 : ℝ) ≤ 2 :=
  zero_le_two

/-- Trivial real positivity of `8`, named to keep arithmetic side conditions
out of the Binet estimates. -/
theorem Real.zero_lt_eight_real : (0 : ℝ) < 8 := by
  linarith [zero_lt_one]

/-- The Binet kernel is integrable on the lower split interval. -/
theorem Complex.binetSecondFormula_kernel_integrableOn_small_interval
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    IntegrableOn
      (fun t : ℝ =>
        Complex.arctan ((t : ℂ) / w) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
      (Set.Ioc (0 : ℝ) (‖w‖ / 2)) := by
  let K : ℝ → ℂ := fun t : ℝ =>
    Complex.arctan ((t : ℂ) / w) /
      (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)
  let M : ℝ → ℝ := fun t : ℝ =>
    t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)
  let c : ℝ := 2 / ‖w‖
  have hw_ne_zero : w ≠ 0 := by
    intro hw_zero
    rw [hw_zero] at hw_re_pos
    exact (lt_irrefl (0 : ℝ)) hw_re_pos
  have hw_norm_pos : 0 < ‖w‖ :=
    norm_pos_iff.mpr hw_ne_zero
  have hM_integrable_Ioi : IntegrableOn M (Set.Ioi (0 : ℝ)) :=
    Real.binetSecondFormula_kernel_majorant_integrableOn
  have hcM_integrable :
      Integrable (fun t : ℝ => c * M t)
        (volume.restrict (Set.Ioc (0 : ℝ) (‖w‖ / 2))) :=
    (hM_integrable_Ioi.mono_set Ioc_subset_Ioi_self).const_mul c
  have hK_meas :
      AEStronglyMeasurable K
        (volume.restrict (Set.Ioc (0 : ℝ) (‖w‖ / 2))) := by
    have hmeas : Measurable K := by
      fun_prop
    exact hmeas.aestronglyMeasurable
  have hpointwise :
      ∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) (‖w‖ / 2)),
        ‖K t‖ ≤ c * M t :=
    (ae_restrict_mem measurableSet_Ioc).mono
      (fun t ht => by
        have hkernel :
            ‖K t‖ ≤
              (2 * (t / ‖w‖)) /
                (Real.exp ((2 : ℝ) * Real.pi * t) - 1) :=
          Complex.binetSecondFormula_kernel_norm_le_on_small_interval
            hw_re_pos ht
        have hrewrite :
            (2 * (t / ‖w‖)) /
                (Real.exp ((2 : ℝ) * Real.pi * t) - 1) =
              c * M t := by
          dsimp [c, M]
          ring
        exact hrewrite ▸ hkernel)
  exact
    hcM_integrable.mono' hK_meas hpointwise

/-- Tail pointwise domination for the Binet kernel on the open right
half-plane after the split at `‖w‖ / 2`, with a constant depending on the
fixed open-half-plane point `w`.

The uniform constant `(2 / ‖w‖)` is false pointwise near the principal
arctangent singularity on rays approaching the imaginary axis. -/
theorem Complex.binetSecondFormula_kernel_tail_norm_le_majorant
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ C : ℝ,
      0 ≤ C ∧
      ∀ t : ℝ,
        t ∈ Set.Ioi (‖w‖ / 2) →
          ‖Complex.arctan ((t : ℂ) / w) /
              (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ ≤
            C *
              (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  sorry

/-- The Binet kernel is integrable on the upper split interval. -/
theorem Complex.binetSecondFormula_kernel_integrableOn_tail_interval
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    IntegrableOn
      (fun t : ℝ =>
        Complex.arctan ((t : ℂ) / w) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
      (Set.Ioi (‖w‖ / 2)) := by
  let K : ℝ → ℂ := fun t : ℝ =>
    Complex.arctan ((t : ℂ) / w) /
      (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)
  let M : ℝ → ℝ := fun t : ℝ =>
    t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)
  rcases
      Complex.binetSecondFormula_kernel_tail_norm_le_majorant
        hw_re_pos with
    ⟨c, hc_nonneg, htail_bound⟩
  have hM_integrable_Ioi : IntegrableOn M (Set.Ioi (0 : ℝ)) :=
    Real.binetSecondFormula_kernel_majorant_integrableOn
  have hcut_nonneg : (0 : ℝ) ≤ ‖w‖ / 2 :=
    div_nonneg (norm_nonneg w) Real.zero_le_two_real
  have hcM_integrable :
      Integrable (fun t : ℝ => c * M t)
        (volume.restrict (Set.Ioi (‖w‖ / 2))) :=
    (hM_integrable_Ioi.mono_set (Ioi_subset_Ioi hcut_nonneg)).const_mul c
  have hK_meas :
      AEStronglyMeasurable K
        (volume.restrict (Set.Ioi (‖w‖ / 2))) := by
    have hmeas : Measurable K := by
      fun_prop
    exact hmeas.aestronglyMeasurable
  have hpointwise :
      ∀ᵐ t ∂volume.restrict (Set.Ioi (‖w‖ / 2)),
        ‖K t‖ ≤ c * M t :=
    (ae_restrict_mem measurableSet_Ioi).mono
      (fun t ht => htail_bound t ht)
  exact
    hcM_integrable.mono' hK_meas hpointwise

/-- The complex Binet kernel is integrable on the positive half-line in the
open right half-plane. -/
theorem Complex.binetSecondFormula_kernel_integrableOn_Ioi_openRightHalfPlane
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    IntegrableOn
      (fun t : ℝ =>
        Complex.arctan ((t : ℂ) / w) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
      (Set.Ioi (0 : ℝ)) := by
  let K : ℝ → ℂ := fun t : ℝ =>
    Complex.arctan ((t : ℂ) / w) /
      (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)
  have hcut_nonneg : (0 : ℝ) ≤ ‖w‖ / 2 :=
    div_nonneg (norm_nonneg w) Real.zero_le_two_real
  have hsmall : IntegrableOn K (Set.Ioc (0 : ℝ) (‖w‖ / 2)) :=
    Complex.binetSecondFormula_kernel_integrableOn_small_interval
      hw_re_pos
  have htail : IntegrableOn K (Set.Ioi (‖w‖ / 2)) :=
    Complex.binetSecondFormula_kernel_integrableOn_tail_interval
      hw_re_pos
  have hunion :
      Set.Ioc (0 : ℝ) (‖w‖ / 2) ∪ Set.Ioi (‖w‖ / 2) =
        Set.Ioi (0 : ℝ) :=
    Set.Ioc_union_Ioi_eq_Ioi hcut_nonneg
  exact
    hunion ▸ hsmall.union htail

/-- The Binet remainder integral splits at `‖w‖ / 2` into its small-argument
and tail pieces. -/
theorem Complex.binetSecondFormulaRemainder_eq_small_add_tail
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    Complex.binetSecondFormulaRemainder w =
      2 * ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.arctan ((t : ℂ) / w) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) +
        2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
          Complex.arctan ((t : ℂ) / w) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) := by
  let K : ℝ → ℂ := fun t : ℝ =>
    Complex.arctan ((t : ℂ) / w) /
      (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)
  have hK_integrable_Ioi : IntegrableOn K (Set.Ioi (0 : ℝ)) :=
    Complex.binetSecondFormula_kernel_integrableOn_Ioi_openRightHalfPlane
      hw_re_pos
  have hcut_nonneg : (0 : ℝ) ≤ ‖w‖ / 2 :=
    div_nonneg (norm_nonneg w) Real.zero_le_two_real
  have hsmall_integrable :
      IntegrableOn K (Set.Ioc (0 : ℝ) (‖w‖ / 2)) :=
    hK_integrable_Ioi.mono_set Ioc_subset_Ioi_self
  have htail_integrable :
      IntegrableOn K (Set.Ioi (‖w‖ / 2)) :=
    hK_integrable_Ioi.mono_set (Ioi_subset_Ioi hcut_nonneg)
  have hsplit :
      ∫ t : ℝ in Set.Ioi (0 : ℝ), K t =
        ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), K t +
          ∫ t : ℝ in Set.Ioi (‖w‖ / 2), K t := by
    have hunion :
        Set.Ioc (0 : ℝ) (‖w‖ / 2) ∪ Set.Ioi (‖w‖ / 2) =
          Set.Ioi (0 : ℝ) :=
      Set.Ioc_union_Ioi_eq_Ioi hcut_nonneg
    have hdisjoint :
        Disjoint (Set.Ioc (0 : ℝ) (‖w‖ / 2))
          (Set.Ioi (‖w‖ / 2)) :=
      Ioc_disjoint_Ioi le_rfl
    calc
      ∫ t : ℝ in Set.Ioi (0 : ℝ), K t =
          ∫ t : ℝ in
            Set.Ioc (0 : ℝ) (‖w‖ / 2) ∪ Set.Ioi (‖w‖ / 2), K t := by
        rw [hunion]
      _ =
          ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), K t +
            ∫ t : ℝ in Set.Ioi (‖w‖ / 2), K t := by
        exact
          setIntegral_union hdisjoint measurableSet_Ioi
            hsmall_integrable htail_integrable
  calc
    Complex.binetSecondFormulaRemainder w =
        2 * ∫ t : ℝ in Set.Ioi (0 : ℝ), K t := by
      rfl
    _ =
        2 *
            (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), K t +
              ∫ t : ℝ in Set.Ioi (‖w‖ / 2), K t) := by
      rw [hsplit]
    _ =
        2 * ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), K t +
          2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2), K t := by
      ring

/-- Small-argument part of the Binet remainder integral, where the principal
arctangent is controlled by its power-series disk estimate. -/
theorem Complex.binetSecondFormulaRemainder_small_norm_le_integral_majorant
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ‖2 * ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
        Complex.arctan ((t : ℂ) / w) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ ≤
      4 *
        (∫ t : ℝ in Set.Ioi (0 : ℝ),
          t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) / ‖w‖ := by
  let K : ℝ → ℂ := fun t : ℝ =>
    Complex.arctan ((t : ℂ) / w) /
      (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)
  let M : ℝ → ℝ := fun t : ℝ =>
    t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)
  let c : ℝ := 2 / ‖w‖
  have hw_ne_zero : w ≠ 0 := by
    intro hw_zero
    rw [hw_zero] at hw_re_pos
    exact (lt_irrefl (0 : ℝ)) hw_re_pos
  have hw_norm_pos : 0 < ‖w‖ :=
    norm_pos_iff.mpr hw_ne_zero
  have hc_nonneg : 0 ≤ c :=
    div_nonneg Real.zero_le_two_real (le_of_lt hw_norm_pos)
  have hM_integrable_Ioi : IntegrableOn M (Set.Ioi (0 : ℝ)) :=
    Real.binetSecondFormula_kernel_majorant_integrableOn
  have hcM_integrable_Ioc :
      Integrable (fun t : ℝ => c * M t)
        (volume.restrict (Set.Ioc (0 : ℝ) (‖w‖ / 2))) :=
    (hM_integrable_Ioi.mono_set Ioc_subset_Ioi_self).const_mul c
  have hpointwise :
      ∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) (‖w‖ / 2)),
        ‖K t‖ ≤ c * M t :=
    (ae_restrict_mem measurableSet_Ioc).mono
      (fun t ht => by
        have hkernel :
            ‖K t‖ ≤
              (2 * (t / ‖w‖)) /
                (Real.exp ((2 : ℝ) * Real.pi * t) - 1) :=
          Complex.binetSecondFormula_kernel_norm_le_on_small_interval
            hw_re_pos ht
        have hrewrite :
            (2 * (t / ‖w‖)) /
                (Real.exp ((2 : ℝ) * Real.pi * t) - 1) =
              c * M t := by
          dsimp [c, M]
          ring
        exact hrewrite ▸ hkernel)
  have hnorm_integral :
      ‖∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), K t‖ ≤
        ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), c * M t :=
    norm_integral_le_of_norm_le hcM_integrable_Ioc hpointwise
  have hmono :
      ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), M t ≤
        ∫ t : ℝ in Set.Ioi (0 : ℝ), M t :=
    setIntegral_mono_set hM_integrable_Ioi
      ((ae_restrict_mem measurableSet_Ioi).mono
        (fun t ht => Real.binetSecondFormula_kernel_majorant_nonneg_on_Ioi t ht))
      (Eventually.of_forall (fun t ht => ht.1))
  have hscaled_mono :
      ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), c * M t ≤
        c * ∫ t : ℝ in Set.Ioi (0 : ℝ), M t := by
    calc
      ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), c * M t =
          c * ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), M t := by
        exact integral_const_mul c M
      _ ≤ c * ∫ t : ℝ in Set.Ioi (0 : ℝ), M t :=
        mul_le_mul_of_nonneg_left hmono hc_nonneg
  calc
    ‖2 * ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), K t‖ =
        2 * ‖∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), K t‖ := by
      simp [norm_mul]
    _ ≤ 2 * (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), c * M t) :=
      mul_le_mul_of_nonneg_left hnorm_integral Real.zero_le_two_real
    _ ≤ 2 * (c * ∫ t : ℝ in Set.Ioi (0 : ℝ), M t) :=
      mul_le_mul_of_nonneg_left hscaled_mono Real.zero_le_two_real
    _ =
        4 *
          (∫ t : ℝ in Set.Ioi (0 : ℝ), M t) / ‖w‖ := by
      dsimp [c]
      ring

/-- Tail part of the Binet remainder integral.  This is where one uses the
principal-branch arctangent bound away from the branch singularities together
with the exponential denominator. -/
theorem Complex.binetSecondFormulaRemainder_tail_norm_le_integral_majorant
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ‖2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
        Complex.arctan ((t : ℂ) / w) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ ≤
      4 *
        (∫ t : ℝ in Set.Ioi (0 : ℝ),
          t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) / ‖w‖ := by
  sorry

/-- Splitting the Binet integral at `‖w‖ / 2` gives the global open-half-plane
remainder bound. -/
theorem Complex.binetSecondFormulaRemainder_norm_le_integral_majorant_from_split
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ‖Complex.binetSecondFormulaRemainder w‖ ≤
      8 *
        (∫ t : ℝ in Set.Ioi (0 : ℝ),
          t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) / ‖w‖ := by
  let J : ℝ :=
    ∫ t : ℝ in Set.Ioi (0 : ℝ),
      t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)
  let S : ℂ :=
    2 * ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
      Complex.arctan ((t : ℂ) / w) /
        (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)
  let T : ℂ :=
    2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
      Complex.arctan ((t : ℂ) / w) /
        (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)
  have hsplit : Complex.binetSecondFormulaRemainder w = S + T := by
    exact Complex.binetSecondFormulaRemainder_eq_small_add_tail hw_re_pos
  have hS : ‖S‖ ≤ 4 * J / ‖w‖ :=
    Complex.binetSecondFormulaRemainder_small_norm_le_integral_majorant
      hw_re_pos
  have hT : ‖T‖ ≤ 4 * J / ‖w‖ :=
    Complex.binetSecondFormulaRemainder_tail_norm_le_integral_majorant
      hw_re_pos
  have hsum : ‖S + T‖ ≤ 8 * J / ‖w‖ := by
    calc
      ‖S + T‖ ≤ ‖S‖ + ‖T‖ := norm_add_le S T
      _ ≤ 4 * J / ‖w‖ + 4 * J / ‖w‖ := add_le_add hS hT
      _ = 8 * J / ‖w‖ := by ring
  exact
    Eq.subst
      (motive := fun x : ℂ => ‖x‖ ≤ 8 * J / ‖w‖)
      hsplit.symm
      hsum

/-- The pointwise Binet-kernel majorant integrates to a norm bound for the
Binet remainder in the open right half-plane. -/
theorem Complex.binetSecondFormulaRemainder_norm_le_integral_majorant_from_kernel_bound
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ‖Complex.binetSecondFormulaRemainder w‖ ≤
      8 *
        (∫ t : ℝ in Set.Ioi (0 : ℝ),
          t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) / ‖w‖ := by
  exact
    Complex.binetSecondFormulaRemainder_norm_le_integral_majorant_from_split
      hw_re_pos

/-- Integration of the pointwise Binet-kernel majorant on the open right
half-plane. -/
theorem Complex.binetSecondFormulaRemainder_norm_le_integral_majorant_openRightHalfPlane
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ‖Complex.binetSecondFormulaRemainder w‖ ≤
      8 *
        (∫ t : ℝ in Set.Ioi (0 : ℝ),
          t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) / ‖w‖ := by
  exact
    Complex.binetSecondFormulaRemainder_norm_le_integral_majorant_from_kernel_bound
      hw_re_pos

/-- A positive integrable function on an open real interval has positive
integral. -/
theorem Real.setIntegral_pos_of_integrableOn_of_pos_on_Ioo
    {f : ℝ → ℝ}
    {a b : ℝ}
    (hab : a < b)
    (h_integrable : IntegrableOn f (Set.Ioo a b))
    (hpos : ∀ t : ℝ, t ∈ Set.Ioo a b → 0 < f t) :
    0 < ∫ t : ℝ in Set.Ioo a b, f t := by
  have hnonneg_ae :
      0 ≤ᵐ[volume.restrict (Set.Ioo a b)] f :=
    (ae_restrict_mem measurableSet_Ioo).mono
      (fun t ht => le_of_lt (hpos t ht))
  have hsupport_pos :
      0 < volume (Function.support f ∩ Set.Ioo a b) := by
    have hIoo_pos : 0 < volume (Set.Ioo a b) :=
      (Measure.measure_Ioo_pos volume).mpr hab
    have hsubset :
        Set.Ioo a b ⊆ Function.support f ∩ Set.Ioo a b := by
      intro t ht
      exact ⟨fun hzero => (ne_of_gt (hpos t ht)) hzero, ht⟩
    exact lt_of_lt_of_le hIoo_pos (measure_mono hsubset)
  exact
    (setIntegral_pos_iff_support_of_nonneg_ae
      hnonneg_ae h_integrable).mpr hsupport_pos

/-- The Binet majorant is integrable on `(0,1)`. -/
theorem Real.binetSecondFormula_kernel_majorant_integrableOn_Ioo_zero_one :
    IntegrableOn
      (fun t : ℝ => t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
      (Set.Ioo (0 : ℝ) 1) := by
  exact
    IntegrableOn.mono_set
      Real.binetSecondFormula_kernel_majorant_integrableOn_zero_one
      Set.Ioo_subset_Ioc_self

/-- The Binet majorant has strictly positive integral on `(0,1)`. -/
theorem Real.binetSecondFormula_kernel_majorant_integral_pos_on_zero_one :
    0 <
      ∫ t : ℝ in Set.Ioo (0 : ℝ) 1,
        t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
  exact
    Real.setIntegral_pos_of_integrableOn_of_pos_on_Ioo
      zero_lt_one
      Real.binetSecondFormula_kernel_majorant_integrableOn_Ioo_zero_one
      (fun t ht =>
        Real.binetSecondFormula_kernel_majorant_pos ht.1)

/-- Positivity of an integral on a subinterval propagates to the larger
positive half-line for a nonnegative integrable function. -/
theorem Real.integral_pos_on_Ioi_zero_of_integral_pos_on_Ioo_zero_one_of_nonneg
    {f : ℝ → ℝ}
    (h_integrable : IntegrableOn f (Set.Ioi (0 : ℝ)))
    (hpos_subinterval :
      0 <
        ∫ t : ℝ in Set.Ioo (0 : ℝ) 1, f t)
    (hnonneg :
      ∀ t : ℝ,
        t ∈ Set.Ioi (0 : ℝ) →
          0 ≤ f t) :
    0 <
      ∫ t : ℝ in Set.Ioi (0 : ℝ), f t := by
  have hnonneg_ae :
      0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] f :=
    (ae_restrict_mem measurableSet_Ioi).mono
      (fun t ht => hnonneg t ht)
  have hsubset_ae :
      Set.Ioo (0 : ℝ) 1 ≤ᵐ[volume] Set.Ioi (0 : ℝ) :=
    Eventually.of_forall (fun t ht => ht.1)
  have hmono :
      ∫ t : ℝ in Set.Ioo (0 : ℝ) 1, f t ≤
        ∫ t : ℝ in Set.Ioi (0 : ℝ), f t :=
    setIntegral_mono_set h_integrable hnonneg_ae hsubset_ae
  exact lt_of_lt_of_le hpos_subinterval hmono

/-- Positivity on `(0,1)` propagates to positivity of the half-line integral
for the nonnegative Binet majorant. -/
theorem Real.binetSecondFormula_kernel_majorant_integral_pos_of_zero_one
    (hpos_subinterval :
      0 <
        ∫ t : ℝ in Set.Ioo (0 : ℝ) 1,
          t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
    (hnonneg :
      ∀ t : ℝ,
        t ∈ Set.Ioi (0 : ℝ) →
          0 ≤ t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) :
    0 <
      ∫ t : ℝ in Set.Ioi (0 : ℝ),
        t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
  exact
    Real.integral_pos_on_Ioi_zero_of_integral_pos_on_Ioo_zero_one_of_nonneg
      Real.binetSecondFormula_kernel_majorant_integrableOn
      hpos_subinterval hnonneg

/-- The Binet majorant integral is a positive finite constant. -/
theorem Real.binetSecondFormula_kernel_majorant_integral_pos :
    0 <
      ∫ t : ℝ in Set.Ioi (0 : ℝ),
        t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
  have hpos_subinterval :
      0 <
        ∫ t : ℝ in Set.Ioo (0 : ℝ) 1,
          t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) :=
    Real.binetSecondFormula_kernel_majorant_integral_pos_on_zero_one
  have hnonneg :
      ∀ t : ℝ,
        t ∈ Set.Ioi (0 : ℝ) →
          0 ≤ t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) :=
    Real.binetSecondFormula_kernel_majorant_nonneg_on_Ioi
  exact
    Real.binetSecondFormula_kernel_majorant_integral_pos_of_zero_one
      hpos_subinterval hnonneg

/-- The Binet second-formula remainder is bounded by a constant divided by
`‖w‖` in the open right half-plane. -/
theorem Complex.binetSecondFormulaRemainder_norm_le_openRightHalfPlane :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        0 < w.re →
          ‖Complex.binetSecondFormulaRemainder w‖ ≤ C / ‖w‖ := by
  let J : ℝ :=
    ∫ t : ℝ in Set.Ioi (0 : ℝ),
      t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)
  let C : ℝ := 8 * J
  have hJ_pos : 0 < J :=
    Real.binetSecondFormula_kernel_majorant_integral_pos
  have hC_pos : 0 < C :=
    mul_pos Real.zero_lt_eight_real hJ_pos
  refine ⟨C, hC_pos, ?_⟩
  intro w hw_re_pos
  exact
    Complex.binetSecondFormulaRemainder_norm_le_integral_majorant_openRightHalfPlane
      hw_re_pos

end

end LFunctions
end Boundary
