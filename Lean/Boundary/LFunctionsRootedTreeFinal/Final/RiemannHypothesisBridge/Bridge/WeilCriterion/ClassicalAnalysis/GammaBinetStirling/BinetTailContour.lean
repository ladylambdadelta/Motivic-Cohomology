import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlana
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.Binet.Derivatives.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.SectorialFromBinet
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Binet tail contour package

This file owns the tail split and contour-deformed full-sector tail comparison
for Binet's second formula.  Zeta normalization files should consume this
classical package rather than own the branch-contour analysis.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology
open MeasureTheory

/-- The lower Binet remainder piece after splitting at `‖w‖ / 2`.

This is the small-argument range where the power-series arctangent estimate
gives the explicit `1 / ‖w‖` factor. -/
noncomputable def Complex.binetSecondFormulaSmallRemainder (w : ℂ) : ℂ :=
  2 * ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
    Complex.arctan ((t : ℂ) / w) /
      (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)

/-- The upper Binet remainder piece after splitting at `‖w‖ / 2`.

This is the only remaining full-sector obstruction: the existing pointwise
principal-arctangent bound supplies either a fixed-`w` constant, or a uniform
constant after wedge separation.  The full closed-right-half-plane owner API
needs this tail to decay like `1 / ‖w‖` without a wedge hypothesis. -/
noncomputable def Complex.binetSecondFormulaTailRemainder (w : ℂ) : ℂ :=
  2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
    Complex.arctan ((t : ℂ) / w) /
      (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)

/-- The Binet tail remainder is exactly twice the integral of the principal
tail kernel. -/
theorem Complex.binetSecondFormulaTailRemainder_eq_principalTailKernel_integral
    (w : ℂ) :
    Complex.binetSecondFormulaTailRemainder w =
      2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
        Complex.binetSecondFormulaPrincipalTailKernel w t := by
  rfl

/-- The principal tail kernel is definitionally the arctangent-over-exponential
Binet kernel. -/
theorem Complex.binetSecondFormulaPrincipalTailKernel_fun_eq
    (w : ℂ) :
    (fun t : ℝ => Complex.binetSecondFormulaPrincipalTailKernel w t) =
      fun t : ℝ =>
        Complex.arctan ((t : ℂ) / w) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) := by
  rfl

/-- The principal tail kernel is integrable on the split tail in the open
right half-plane. -/
theorem Complex.binetSecondFormulaPrincipalTailKernel_integrableOn_tail
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    IntegrableOn
      (fun t : ℝ => Complex.binetSecondFormulaPrincipalTailKernel w t)
      (Set.Ioi (‖w‖ / 2)) := by
  exact
    Complex.binetSecondFormula_arctanKernel_integrableOn_tail_interval
      (w := w) hw_re_pos

/-- The norm of the Binet tail remainder is bounded by twice the integral of
the norm of the principal tail kernel. -/
theorem Complex.binetSecondFormulaTailRemainder_norm_le_principalTailKernel_norm_integral
    {w : ℂ}
    (_hw_re_pos : 0 < w.re) :
    ‖Complex.binetSecondFormulaTailRemainder w‖ ≤
      2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
        ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ := by
  let K : ℝ → ℂ := fun t : ℝ =>
    Complex.binetSecondFormulaPrincipalTailKernel w t
  have hnorm_integral :
      ‖∫ t : ℝ in Set.Ioi (‖w‖ / 2), K t‖ ≤
        ∫ t : ℝ in Set.Ioi (‖w‖ / 2), ‖K t‖ :=
    norm_integral_le_integral_norm _
  have htail_eq :
      Complex.binetSecondFormulaTailRemainder w =
        2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2), K t :=
    Complex.binetSecondFormulaTailRemainder_eq_principalTailKernel_integral w
  calc
    ‖Complex.binetSecondFormulaTailRemainder w‖ =
        ‖2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2), K t‖ := by
      exact congrArg norm htail_eq
    _ = 2 * ‖∫ t : ℝ in Set.Ioi (‖w‖ / 2), K t‖ := by
      have htwo : ‖(2 : ℂ)‖ = (2 : ℝ) := by
        exact Complex.norm_two
      calc
        ‖2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2), K t‖ =
            ‖(2 : ℂ)‖ * ‖∫ t : ℝ in Set.Ioi (‖w‖ / 2), K t‖ := by
          exact norm_mul _ _
        _ = 2 * ‖∫ t : ℝ in Set.Ioi (‖w‖ / 2), K t‖ := by
          exact congrArg (fun x : ℝ => x * ‖∫ t : ℝ in Set.Ioi (‖w‖ / 2), K t‖) htwo
    _ ≤ 2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2), ‖K t‖ :=
      mul_le_mul_of_nonneg_left hnorm_integral zero_le_two

/-- Fixed-`w` integrated tail control for the Binet tail remainder.

This is the honest consequence of the existing principal-branch arctangent
tail bound: the constant may depend on `w`.  The full-sector C5 obstruction is
therefore strictly stronger; it asks for a uniform constant with an explicit
`1 / ‖w‖` factor. -/
theorem Complex.binetSecondFormulaTailRemainder_norm_le_fixed_integral_majorant
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ C : ℝ,
      0 ≤ C ∧
      ‖Complex.binetSecondFormulaTailRemainder w‖ ≤
        2 * C *
          (∫ t : ℝ in Set.Ioi (0 : ℝ),
            t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  match
    Complex.binetSecondFormulaRemainder_tail_norm_le_integral_majorant
      (w := w) hw_re_pos with
  | ⟨C, hC_nonneg, htail⟩ =>
      have htail_eq :
          Complex.binetSecondFormulaTailRemainder w =
            2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
              Complex.arctan ((t : ℂ) / w) /
                (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) :=
        Eq.refl (Complex.binetSecondFormulaTailRemainder w)
      have hnorm_transport :
          ‖Complex.binetSecondFormulaTailRemainder w‖ =
            ‖2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
              Complex.arctan ((t : ℂ) / w) /
                (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ :=
        congrArg norm htail_eq
      exact
        Exists.intro C
          (And.intro hC_nonneg
            (Eq.subst
              (motive := fun x : ℝ =>
                x ≤ 2 * C *
                  (∫ t : ℝ in Set.Ioi (0 : ℝ),
                    t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)))
              hnorm_transport.symm
              htail))

/-- On a fixed wedge of the open right half-plane, the principal tail kernel
has the scaled pointwise majorant needed by the full `C / ‖w‖` tail estimate.

The wedge separation keeps the arctangent branch uniformly bounded.  The split
tail condition `‖w‖ / 2 < t` then converts that bounded estimate into the
linear scaled estimate `O(t / ‖w‖)`. -/
theorem Complex.binetSecondFormulaPrincipalTailKernel_norm_le_sectorSeparated_scaled_majorant
    (ε : ℝ)
    (hε : 0 < ε) :
    ∃ C : ℝ,
      0 ≤ C ∧
      ∀ w : ℂ,
        0 < w.re →
          ε ≤ w.re / ‖w‖ →
          1 ≤ ‖w‖ →
          ∀ t : ℝ,
            t ∈ Set.Ioi (‖w‖ / 2) →
              ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ ≤
                (C / ‖w‖) *
                  (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  match
    Complex.binetSecondFormula_arctan_tail_bounded_sectorSeparated ε hε with
  | ⟨B, hB_nonneg, hB⟩ =>
      refine ⟨2 * B, mul_nonneg Real.zero_le_two_real hB_nonneg, ?_⟩
      intro w hw_re_pos hw_sep hw_large t ht_tail
      let D : ℝ := Real.exp ((2 : ℝ) * Real.pi * t) - 1
      have hw_norm_pos : 0 < ‖w‖ :=
        Complex.norm_pos_of_re_pos hw_re_pos
      have hcoeff_nonneg : 0 ≤ (2 * B) / ‖w‖ :=
        div_nonneg (mul_nonneg Real.zero_le_two_real hB_nonneg)
          (le_of_lt hw_norm_pos)
      have ht_lower : ‖w‖ / 2 ≤ t :=
        le_of_lt ht_tail
      have hB_at_cutoff :
          ((2 * B) / ‖w‖) * (‖w‖ / 2) = B :=
        Real.two_mul_div_mul_half_eq (B := B) (r := ‖w‖)
          hw_norm_pos.ne'
      have hB_scaled :
          B ≤ ((2 * B) / ‖w‖) * t := by
        calc
          B = ((2 * B) / ‖w‖) * (‖w‖ / 2) :=
            hB_at_cutoff.symm
          _ ≤ ((2 * B) / ‖w‖) * t :=
            mul_le_mul_of_nonneg_left ht_lower hcoeff_nonneg
      have harctan_scaled :
          ‖Complex.arctan ((t : ℂ) / w)‖ ≤
            ((2 * B) / ‖w‖) * t :=
        le_trans (hB w hw_re_pos hw_sep t ht_tail) hB_scaled
      have ht_pos : 0 < t :=
        lt_of_le_of_lt
          (div_nonneg (norm_nonneg w) Real.zero_le_two_real)
          ht_tail
      have hden_norm :
          ‖Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1‖ = D :=
        Complex.exp_tail_denominator_norm_eq t ht_pos
      have hden_nonneg : 0 ≤ D :=
        le_of_lt (Real.binetSecondFormula_exp_denominator_pos ht_pos)
      calc
        ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ =
            ‖Complex.arctan ((t : ℂ) / w) /
              (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ := by
          rfl
        _ =
            ‖Complex.arctan ((t : ℂ) / w)‖ /
              ‖Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1‖ := by
          exact norm_div _ _
        _ = ‖Complex.arctan ((t : ℂ) / w)‖ / D := by
          exact congrArg
            (fun x : ℝ => ‖Complex.arctan ((t : ℂ) / w)‖ / x)
            hden_norm
        _ ≤ (((2 * B) / ‖w‖) * t) / D :=
          div_le_div_of_nonneg_right harctan_scaled hden_nonneg
        _ =
            ((2 * B) / ‖w‖) * (t / D) := by
          exact mul_div_assoc ((2 * B) / ‖w‖) t D

/-- Sector-separated integrated `C / ‖w‖` estimate for the raw principal
Binet tail kernel.

This is a genuine uniform tail estimate on every fixed wedge.  It is still
weaker than the C5 full-sector cancellation estimate because the constant
depends on the wedge separation parameter `ε`. -/
theorem Complex.binetSecondFormula_principalTailKernel_integral_sectorSeparated_scaled_decay
    (ε : ℝ)
    (hε : 0 < ε) :
    ∃ C : ℝ,
      0 ≤ C ∧
      ∀ w : ℂ,
        0 < w.re →
          ε ≤ w.re / ‖w‖ →
          1 ≤ ‖w‖ →
            2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ ≤
              (C / ‖w‖) *
                (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                  t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  match
    Complex.binetSecondFormulaPrincipalTailKernel_norm_le_sectorSeparated_scaled_majorant
      ε hε with
  | ⟨C, hC_nonneg, hpoint⟩ =>
      refine ⟨2 * C, mul_nonneg Real.zero_le_two_real hC_nonneg, ?_⟩
      intro w hw_re_pos hw_sep hw_large
      let M : ℝ → ℝ := fun t : ℝ =>
        t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)
      let P : ℝ → ℝ := fun t : ℝ =>
        ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖
      have hhalf_ge_zero : (0 : ℝ) ≤ ‖w‖ / 2 :=
        div_nonneg (norm_nonneg w) Real.zero_le_two_real
      have hM_integrable :
          IntegrableOn M (Set.Ioi (‖w‖ / 2)) :=
        Real.binetSecondFormula_kernel_majorant_integrableOn.mono_set
          (fun t ht => lt_of_le_of_lt hhalf_ge_zero ht)
      have hscaled_integrable :
          IntegrableOn
            (fun t : ℝ => (C / ‖w‖) * M t)
            (Set.Ioi (‖w‖ / 2)) :=
        hM_integrable.const_mul (C / ‖w‖)
      have hP_integrable :
          IntegrableOn P (Set.Ioi (‖w‖ / 2)) :=
        (Complex.binetSecondFormulaPrincipalTailKernel_integrableOn_tail
          (w := w) hw_re_pos).norm
      have hpoint_ae :
          ∀ᵐ t ∂volume.restrict (Set.Ioi (‖w‖ / 2)),
            P t ≤ (C / ‖w‖) * M t :=
        (ae_restrict_mem measurableSet_Ioi).mono
          (fun t ht => hpoint w hw_re_pos hw_sep hw_large t ht)
      have hintegral :
          ∫ t : ℝ in Set.Ioi (‖w‖ / 2), P t ≤
            ∫ t : ℝ in Set.Ioi (‖w‖ / 2), (C / ‖w‖) * M t :=
        setIntegral_mono_ae_restrict
          hP_integrable
          hscaled_integrable
          hpoint_ae
      have hscale :
          ∫ t : ℝ in Set.Ioi (‖w‖ / 2), (C / ‖w‖) * M t =
            (C / ‖w‖) *
              (∫ t : ℝ in Set.Ioi (‖w‖ / 2), M t) := by
        exact MeasureTheory.integral_mul_left (C / ‖w‖) M
      have htwice :
          2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2), P t ≤
            2 *
              ((C / ‖w‖) *
                (∫ t : ℝ in Set.Ioi (‖w‖ / 2), M t)) := by
        exact
          mul_le_mul_of_nonneg_left
            (le_trans hintegral (le_of_eq hscale))
            Real.zero_le_two_real
      have hconst :
          2 *
              ((C / ‖w‖) *
                (∫ t : ℝ in Set.Ioi (‖w‖ / 2), M t)) =
            ((2 * C) / ‖w‖) *
              (∫ t : ℝ in Set.Ioi (‖w‖ / 2), M t) := by
        calc
          2 *
              ((C / ‖w‖) *
                (∫ t : ℝ in Set.Ioi (‖w‖ / 2), M t)) =
              (2 * (C / ‖w‖)) *
                (∫ t : ℝ in Set.Ioi (‖w‖ / 2), M t) := by
            exact
              (mul_assoc (2 : ℝ) (C / ‖w‖)
                (∫ t : ℝ in Set.Ioi (‖w‖ / 2), M t)).symm
          _ =
              ((2 * C) / ‖w‖) *
                (∫ t : ℝ in Set.Ioi (‖w‖ / 2), M t) := by
            exact congrArg
              (fun x : ℝ =>
                x * (∫ t : ℝ in Set.Ioi (‖w‖ / 2), M t))
              (mul_div_assoc (2 : ℝ) C ‖w‖).symm
      exact
        le_trans htwice (le_of_eq hconst)

/-- Sector-separated principal-tail cancellation estimate in the exact
positive-constant shape needed by the full owner gap.

This is the non-indentation half of the branch-sensitive estimate: away from
the arctangent branch wall, the raw principal tail itself already has the
`C / ‖w‖` integrated decay. -/
theorem Complex.binetSecondFormula_principalTailKernel_integral_cancellation_estimate_sectorSeparated
    (ε : ℝ)
    (hε : 0 < ε) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        0 < w.re →
          ε ≤ w.re / ‖w‖ →
          2 ≤ ‖w‖ →
            2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ ≤
              (C / ‖w‖) *
                (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                  t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  match
    Complex.binetSecondFormula_principalTailKernel_integral_sectorSeparated_scaled_decay
      ε hε with
  | ⟨C, hC_nonneg, hdecay⟩ =>
      refine ⟨C + 1, ?_, ?_⟩
      · exact lt_of_lt_of_le zero_lt_one
          (by
            calc
              (1 : ℝ) = 0 + 1 := (zero_add 1).symm
              _ ≤ C + 1 := add_le_add_right hC_nonneg 1)
      · intro w hw_re_pos hw_sep hw_large
        let J : ℝ :=
          ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
            t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)
        have hw_large_one : 1 ≤ ‖w‖ :=
          le_trans one_le_two hw_large
        have hraw :
            2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ ≤
              (C / ‖w‖) * J :=
          hdecay w hw_re_pos hw_sep hw_large_one
        have hJ_nonneg : 0 ≤ J :=
          integral_nonneg_of_ae
            ((ae_restrict_mem measurableSet_Ioi).mono
              (fun t ht =>
                Real.binetSecondFormula_kernel_majorant_nonneg_on_Ioi t
                  (lt_of_le_of_lt
                    (div_nonneg (norm_nonneg w) Real.zero_le_two_real)
                    ht)))
        have hw_norm_pos : 0 < ‖w‖ :=
          Complex.norm_pos_of_re_pos hw_re_pos
        have hcoeff :
            C / ‖w‖ ≤ (C + 1) / ‖w‖ :=
          div_le_div_of_nonneg_right
            (by
              calc
                C ≤ C + 0 := (add_zero C).symm.le
                _ ≤ C + 1 := add_le_add_left zero_le_one C)
            (le_of_lt hw_norm_pos)
        have hscaled :
            (C / ‖w‖) * J ≤ ((C + 1) / ‖w‖) * J :=
          mul_le_mul_of_nonneg_right hcoeff hJ_nonneg
        exact le_trans hraw hscaled

/-- Full-sector pointwise scaled majorant for the far part of the principal
Binet tail, after the branch-wall window `t ≤ 2‖w‖` has been removed. -/
theorem Complex.binetSecondFormulaPrincipalTailKernel_norm_le_far_scaled_majorant :
    ∃ C : ℝ,
      0 ≤ C ∧
      ∀ w : ℂ,
        0 < w.re →
          ∀ t : ℝ,
            t ∈ Set.Ioi (2 * ‖w‖) →
              ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ ≤
                (C / ‖w‖) *
                  (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  let C : ℝ := max |Real.log (1 / 3 : ℝ)| |Real.log (3 : ℝ)| + Real.pi
  have hC_nonneg : 0 ≤ C :=
    add_nonneg (le_max_of_le_left (abs_nonneg _)) Real.pi_nonneg
  refine ⟨C, hC_nonneg, ?_⟩
  intro w hw_re_pos t ht_far_open
  let D : ℝ := Real.exp ((2 : ℝ) * Real.pi * t) - 1
  let R : ℂ :=
    (1 + ((t : ℂ) / w) * Complex.I) /
      (1 - ((t : ℂ) / w) * Complex.I)
  have hw_norm_pos : 0 < ‖w‖ :=
    Complex.norm_pos_of_re_pos hw_re_pos
  have hw_ne_zero : w ≠ 0 := by
    intro hw_zero
    cases hw_zero
    exact (lt_irrefl (0 : ℝ)) hw_re_pos
  have ht_far : 2 * ‖w‖ ≤ t :=
    le_of_lt ht_far_open
  have ht_pos : 0 < t := by
    have htwo_norm_nonneg : 0 ≤ 2 * ‖w‖ :=
      mul_nonneg zero_le_two (norm_nonneg w)
    exact lt_of_le_of_lt htwo_norm_nonneg ht_far_open
  have hratio :
      (1 / 3 : ℝ) ≤ ‖R‖ ∧ ‖R‖ ≤ (3 : ℝ) := by
    rcases
        Complex.binetSecondFormula_arctan_tail_far_ratio_bounds
          (w := w) (t := t) ht_far with
      ⟨hnum_le, hden_le⟩
    have hden_lower :
        w.re ≤ ‖w - (t : ℂ) * Complex.I‖ :=
      Complex.binetSecondFormula_arctan_tail_ratio_denominator_lower
        hw_re_pos t
    have hden_pos : 0 < ‖w - (t : ℂ) * Complex.I‖ :=
      lt_of_lt_of_le hw_re_pos hden_lower
    constructor
    · have hthird :
          (1 / 3 : ℝ) ≤
            ‖w + (t : ℂ) * Complex.I‖ /
              ‖w - (t : ℂ) * Complex.I‖ := by
        have hmul :
            (1 / 3 : ℝ) *
                ‖w - (t : ℂ) * Complex.I‖ ≤
              (1 / 3 : ℝ) *
                (3 * ‖w + (t : ℂ) * Complex.I‖) :=
          mul_le_mul_of_nonneg_left hden_le
            (div_nonneg zero_le_one (le_of_lt Real.zero_lt_three))
        have hmul' :
            (1 / 3 : ℝ) *
                ‖w - (t : ℂ) * Complex.I‖ ≤
              ‖w + (t : ℂ) * Complex.I‖ :=
          hmul.trans_eq
            (Real.one_div_three_mul_three_mul
              ‖w + (t : ℂ) * Complex.I‖)
        exact (le_div_iff₀ hden_pos).2 hmul'
      calc
        (1 / 3 : ℝ) ≤
            ‖w + (t : ℂ) * Complex.I‖ /
              ‖w - (t : ℂ) * Complex.I‖ := hthird
        _ = ‖R‖ := by
          exact (norm_div _ _).symm.trans
            (Complex.binetSecondFormula_arctan_tail_ratio_eq_norm
              w hw_ne_zero t).symm
    · have hthree :
          ‖w + (t : ℂ) * Complex.I‖ /
              ‖w - (t : ℂ) * Complex.I‖ ≤ 3 := by
        exact (div_le_iff₀ hden_pos).2 hnum_le
      calc
        ‖R‖ =
            ‖w + (t : ℂ) * Complex.I‖ /
              ‖w - (t : ℂ) * Complex.I‖ := by
          exact
            (Complex.binetSecondFormula_arctan_tail_ratio_eq_norm
              w hw_ne_zero t).trans (norm_div _ _)
        _ ≤ 3 := hthree
  have hthird_pos : (0 : ℝ) < 1 / 3 :=
    div_pos zero_lt_one Real.zero_lt_three
  have hthird_le_three : (1 / 3 : ℝ) ≤ 3 :=
    Real.one_div_three_le_three_real
  have hlog :
      ‖Complex.log R‖ ≤ C :=
    Complex.log_norm_le_of_norm_bounds
      hthird_pos hthird_le_three hratio.1 hratio.2
  have harctan :
      ‖Complex.arctan ((t : ℂ) / w)‖ ≤ C := by
    have hfactor_norm_le_one : ‖(-Complex.I / 2 : ℂ)‖ ≤ (1 : ℝ) :=
      Complex.norm_neg_I_div_two_le_one
    have hmul :
        ‖(-Complex.I / 2 : ℂ) * Complex.log R‖ ≤
          ‖Complex.log R‖ := by
      calc
        ‖(-Complex.I / 2 : ℂ) * Complex.log R‖ ≤
            ‖(-Complex.I / 2 : ℂ)‖ * ‖Complex.log R‖ :=
          norm_mul_le _ _
        _ ≤ 1 * ‖Complex.log R‖ :=
          mul_le_mul_of_nonneg_right hfactor_norm_le_one
            (norm_nonneg (Complex.log R))
        _ = ‖Complex.log R‖ :=
          one_mul ‖Complex.log R‖
    calc
      ‖Complex.arctan ((t : ℂ) / w)‖ =
          ‖(-Complex.I / 2 : ℂ) * Complex.log R‖ := by
        exact congrArg norm
          (Complex.binetSecondFormula_arctan_tail_expr_eq w t)
      _ ≤ ‖Complex.log R‖ := hmul
      _ ≤ C := hlog
  have hscaled_arctan :
      ‖Complex.arctan ((t : ℂ) / w)‖ ≤
        (C / ‖w‖) * t := by
    have hnorm_le_t : ‖w‖ ≤ t := by
      have hnorm_le_two_norm : ‖w‖ ≤ 2 * ‖w‖ :=
        le_mul_of_one_le_left (norm_nonneg w) one_le_two
      exact le_trans hnorm_le_two_norm ht_far
    have hC_le_scaled_cutoff : C ≤ (C / ‖w‖) * ‖w‖ := by
      calc
        C = C / ‖w‖ * ‖w‖ :=
          Eq.symm (div_mul_cancel₀ C hw_norm_pos.ne')
        _ ≤ (C / ‖w‖) * ‖w‖ := le_rfl
    have hcoeff_nonneg : 0 ≤ C / ‖w‖ :=
      div_nonneg hC_nonneg (le_of_lt hw_norm_pos)
    calc
      ‖Complex.arctan ((t : ℂ) / w)‖ ≤ C := harctan
      _ ≤ (C / ‖w‖) * ‖w‖ := hC_le_scaled_cutoff
      _ ≤ (C / ‖w‖) * t :=
        mul_le_mul_of_nonneg_left hnorm_le_t hcoeff_nonneg
  have hden_norm :
      ‖Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1‖ = D :=
    Complex.exp_tail_denominator_norm_eq t ht_pos
  have hD_nonneg : 0 ≤ D :=
    le_of_lt (Real.binetSecondFormula_exp_denominator_pos ht_pos)
  calc
    ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ =
        ‖Complex.arctan ((t : ℂ) / w) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ := by
      rfl
    _ =
        ‖Complex.arctan ((t : ℂ) / w)‖ /
          ‖Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1‖ := by
      exact norm_div _ _
    _ = ‖Complex.arctan ((t : ℂ) / w)‖ / D := by
      exact congrArg
        (fun x : ℝ => ‖Complex.arctan ((t : ℂ) / w)‖ / x)
        hden_norm
    _ ≤ ((C / ‖w‖) * t) / D :=
      div_le_div_of_nonneg_right hscaled_arctan hD_nonneg
    _ = (C / ‖w‖) * (t / D) :=
      mul_div_assoc (C / ‖w‖) t D

/-- Full-sector integrated scaled majorant for the far part of the principal
Binet tail, after the bounded branch-wall window. -/
theorem Complex.binetSecondFormula_principalTailKernel_integral_far_scaled_decay :
    ∃ C : ℝ,
      0 ≤ C ∧
      ∀ w : ℂ,
        0 < w.re →
          1 ≤ ‖w‖ →
            2 * ∫ t : ℝ in Set.Ioi (2 * ‖w‖),
                ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ ≤
              (C / ‖w‖) *
                (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                  t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  match Complex.binetSecondFormulaPrincipalTailKernel_norm_le_far_scaled_majorant with
  | ⟨C, hC_nonneg, hpoint⟩ =>
      refine ⟨2 * C, mul_nonneg zero_le_two hC_nonneg, ?_⟩
      intro w hw_re_pos _hw_large
      let M : ℝ → ℝ := fun t : ℝ =>
        t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)
      let P : ℝ → ℝ := fun t : ℝ =>
        ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖
      have hhalf_nonneg : 0 ≤ ‖w‖ / 2 :=
        div_nonneg (norm_nonneg w) zero_le_two
      have hfar_subset_tail :
          Set.Ioi (2 * ‖w‖) ⊆ Set.Ioi (‖w‖ / 2) := by
        intro t ht
        have hhalf_le_norm : ‖w‖ / 2 ≤ ‖w‖ := by
          exact div_le_self (norm_nonneg w) one_le_two
        have hnorm_le_two_norm : ‖w‖ ≤ 2 * ‖w‖ :=
          le_mul_of_one_le_left (norm_nonneg w) one_le_two
        exact lt_of_le_of_lt (le_trans hhalf_le_norm hnorm_le_two_norm) ht
      have hM_integrable_tail :
          IntegrableOn M (Set.Ioi (‖w‖ / 2)) :=
        Real.binetSecondFormula_kernel_majorant_integrableOn.mono_set
          (fun t ht => lt_of_le_of_lt hhalf_nonneg ht)
      have hM_integrable_far :
          IntegrableOn M (Set.Ioi (2 * ‖w‖)) :=
        hM_integrable_tail.mono_set hfar_subset_tail
      have hscaled_integrable_far :
          IntegrableOn
            (fun t : ℝ => (C / ‖w‖) * M t)
            (Set.Ioi (2 * ‖w‖)) :=
        hM_integrable_far.const_mul (C / ‖w‖)
      have hP_integrable_far :
          IntegrableOn P (Set.Ioi (2 * ‖w‖)) :=
        (Complex.binetSecondFormulaPrincipalTailKernel_integrableOn_tail
          (w := w) hw_re_pos).norm.mono_set hfar_subset_tail
      have hpoint_ae :
          ∀ᵐ t ∂volume.restrict (Set.Ioi (2 * ‖w‖)),
            P t ≤ (C / ‖w‖) * M t :=
        (ae_restrict_mem measurableSet_Ioi).mono
          (fun t ht => hpoint w hw_re_pos t ht)
      have hintegral :
          ∫ t : ℝ in Set.Ioi (2 * ‖w‖), P t ≤
            ∫ t : ℝ in Set.Ioi (2 * ‖w‖), (C / ‖w‖) * M t :=
        setIntegral_mono_ae_restrict
          hP_integrable_far hscaled_integrable_far hpoint_ae
      have hscale_far :
          ∫ t : ℝ in Set.Ioi (2 * ‖w‖), (C / ‖w‖) * M t =
            (C / ‖w‖) *
              (∫ t : ℝ in Set.Ioi (2 * ‖w‖), M t) :=
        MeasureTheory.integral_mul_left (C / ‖w‖) M
      have hM_nonneg_tail :
          0 ≤ᵐ[volume.restrict (Set.Ioi (‖w‖ / 2))] M :=
        (ae_restrict_mem measurableSet_Ioi).mono
          (fun t ht =>
            Real.binetSecondFormula_kernel_majorant_nonneg_on_Ioi t
              (lt_of_le_of_lt hhalf_nonneg ht))
      have hmono_tail :
          ∫ t : ℝ in Set.Ioi (2 * ‖w‖), M t ≤
            ∫ t : ℝ in Set.Ioi (‖w‖ / 2), M t :=
        setIntegral_mono_set hM_integrable_tail hM_nonneg_tail
          (Filter.Eventually.of_forall hfar_subset_tail)
      have hcoeff_nonneg : 0 ≤ C / ‖w‖ :=
        div_nonneg hC_nonneg
          (le_of_lt (Complex.norm_pos_of_re_pos hw_re_pos))
      have hscaled_tail :
          ∫ t : ℝ in Set.Ioi (2 * ‖w‖), (C / ‖w‖) * M t ≤
            (C / ‖w‖) *
              (∫ t : ℝ in Set.Ioi (‖w‖ / 2), M t) := by
        calc
          ∫ t : ℝ in Set.Ioi (2 * ‖w‖), (C / ‖w‖) * M t =
              (C / ‖w‖) *
                (∫ t : ℝ in Set.Ioi (2 * ‖w‖), M t) :=
            hscale_far
          _ ≤ (C / ‖w‖) *
                (∫ t : ℝ in Set.Ioi (‖w‖ / 2), M t) :=
            mul_le_mul_of_nonneg_left hmono_tail hcoeff_nonneg
      have htwice :
          2 * ∫ t : ℝ in Set.Ioi (2 * ‖w‖), P t ≤
            2 * ((C / ‖w‖) *
              (∫ t : ℝ in Set.Ioi (‖w‖ / 2), M t)) :=
        mul_le_mul_of_nonneg_left
          (le_trans hintegral hscaled_tail) zero_le_two
      have hconst :
          2 * ((C / ‖w‖) *
              (∫ t : ℝ in Set.Ioi (‖w‖ / 2), M t)) =
            ((2 * C) / ‖w‖) *
              (∫ t : ℝ in Set.Ioi (‖w‖ / 2), M t) := by
        calc
          2 * ((C / ‖w‖) *
              (∫ t : ℝ in Set.Ioi (‖w‖ / 2), M t)) =
              (2 * (C / ‖w‖)) *
                (∫ t : ℝ in Set.Ioi (‖w‖ / 2), M t) :=
            (mul_assoc (2 : ℝ) (C / ‖w‖)
              (∫ t : ℝ in Set.Ioi (‖w‖ / 2), M t)).symm
          _ = ((2 * C) / ‖w‖) *
                (∫ t : ℝ in Set.Ioi (‖w‖ / 2), M t) := by
            exact congrArg
              (fun x : ℝ =>
                x * (∫ t : ℝ in Set.Ioi (‖w‖ / 2), M t))
              (mul_div_assoc (2 : ℝ) C ‖w‖).symm
      exact le_trans htwice (le_of_eq hconst)

/-- Split the principal-tail norm integral into the bounded branch-wall window
and the far tail. -/
theorem Complex.binetSecondFormula_principalTailKernel_integral_le_boundedWindow_add_far
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
        ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ ≤
      (∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
        ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖) +
      (∫ t : ℝ in Set.Ioi (2 * ‖w‖),
        ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖) := by
  let P : ℝ → ℝ := fun t : ℝ =>
    ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖
  have htail_integrable :
      IntegrableOn P (Set.Ioi (‖w‖ / 2)) :=
    (Complex.binetSecondFormulaPrincipalTailKernel_integrableOn_tail
      (w := w) hw_re_pos).norm
  have hcut_le_far : ‖w‖ / 2 ≤ 2 * ‖w‖ := by
    have hhalf_le_norm : ‖w‖ / 2 ≤ ‖w‖ :=
      div_le_self (norm_nonneg w) one_le_two
    have hnorm_le_two_norm : ‖w‖ ≤ 2 * ‖w‖ :=
      le_mul_of_one_le_left (norm_nonneg w) one_le_two
    exact le_trans hhalf_le_norm hnorm_le_two_norm
  have hwindow_subset_tail :
      Set.Ioc (‖w‖ / 2) (2 * ‖w‖) ⊆ Set.Ioi (‖w‖ / 2) := by
    intro t ht
    exact ht.1
  have hfar_subset_tail :
      Set.Ioi (2 * ‖w‖) ⊆ Set.Ioi (‖w‖ / 2) := by
    intro t ht
    exact lt_of_le_of_lt hcut_le_far ht
  have hwindow_integrable :
      IntegrableOn P (Set.Ioc (‖w‖ / 2) (2 * ‖w‖)) :=
    htail_integrable.mono_set hwindow_subset_tail
  have hfar_integrable :
      IntegrableOn P (Set.Ioi (2 * ‖w‖)) :=
    htail_integrable.mono_set hfar_subset_tail
  have hsplit :
      ∫ t : ℝ in Set.Ioi (‖w‖ / 2), P t =
        (∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖), P t) +
          (∫ t : ℝ in Set.Ioi (2 * ‖w‖), P t) := by
    have hunion :
        Set.Ioc (‖w‖ / 2) (2 * ‖w‖) ∪ Set.Ioi (2 * ‖w‖) =
          Set.Ioi (‖w‖ / 2) :=
      Set.Ioc_union_Ioi_eq_Ioi hcut_le_far
    have hdisjoint :
        Disjoint (Set.Ioc (‖w‖ / 2) (2 * ‖w‖))
          (Set.Ioi (2 * ‖w‖)) :=
      Ioc_disjoint_Ioi le_rfl
    calc
      ∫ t : ℝ in Set.Ioi (‖w‖ / 2), P t =
          ∫ t : ℝ in
            Set.Ioc (‖w‖ / 2) (2 * ‖w‖) ∪
              Set.Ioi (2 * ‖w‖), P t := by
        exact congrArg (fun s : Set ℝ => ∫ t : ℝ in s, P t) hunion.symm
      _ =
          (∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖), P t) +
            (∫ t : ℝ in Set.Ioi (2 * ‖w‖), P t) := by
        exact
          setIntegral_union hdisjoint measurableSet_Ioi
            hwindow_integrable hfar_integrable
  exact le_of_eq hsplit

/-- Combined bounded-window local-indentation estimate plus far-tail scaled
decay for the raw principal-tail norm integral. -/
theorem Complex.binetSecondFormula_principalTailKernel_integral_localIndentation_add_far_scaled_decay :
    ∃ Cfar : ℝ,
      0 ≤ Cfar ∧
      ∀ w : ℂ,
        0 < w.re →
          1 ≤ ‖w‖ →
            2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ ≤
            2 *
                (((max |Real.log (w.re / (3 * ‖w‖))|
                    (max |Real.log (1 : ℝ)|
                      |Real.log ((3 * ‖w‖) / w.re)|) + Real.pi) /
                  (Real.exp (Real.pi * ‖w‖) - 1)) *
                  (volume (Set.Ioc (‖w‖ / 2) (2 * ‖w‖))).toReal) +
                (Cfar / ‖w‖) *
                  (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                    t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  match Complex.binetSecondFormula_principalTailKernel_integral_far_scaled_decay with
  | ⟨Cfar, hCfar_nonneg, hfar⟩ =>
      refine ⟨Cfar, hCfar_nonneg, ?_⟩
      intro w hw_re_pos hw_large
      let P : ℝ → ℝ := fun t : ℝ =>
        ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖
      let L : ℝ :=
        ((max |Real.log (w.re / (3 * ‖w‖))|
            (max |Real.log (1 : ℝ)|
              |Real.log ((3 * ‖w‖) / w.re)|) + Real.pi) /
          (Real.exp (Real.pi * ‖w‖) - 1)) *
          (volume (Set.Ioc (‖w‖ / 2) (2 * ‖w‖))).toReal
      let J : ℝ :=
        ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
          t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)
      have hsplit :
          ∫ t : ℝ in Set.Ioi (‖w‖ / 2), P t ≤
            (∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖), P t) +
              (∫ t : ℝ in Set.Ioi (2 * ‖w‖), P t) :=
        Complex.binetSecondFormula_principalTailKernel_integral_le_boundedWindow_add_far
          (w := w) hw_re_pos
      have hlocal :
          ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖), P t ≤ L :=
        Complex.binetSecondFormula_principalTailKernel_integral_le_branchWall_localIndentation_boundedTailWindow_Ioc
          (w := w) hw_re_pos
      have hfar' :
          2 * ∫ t : ℝ in Set.Ioi (2 * ‖w‖), P t ≤
            (Cfar / ‖w‖) * J :=
        hfar w hw_re_pos hw_large
      have hcombined :
          ∫ t : ℝ in Set.Ioi (‖w‖ / 2), P t ≤
            L + ∫ t : ℝ in Set.Ioi (2 * ‖w‖), P t :=
        le_trans hsplit (add_le_add_right hlocal _)
      have htwice :
          2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2), P t ≤
            2 * (L + ∫ t : ℝ in Set.Ioi (2 * ‖w‖), P t) :=
        mul_le_mul_of_nonneg_left hcombined zero_le_two
      have hdistrib :
          2 * (L + ∫ t : ℝ in Set.Ioi (2 * ‖w‖), P t) =
            2 * L + 2 * ∫ t : ℝ in Set.Ioi (2 * ‖w‖), P t :=
        left_distrib (2 : ℝ) L
          (∫ t : ℝ in Set.Ioi (2 * ‖w‖), P t)
      calc
        2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2), P t ≤
            2 * (L + ∫ t : ℝ in Set.Ioi (2 * ‖w‖), P t) := htwice
        _ = 2 * L + 2 * ∫ t : ℝ in Set.Ioi (2 * ‖w‖), P t := hdistrib
        _ ≤ 2 * L + (Cfar / ‖w‖) * J :=
          add_le_add_left hfar' (2 * L)

/-- Integral branch comparison between the literal principal tail and a
contour-deformed tail kernel on the split tail. -/
def Complex.BinetSecondFormulaContourTailIntegralComparison
    (K : Complex.BinetSecondFormulaContourDeformedTailKernel)
    (R : ℝ) : Prop :=
  ∀ w : ℂ,
    0 < w.re →
    R ≤ ‖w‖ →
      ‖Complex.binetSecondFormulaTailRemainder w‖ ≤
        2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2), ‖K w t‖

/-- Kernel-integral form of the contour comparison.

This is the lowest branch-sensitive theorem in this file.  It compares the
literal principal-tail kernel only after integration over the split tail, which
is the level at which contour deformation is mathematically valid; cf. the
standard contour form of Binet's second formula in DLMF §5.11. -/
theorem Complex.binetSecondFormula_principalTailKernel_branchSingularity_absorbed_by_contourDeformation :
    Complex.BinetSecondFormulaPrincipalTailKernelIntegralComparison
      Complex.binetSecondFormulaContourTailMajorantKernel 2 := by
  exact
    Complex.binetSecondFormula_principalTailKernel_branchSingularity_absorbed_by_AbelPlanaContour

/-- Public kernel-integral form of the contour comparison.

This theorem is intentionally only a wrapper: the analytic content is the
branch-singularity absorption theorem above. -/
theorem Complex.binetSecondFormula_principalTailKernel_integral_le_contourTailMajorantKernel_integral :
    Complex.BinetSecondFormulaPrincipalTailKernelIntegralComparison
      Complex.binetSecondFormulaContourTailMajorantKernel 2 := by
  exact
    Complex.binetSecondFormula_principalTailKernel_branchSingularity_absorbed_by_contourDeformation

/-- Uniform full-sector pointwise majorant for a contour-deformed Binet tail
kernel. -/
def Complex.BinetSecondFormulaContourTailUniformMajorant
    (K : Complex.BinetSecondFormulaContourDeformedTailKernel)
    (R C : ℝ) : Prop :=
  ∀ w : ℂ,
    0 < w.re →
    R ≤ ‖w‖ →
      ∀ᵐ t ∂volume.restrict (Set.Ioi (‖w‖ / 2)),
        ‖K w t‖ ≤
          (C / ‖w‖) *
            (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))

/-- The branch-safe contour-deformation comparison for the Binet tail. -/
theorem Complex.binetSecondFormula_tailRemainder_norm_le_contourTailMajorantKernel_integral :
    Complex.BinetSecondFormulaContourTailIntegralComparison
      Complex.binetSecondFormulaContourTailMajorantKernel 2 :=
  fun w hw_re_pos hw_norm =>
  let htail_to_kernel :
      ‖Complex.binetSecondFormulaTailRemainder w‖ ≤
        2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
          ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ :=
    Complex.binetSecondFormulaTailRemainder_norm_le_principalTailKernel_norm_integral
      (w := w) hw_re_pos
  let hkernel_compare :
      ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
          ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ ≤
        ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
          ‖Complex.binetSecondFormulaContourTailMajorantKernel w t‖ :=
    Complex.binetSecondFormula_principalTailKernel_integral_le_contourTailMajorantKernel_integral
      w hw_re_pos hw_norm
  le_trans htail_to_kernel
    (mul_le_mul_of_nonneg_left hkernel_compare zero_le_two)

/-- A contour-kernel integral decay estimate turns the branch-sensitive
contour comparison into the decaying tail-remainder estimate.  The factor `2`
is the normalization of Binet's second-formula tail remainder. -/
theorem Complex.binetSecondFormula_tailRemainder_norm_le_of_contourTailKernel_integral_decay
    {K : Complex.BinetSecondFormulaContourDeformedTailKernel}
    {R C : ℝ}
    (hcontour : Complex.BinetSecondFormulaContourTailIntegralComparison K R)
    (hdecay :
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
          2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2), ‖K w t‖ ≤
            (C / ‖w‖) *
              (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))) :
    ∀ w : ℂ,
      0 < w.re →
      R ≤ ‖w‖ →
        ‖Complex.binetSecondFormulaTailRemainder w‖ ≤
          (C / ‖w‖) *
            (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
              t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) :=
  fun w hw_re_pos hRle =>
    le_trans
      (hcontour w hw_re_pos hRle)
      (hdecay w hw_re_pos hRle)

/-- Specialized form for the current contour-tail majorant kernel.

The analytic inequality is isolated as the second hypothesis: the contour
majorant integral itself has the pure decaying `C / ‖w‖` bound. -/
theorem Complex.binetSecondFormula_tailRemainder_norm_le_of_contourTailMajorantKernel_integral_decay
    {C : ℝ}
    (hdecay :
      ∀ w : ℂ,
        0 < w.re →
        2 ≤ ‖w‖ →
          2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
              ‖Complex.binetSecondFormulaContourTailMajorantKernel w t‖ ≤
            (C / ‖w‖) *
              (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))) :
    ∀ w : ℂ,
      0 < w.re →
      2 ≤ ‖w‖ →
        ‖Complex.binetSecondFormulaTailRemainder w‖ ≤
          (C / ‖w‖) *
            (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
              t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) :=
  Complex.binetSecondFormula_tailRemainder_norm_le_of_contourTailKernel_integral_decay
    Complex.binetSecondFormula_tailRemainder_norm_le_contourTailMajorantKernel_integral
    hdecay

end

end LFunctions
end Boundary
