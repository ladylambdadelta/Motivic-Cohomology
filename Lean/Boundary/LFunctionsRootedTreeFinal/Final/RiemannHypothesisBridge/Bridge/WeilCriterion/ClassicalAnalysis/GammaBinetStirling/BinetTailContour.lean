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
open Filter
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

/-- The lower Abel-Plana vertical logarithmic-jump tail is exactly the Binet
tail remainder after the split at `‖w‖ / 2`.

This is the tail-interval transport of the pointwise branch normalization
`binetAbelPlana_logJump_integrand_eq_two_arctanKernel`.  It is the bridge from
finite-height Abel-Plana vertical-boundary language to the infinite Binet tail
object consumed by the wall-cancellation owner. -/
theorem Complex.finiteAbelPlana_lowerVerticalTailIntegral_eq_binetTailRemainder
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
        Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t =
      Complex.binetSecondFormulaTailRemainder w := by
  let L : ℝ → ℂ := fun t : ℝ =>
    Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t
  let K : ℝ → ℂ := fun t : ℝ =>
    Complex.binetSecondFormulaPrincipalTailKernel w t
  have hcut_nonneg : 0 ≤ ‖w‖ / 2 :=
    div_nonneg (norm_nonneg w) zero_le_two
  have hpoint :
      ∀ᵐ t ∂volume.restrict (Set.Ioi (‖w‖ / 2)),
        L t = 2 * K t :=
    (ae_restrict_mem measurableSet_Ioi).mono
      (fun t ht =>
        have ht_pos : 0 < t :=
          lt_of_le_of_lt hcut_nonneg ht
        calc
          L t =
              (-Complex.I) *
                ((Complex.log (w + (t : ℂ) * Complex.I) -
                    Complex.log (w - (t : ℂ) * Complex.I)) /
                  (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)) := by
            exact Complex.finiteAbelPlana_log_lowerVerticalIntegrand_eq_binet w t
          _ = 2 *
              (Complex.arctan ((t : ℂ) / w) /
                (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)) := by
            exact
              Complex.binetAbelPlana_logJump_integrand_eq_two_arctanKernel
                (w := w) (t := t) hw_re_pos ht_pos
          _ = 2 * K t := by
            rfl)
  have hintegral :
      ∫ t : ℝ in Set.Ioi (‖w‖ / 2), L t =
        ∫ t : ℝ in Set.Ioi (‖w‖ / 2), 2 * K t :=
    integral_congr_ae hpoint
  have hscale :
      ∫ t : ℝ in Set.Ioi (‖w‖ / 2), 2 * K t =
        2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2), K t :=
    integral_mul_left
      (μ := volume.restrict (Set.Ioi (‖w‖ / 2)))
      (2 : ℂ)
      K
  have htail :
      Complex.binetSecondFormulaTailRemainder w =
        2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2), K t :=
    Complex.binetSecondFormulaTailRemainder_eq_principalTailKernel_integral w
  calc
    ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
        Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t =
        ∫ t : ℝ in Set.Ioi (‖w‖ / 2), L t := by
      rfl
    _ = ∫ t : ℝ in Set.Ioi (‖w‖ / 2), 2 * K t :=
      hintegral
    _ = 2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2), K t :=
      hscale
    _ = Complex.binetSecondFormulaTailRemainder w :=
      htail.symm

/-- The lower Abel-Plana vertical full integral splits at the Binet tail
cutoff into the bounded initial window and the Binet tail remainder.

This is the exact split needed by the branch-wall cancellation proof: the
finite-height vertical side converges to a full lower vertical integral, and
that full integral contains the Binet tail remainder as its open tail beyond
`‖w‖ / 2`. -/
theorem Complex.finiteAbelPlana_lowerVerticalFullIntegral_eq_initialWindow_add_binetTailRemainder
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w =
      (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
        Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t) +
        Complex.binetSecondFormulaTailRemainder w := by
  let L : ℝ → ℂ := fun t : ℝ =>
    Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t
  let a : ℝ := ‖w‖ / 2
  have ha_nonneg : 0 ≤ a :=
    div_nonneg (norm_nonneg w) zero_le_two
  have hL :
      IntegrableOn L (Set.Ioi (0 : ℝ)) :=
    Complex.finiteAbelPlana_log_lowerVerticalIntegrand_integrableOn_Ioi
      hw_re_pos
  have hwindow :
      IntegrableOn L (Set.Ioc (0 : ℝ) a) :=
    hL.mono_set
      (fun t ht => ht.1)
  have htail_integrable :
      IntegrableOn L (Set.Ioi a) :=
    hL.mono_set
      (fun t ht => lt_of_le_of_lt ha_nonneg ht)
  have hdisjoint :
      Disjoint (Set.Ioc (0 : ℝ) a) (Set.Ioi a) :=
    Set.disjoint_left.mpr
      (fun t ht_window ht_tail =>
        not_lt_of_ge ht_window.2 ht_tail)
  have hunion :
      Set.Ioc (0 : ℝ) a ∪ Set.Ioi a =
        Set.Ioi (0 : ℝ) := by
    ext t
    constructor
    · intro ht
      match ht with
      | Or.inl ht_window => exact ht_window.1
      | Or.inr ht_tail => exact lt_of_le_of_lt ha_nonneg ht_tail
    · intro ht
      by_cases ht_cut : t ≤ a
      · exact Or.inl ⟨ht, ht_cut⟩
      · exact Or.inr (lt_of_not_ge ht_cut)
  have hsplit :
      ∫ t : ℝ in Set.Ioc (0 : ℝ) a ∪ Set.Ioi a, L t =
        (∫ t : ℝ in Set.Ioc (0 : ℝ) a, L t) +
          ∫ t : ℝ in Set.Ioi a, L t :=
    setIntegral_union hdisjoint measurableSet_Ioi hwindow htail_integrable
  have htail :
      ∫ t : ℝ in Set.Ioi a, L t =
        Complex.binetSecondFormulaTailRemainder w := by
    exact
      Complex.finiteAbelPlana_lowerVerticalTailIntegral_eq_binetTailRemainder
        hw_re_pos
  calc
    Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w =
        ∫ t : ℝ in Set.Ioi (0 : ℝ), L t := by
      exact Complex.finiteAbelPlana_log_lowerVerticalFullIntegral_unfold w
    _ = ∫ t : ℝ in Set.Ioc (0 : ℝ) a ∪ Set.Ioi a, L t := by
      exact congrArg (fun s : Set ℝ => ∫ t : ℝ in s, L t) hunion.symm
    _ = (∫ t : ℝ in Set.Ioc (0 : ℝ) a, L t) +
          ∫ t : ℝ in Set.Ioi a, L t :=
      hsplit
    _ = (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t) +
          Complex.binetSecondFormulaTailRemainder w := by
      exact congrArg
        (fun z : ℂ =>
          (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
            Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t) + z)
        htail

/-- Difference form of the lower-vertical split at the Binet tail cutoff.

This is the algebraic form consumed by cancellation estimates: once the
bounded initial window has been paired with the finite-height contour
contribution, the remaining difference is exactly the Binet tail remainder. -/
theorem Complex.binetSecondFormulaTailRemainder_eq_lowerVerticalFullIntegral_sub_initialWindow
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    Complex.binetSecondFormulaTailRemainder w =
      Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t) := by
  let I : ℂ :=
    ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
      Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t
  let T : ℂ := Complex.binetSecondFormulaTailRemainder w
  let F : ℂ := Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w
  have hsplit : F = I + T :=
    Complex.finiteAbelPlana_lowerVerticalFullIntegral_eq_initialWindow_add_binetTailRemainder
      hw_re_pos
  have htail_sub : T = (I + T) - I :=
    (add_sub_cancel_left I T).symm
  have hfull_sub : (I + T) - I = F - I :=
    congrArg (fun z : ℂ => z - I) hsplit.symm
  calc
    Complex.binetSecondFormulaTailRemainder w = T := by
      rfl
    _ = (I + T) - I :=
      htail_sub
    _ = F - I :=
      hfull_sub
    _ =
        Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w -
          (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
            Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t) := by
      rfl

/-- Norm form of the lower-vertical difference representation of the Binet
tail remainder. -/
theorem Complex.binetSecondFormulaTailRemainder_norm_eq_lowerVerticalFullIntegral_sub_initialWindow_norm
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ‖Complex.binetSecondFormulaTailRemainder w‖ =
      ‖Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ := by
  exact congrArg norm
    (Complex.binetSecondFormulaTailRemainder_eq_lowerVerticalFullIntegral_sub_initialWindow
      hw_re_pos)

/-- Finite-height lower vertical tails converge to the Binet tail remainder
after subtracting the fixed initial window at the Binet cutoff.

This is the finite-height version of the lower-vertical split: the moving upper
height tends to the full lower vertical integral, while the initial window
`(0, ‖w‖ / 2]` is kept fixed. -/
theorem Complex.finiteAbelPlana_lowerVerticalUpTo_sub_initialWindow_tendsto_binetTailRemainder
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    Tendsto
      (fun T : ℝ =>
        Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
          (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
            Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t))
      atTop
      (𝓝 (Complex.binetSecondFormulaTailRemainder w)) := by
  let I : ℂ :=
    ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
      Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t
  have hfull :
      Tendsto
        (fun T : ℝ =>
          Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)
        atTop
        (𝓝 (Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w)) :=
    Complex.finiteAbelPlana_log_lowerVerticalIntegralUpTo_tendsto_unsplitFull_owner
      hw_re_pos
  have hsub :
      Tendsto
        (fun T : ℝ =>
          Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T - I)
        atTop
        (𝓝 (Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w - I)) :=
    hfull.sub tendsto_const_nhds
  have htail :
      Complex.binetSecondFormulaTailRemainder w =
        Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w - I :=
    Complex.binetSecondFormulaTailRemainder_eq_lowerVerticalFullIntegral_sub_initialWindow
      hw_re_pos
  exact htail.symm ▸ hsub

/-- A complex limit of an eventually norm-bounded finite-height family is
bounded by the same real constant. -/
theorem Complex.norm_le_of_eventually_norm_le_of_tendsto
    {ι : Type*}
    {l : Filter ι}
    [Filter.NeBot l]
    {u : ι → ℂ}
    {z : ℂ}
    {C : ℝ}
    (hu : Tendsto u l (𝓝 z))
    (hbound : ∀ᶠ i in l, ‖u i‖ ≤ C) :
    ‖z‖ ≤ C := by
  have hclosed : IsClosed {v : ℂ | ‖v‖ ≤ C} :=
    isClosed_le continuous_norm continuous_const
  exact hclosed.mem_of_tendsto hu hbound

/-- Finite-height lower-tail estimates pass to the Binet tail remainder.

This is the closure step needed after paired contour cancellation supplies an
eventual finite-height estimate. -/
theorem Complex.binetSecondFormulaTailRemainder_norm_le_of_eventually_lowerVerticalUpTo_sub_initialWindow_norm_le
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    {B : ℝ}
    (hbound :
      ∀ᶠ T : ℝ in atTop,
        ‖Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
          (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
            Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤ B) :
    ‖Complex.binetSecondFormulaTailRemainder w‖ ≤ B := by
  exact
    Complex.norm_le_of_eventually_norm_le_of_tendsto
      (Complex.finiteAbelPlana_lowerVerticalUpTo_sub_initialWindow_tendsto_binetTailRemainder
        hw_re_pos)
      hbound

/-- Solving the finite-height Abel-Plana boundary equation for the lower
vertical tail at the Binet cutoff.

This is a pure algebraic identity.  The finite-height contour error appears
with the sign forced by
`finiteHeightContourError = boundaryNamedPiecesUpTo - residueContribution`;
the remaining terms are the real segment, endpoint half contribution, upper
vertical side, residue contribution, and the fixed initial lower window. -/
theorem Complex.finiteAbelPlana_lowerVerticalUpTo_sub_initialWindow_eq_boundarySolved
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t) =
      ((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
          Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
        Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
        Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w -
        Complex.finiteAbelPlanaLogFiniteHeightContourError N w T) -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t) := by
  let R : ℂ :=
    ∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
      Complex.finiteAbelPlanaLogSummand w (x : ℂ)
  let H : ℂ := Complex.finiteAbelPlanaLogSummandHalfEndpoints N w
  let L : ℂ := Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T
  let U : ℂ := Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T
  let P : ℂ := Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w
  let E : ℂ := Complex.finiteAbelPlanaLogFiniteHeightContourError N w T
  let I : ℂ :=
    ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
      Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t
  have hboundary :
      Complex.finiteAbelPlanaLogBoundaryNamedPiecesUpTo N w T =
        R + H - L - U := by
    exact Complex.finiteAbelPlana_log_boundaryNamedPiecesUpTo_unfold N w T
  have herror :
      E =
        Complex.finiteAbelPlanaLogBoundaryNamedPiecesUpTo N w T - P :=
    Complex.finiteAbelPlana_log_finiteHeightContourError_unfold' N w T
  have herror_expanded :
      E = R + H - L - U - P := by
    calc
      E = Complex.finiteAbelPlanaLogBoundaryNamedPiecesUpTo N w T - P :=
        herror
      _ = (R + H - L - U) - P := by
        exact congrArg (fun z : ℂ => z - P) hboundary
      _ = R + H - L - U - P := by
        rfl
  have hsolve :
      L = R + H - U - P - E := by
    let A : ℂ := R + H - U - P
    have hreorder :
        R + H - L - U - P = A - L := by
      calc
        R + H - L - U - P =
            (R + H) - L - U - P := by
          rfl
        _ = (R + H) - U - L - P := by
          exact congrArg (fun z : ℂ => z - P)
            (sub_right_comm (R + H) L U)
        _ = (R + H) - U - P - L := by
          exact sub_right_comm ((R + H) - U) L P
        _ = A - L := by
          rfl
    have hcancel :
        A - (R + H - L - U - P) = L := by
      calc
        A - (R + H - L - U - P) = A - (A - L) := by
          exact congrArg (fun z : ℂ => A - z) hreorder
        _ = L := by
          exact sub_sub_self A L
    calc
      L = A - (R + H - L - U - P) :=
        hcancel.symm
      _ = A - E := by
        exact congrArg (fun z : ℂ => A - z) herror_expanded.symm
      _ = R + H - U - P - E := by
        rfl
  calc
    Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t) =
        L - I := by
      rfl
    _ = (R + H - U - P - E) - I := by
      exact congrArg (fun z : ℂ => z - I) hsolve
    _ =
      ((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
          Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
        Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
        Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w -
        Complex.finiteAbelPlanaLogFiniteHeightContourError N w T) -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t) := by
      rfl

/-- Move a middle additive term to the right of one subtraction. -/
theorem Complex.add_middle_sub_right
    (a h b : ℂ) :
    a + h - b = a - b + h := by
  calc
    a + h - b = (a + h) + -b := by
      exact sub_eq_add_neg (a + h) b
    _ = a + (h + -b) := by
      exact add_assoc a h (-b)
    _ = a + (-b + h) := by
      exact congrArg (fun z : ℂ => a + z) (add_comm h (-b))
    _ = (a + -b) + h := by
      exact (add_assoc a (-b) h).symm
    _ = a - b + h := by
      exact congrArg (fun z : ℂ => z + h) (sub_eq_add_neg a b).symm

/-- Move the finite endpoint term across the two static subtractions. -/
theorem Complex.endpoint_middle_static_subtractions
    (R H U P E : ℂ) :
    R + H - U - P - E =
      (R - U - P) + H - E := by
  calc
    R + H - U - P - E =
        (R - U + H) - P - E := by
      exact congrArg (fun z : ℂ => z - P - E)
        (Complex.add_middle_sub_right R H U)
    _ = ((R - U) - P + H) - E := by
      exact congrArg (fun z : ℂ => z - E)
        (Complex.add_middle_sub_right (R - U) H P)
    _ = (R - U - P) + H - E := by
      rfl

/-- Absorb the endpoint term into the restored contour error. -/
theorem Complex.static_endpoint_absorb_restored_error
    (A H E : ℂ) :
    A + H - E = A - (E - H) := by
  calc
    A + H - E = (A + H) + -E := by
      exact sub_eq_add_neg (A + H) E
    _ = A + (H + -E) := by
      exact add_assoc A H (-E)
    _ = A + (H - E) := by
      exact congrArg (fun z : ℂ => A + z) (sub_eq_add_neg H E).symm
    _ = A + (-(E - H)) := by
      exact congrArg (fun z : ℂ => A + z) (neg_sub E H).symm
    _ = A - (E - H) := by
      exact (sub_eq_add_neg A (E - H)).symm

/-- Restored-error form of the solved finite-height Abel-Plana boundary
equation.

After replacing the old contour error by
`finiteHeightEndpointRestoredContourError = finiteHeightContourError -
endpointIndentation`, the explicit half-endpoint term in the static part
cancels. -/
theorem Complex.finiteAbelPlana_lowerVerticalUpTo_sub_initialWindow_eq_boundarySolved_endpointRestored
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t) =
      ((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
          Complex.finiteAbelPlanaLogSummand w (x : ℂ)) -
        Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w -
        Complex.finiteAbelPlanaLogFiniteHeightEndpointRestoredContourError N w T) -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t) := by
  let R : ℂ :=
    ∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
      Complex.finiteAbelPlanaLogSummand w (x : ℂ)
  let H : ℂ := Complex.finiteAbelPlanaLogSummandHalfEndpoints N w
  let U : ℂ := Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T
  let P : ℂ := Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w
  let E : ℂ := Complex.finiteAbelPlanaLogFiniteHeightContourError N w T
  let Er : ℂ :=
    Complex.finiteAbelPlanaLogFiniteHeightEndpointRestoredContourError N w T
  let I : ℂ :=
    ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
      Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t
  have hbase :
      Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T - I =
        (R + H - U - P - E) - I :=
    Complex.finiteAbelPlana_lowerVerticalUpTo_sub_initialWindow_eq_boundarySolved
      N w T
  have hendpoint :
      Complex.finiteAbelPlanaLogEndpointPVIndentationContribution N w = H :=
    Complex.finiteAbelPlana_log_endpointPVIndentationContribution_unfold N w
  have hrestored :
      Er = E - H := by
    calc
      Er =
          E - Complex.finiteAbelPlanaLogEndpointPVIndentationContribution N w := by
        rfl
      _ = E - H := by
        exact congrArg (fun z : ℂ => E - z) hendpoint
  have hstatic :
      R + H - U - P - E =
        R - U - P - Er := by
    calc
      R + H - U - P - E =
          (R - U - P) + H - E :=
        Complex.endpoint_middle_static_subtractions R H U P E
      _ = (R - U - P) - (E - H) :=
        Complex.static_endpoint_absorb_restored_error (R - U - P) H E
      _ = R - U - P - Er := by
        exact congrArg (fun z : ℂ => R - U - P - z) hrestored.symm
  calc
    Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T - I =
        (R + H - U - P - E) - I :=
      hbase
    _ = (R - U - P - Er) - I := by
      exact congrArg (fun z : ℂ => z - I) hstatic
    _ =
      ((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
          Complex.finiteAbelPlanaLogSummand w (x : ℂ)) -
        Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w -
        Complex.finiteAbelPlanaLogFiniteHeightEndpointRestoredContourError N w T) -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t) := by
      rfl

/-- Norm estimate obtained from the solved finite-height boundary equation:
the lower vertical tail is bounded by the non-error solved boundary part plus
the finite-height contour-error norm. -/
theorem Complex.finiteAbelPlana_lowerVerticalUpTo_sub_initialWindow_norm_le_boundarySolvedStatic_add_contourError
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    ‖Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
      ‖((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
          Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
        Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
        Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ +
        ‖Complex.finiteAbelPlanaLogFiniteHeightContourError N w T‖ := by
  let A : ℂ :=
    (∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
      Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
      Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
      Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
      Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w
  let E : ℂ := Complex.finiteAbelPlanaLogFiniteHeightContourError N w T
  let I : ℂ :=
    ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
      Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t
  have hsolved :
      Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T - I =
        (A - E) - I :=
    Complex.finiteAbelPlana_lowerVerticalUpTo_sub_initialWindow_eq_boundarySolved
      N w T
  have hreorder :
      (A - E) - I = (A - I) - E := by
    exact sub_right_comm A E I
  have hnorm :
      ‖(A - I) - E‖ ≤ ‖A - I‖ + ‖E‖ :=
    norm_sub_le (A - I) E
  have hsource :
      ‖Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T - I‖ =
        ‖(A - I) - E‖ := by
    exact congrArg norm (Eq.trans hsolved hreorder)
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ ‖A - I‖ + ‖E‖)
      hsource.symm
      hnorm

/-- Restored-error norm estimate obtained from the solved finite-height
boundary equation. -/
theorem Complex.finiteAbelPlana_lowerVerticalUpTo_sub_initialWindow_norm_le_boundarySolvedStatic_add_endpointRestoredContourError
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    ‖Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
      ‖((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
          Complex.finiteAbelPlanaLogSummand w (x : ℂ)) -
        Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ +
        ‖Complex.finiteAbelPlanaLogFiniteHeightEndpointRestoredContourError N w T‖ := by
  let A : ℂ :=
    (∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
      Complex.finiteAbelPlanaLogSummand w (x : ℂ)) -
      Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
      Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w
  let E : ℂ :=
    Complex.finiteAbelPlanaLogFiniteHeightEndpointRestoredContourError N w T
  let I : ℂ :=
    ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
      Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t
  have hsolved :
      Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T - I =
        (A - E) - I :=
    Complex.finiteAbelPlana_lowerVerticalUpTo_sub_initialWindow_eq_boundarySolved_endpointRestored
      N w T
  have hreorder :
      (A - E) - I = (A - I) - E := by
    exact sub_right_comm A E I
  have hnorm :
      ‖(A - I) - E‖ ≤ ‖A - I‖ + ‖E‖ :=
    norm_sub_le (A - I) E
  have hsource :
      ‖Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T - I‖ =
        ‖(A - I) - E‖ := by
    exact congrArg norm (Eq.trans hsolved hreorder)
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ ‖A - I‖ + ‖E‖)
      hsource.symm
      hnorm

/-- Restored-error solved finite-height equation with the endpoint term
returned on both sides of the paired difference.

The endpoint-restored static expression and endpoint-restored contour error
must not be estimated separately at this layer: the half-endpoint term moves
between them.  This equality records the canonical paired object whose norm is
the finite-height lower-vertical difference. -/
theorem Complex.finiteAbelPlana_lowerVerticalUpTo_sub_initialWindow_eq_endpointReturnedRestoredPair
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t) =
      ((((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
          Complex.finiteAbelPlanaLogSummand w (x : ℂ)) -
        Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)) +
        Complex.finiteAbelPlanaLogSummandHalfEndpoints N w) -
        (Complex.finiteAbelPlanaLogFiniteHeightEndpointRestoredContourError N w T +
          Complex.finiteAbelPlanaLogSummandHalfEndpoints N w) := by
  let A : ℂ :=
    (∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
      Complex.finiteAbelPlanaLogSummand w (x : ℂ)) -
      Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
      Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w
  let E : ℂ :=
    Complex.finiteAbelPlanaLogFiniteHeightEndpointRestoredContourError N w T
  let H : ℂ := Complex.finiteAbelPlanaLogSummandHalfEndpoints N w
  let I : ℂ :=
    ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
      Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t
  have hsolved :
      Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T - I =
        (A - E) - I :=
    Complex.finiteAbelPlana_lowerVerticalUpTo_sub_initialWindow_eq_boundarySolved_endpointRestored
      N w T
  have hreorder :
      (A - E) - I = (A - I) - E :=
    sub_right_comm A E I
  have hpair :
      ((A - I) + H) - (E + H) = (A - I) - E := by
    let S : ℂ := A - I
    calc
      ((A - I) + H) - (E + H) = (S + H) - (E + H) := by
        rfl
      _ = (S + H) - E - H := by
        exact sub_add_eq_sub_sub (S + H) E H
      _ = S + H - H - E := by
        exact sub_right_comm (S + H) E H
      _ = S - E := by
        exact congrArg (fun z : ℂ => z - E) (add_sub_cancel_right S H)
      _ = (A - I) - E := by
        rfl
  calc
    Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T - I =
        (A - E) - I :=
      hsolved
    _ = (A - I) - E :=
      hreorder
    _ = ((A - I) + H) - (E + H) :=
      hpair.symm
    _ =
      ((((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
          Complex.finiteAbelPlanaLogSummand w (x : ℂ)) -
        Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)) +
        Complex.finiteAbelPlanaLogSummandHalfEndpoints N w) -
        (Complex.finiteAbelPlanaLogFiniteHeightEndpointRestoredContourError N w T +
          Complex.finiteAbelPlanaLogSummandHalfEndpoints N w) := by
      rfl

/-- Norm form of the endpoint-returned restored-pair finite-height equation. -/
theorem Complex.finiteAbelPlana_lowerVerticalUpTo_sub_initialWindow_norm_eq_endpointReturnedRestoredPair_norm
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    ‖Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ =
      ‖(((((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
          Complex.finiteAbelPlanaLogSummand w (x : ℂ)) -
        Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)) +
        Complex.finiteAbelPlanaLogSummandHalfEndpoints N w) -
        (Complex.finiteAbelPlanaLogFiniteHeightEndpointRestoredContourError N w T +
          Complex.finiteAbelPlanaLogSummandHalfEndpoints N w))‖ := by
  exact congrArg norm
    (Complex.finiteAbelPlana_lowerVerticalUpTo_sub_initialWindow_eq_endpointReturnedRestoredPair
      N w T)

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
      exact Exists.intro (2 * B)
        (And.intro (mul_nonneg Real.zero_le_two_real hB_nonneg) (by
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
        ))

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
      exact Exists.intro (2 * C)
        (And.intro (mul_nonneg Real.zero_le_two_real hC_nonneg) (by
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
        ))

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
      exact Exists.intro (C + 1)
        (And.intro
          (lt_of_lt_of_le zero_lt_one
          (by
            calc
              (1 : ℝ) = 0 + 1 := (zero_add 1).symm
              _ ≤ C + 1 := add_le_add_right hC_nonneg 1))
          (by
        intro w hw_re_pos hw_sep hw_large
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
          ))

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
  exact Exists.intro C (And.intro hC_nonneg (by
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
    match
        Complex.binetSecondFormula_arctan_tail_far_ratio_bounds
          (w := w) (t := t) ht_far with
    | ⟨hnum_le, hden_le⟩ =>
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
  ))

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
      exact Exists.intro (2 * C)
        (And.intro (mul_nonneg zero_le_two hC_nonneg) (by
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
        have hP_integrable_tail :
            IntegrableOn P (Set.Ioi (‖w‖ / 2)) :=
          (Complex.binetSecondFormulaPrincipalTailKernel_integrableOn_tail
            (w := w) hw_re_pos).norm
        hP_integrable_tail.mono_set hfar_subset_tail
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
        ))

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
      Set.disjoint_left.mpr
        (fun t ht_window ht_tail =>
          not_lt_of_ge ht_window.2 ht_tail)
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
      exact Exists.intro Cfar (And.intro hCfar_nonneg (by
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
      ))

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

/-- A uniformly majorized contour-tail kernel has the corresponding integrated
`C / ‖w‖` decay.

This is the real-variable integration step in the contour-cancellation proof:
the analytic contour theorem supplies the comparison to `K`, while the
pointwise full-sector majorant supplies the decaying scalar tail. -/
theorem Complex.binetSecondFormula_contourTailKernel_integral_decay_of_uniform_majorant
    {K : Complex.BinetSecondFormulaContourDeformedTailKernel}
    {R C : ℝ}
    (hK_integrable :
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
          IntegrableOn
            (fun t : ℝ => K w t)
            (Set.Ioi (‖w‖ / 2)))
    (hmajorant : Complex.BinetSecondFormulaContourTailUniformMajorant K R C) :
    ∀ w : ℂ,
      0 < w.re →
      R ≤ ‖w‖ →
        2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2), ‖K w t‖ ≤
          ((2 * C) / ‖w‖) *
            (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
              t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  intro w hw_re_pos hRle
  let M : ℝ → ℝ := fun t : ℝ =>
    t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)
  let G : ℝ → ℝ := fun t : ℝ => ‖K w t‖
  let J : ℝ := ∫ t : ℝ in Set.Ioi (‖w‖ / 2), M t
  have hhalf_nonneg : 0 ≤ ‖w‖ / 2 :=
    div_nonneg (norm_nonneg w) zero_le_two
  have hM_integrable :
      IntegrableOn M (Set.Ioi (‖w‖ / 2)) :=
    Real.binetSecondFormula_kernel_majorant_integrableOn.mono_set
      (fun t ht => lt_of_le_of_lt hhalf_nonneg ht)
  have hscaled_integrable :
      IntegrableOn
        (fun t : ℝ => (C / ‖w‖) * M t)
        (Set.Ioi (‖w‖ / 2)) :=
    hM_integrable.const_mul (C / ‖w‖)
  have hG_integrable :
      IntegrableOn G (Set.Ioi (‖w‖ / 2)) :=
    (hK_integrable w hw_re_pos hRle).norm
  have hpoint :
      ∀ᵐ t ∂volume.restrict (Set.Ioi (‖w‖ / 2)),
        G t ≤ (C / ‖w‖) * M t :=
    hmajorant w hw_re_pos hRle
  have hintegral :
      ∫ t : ℝ in Set.Ioi (‖w‖ / 2), G t ≤
        ∫ t : ℝ in Set.Ioi (‖w‖ / 2), (C / ‖w‖) * M t :=
    setIntegral_mono_ae_restrict
      hG_integrable
      hscaled_integrable
      hpoint
  have hscale :
      ∫ t : ℝ in Set.Ioi (‖w‖ / 2), (C / ‖w‖) * M t =
        (C / ‖w‖) * J := by
    exact MeasureTheory.integral_mul_left (C / ‖w‖) M
  have htwice :
      2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2), G t ≤
        2 * ((C / ‖w‖) * J) :=
    mul_le_mul_of_nonneg_left
      (le_trans hintegral (le_of_eq hscale))
      zero_le_two
  have hconstant :
      2 * ((C / ‖w‖) * J) =
        ((2 * C) / ‖w‖) * J := by
    calc
      2 * ((C / ‖w‖) * J) =
          (2 * (C / ‖w‖)) * J := by
        exact (mul_assoc (2 : ℝ) (C / ‖w‖) J).symm
      _ = ((2 * C) / ‖w‖) * J := by
        exact congrArg (fun x : ℝ => x * J)
          (mul_div_assoc (2 : ℝ) C ‖w‖).symm
  exact le_trans htwice (le_of_eq hconstant)

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
