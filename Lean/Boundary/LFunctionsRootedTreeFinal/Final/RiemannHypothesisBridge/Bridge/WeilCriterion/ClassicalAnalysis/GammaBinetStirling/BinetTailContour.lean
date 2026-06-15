import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlana
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.SectorialFromBinet

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

/-- The principal tail kernel is integrable on the split tail in the open
right half-plane. -/
theorem Complex.binetSecondFormulaPrincipalTailKernel_integrableOn_tail
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    IntegrableOn
      (fun t : ℝ => Complex.binetSecondFormulaPrincipalTailKernel w t)
      (Set.Ioi (‖w‖ / 2)) := by
  exact
    Eq.ndrec
      Complex.binetSecondFormula_arctanKernel_integrableOn_tail_interval
      (by
        unfold Complex.binetSecondFormulaPrincipalTailKernel
        rfl)

/-- The norm of the Binet tail remainder is bounded by twice the integral of
the norm of the principal tail kernel. -/
theorem Complex.binetSecondFormulaTailRemainder_norm_le_principalTailKernel_norm_integral
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
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
        norm_num [Complex.normSq]
      calc
        ‖2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2), K t‖ =
            ‖(2 : ℂ)‖ * ‖∫ t : ℝ in Set.Ioi (‖w‖ / 2), K t‖ := by
          exact norm_mul _ _
        _ = 2 * ‖∫ t : ℝ in Set.Ioi (‖w‖ / 2), K t‖ := by
          exact congrArg (fun x : ℝ => x * ‖∫ t : ℝ in Set.Ioi (‖w‖ / 2), K t‖) htwo
    _ ≤ 2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2), ‖K t‖ :=
      mul_le_mul_of_nonneg_left hnorm_integral zero_le_two

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
      Complex.binetSecondFormulaContourTailMajorantKernel 2 := by
  intro w hw_re_pos hw_norm
  have htail_to_kernel :
      ‖Complex.binetSecondFormulaTailRemainder w‖ ≤
        2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
          ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ :=
    Complex.binetSecondFormulaTailRemainder_norm_le_principalTailKernel_norm_integral
      (w := w) hw_re_pos
  have hkernel_compare :
      ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
          ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ ≤
        ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
          ‖Complex.binetSecondFormulaContourTailMajorantKernel w t‖ :=
    Complex.binetSecondFormula_principalTailKernel_integral_le_contourTailMajorantKernel_integral
      w hw_re_pos hw_norm
  exact
    le_trans htail_to_kernel
      (mul_le_mul_of_nonneg_left hkernel_compare zero_le_two)

end

end LFunctions
end Boundary
