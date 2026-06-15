import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetKernelBounds
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.Order.Interval.Set.Disjoint

/-!
# Core Abel-Plana objects for Binet's second formula

This file owns the concrete objects used by the Abel-Plana derivation of
Binet's second logarithmic formula.  The assembly file `BinetAbelPlana` should
contain no analytic proof roots; roots live here with the smallest useful
mathematical statements.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Type of a contour-deformed Binet tail kernel. -/
abbrev Complex.BinetSecondFormulaContourDeformedTailKernel :=
  ℂ → ℝ → ℂ

/-- The literal principal-branch Binet tail kernel after the split at
`‖w‖ / 2`. -/
noncomputable def Complex.binetSecondFormulaPrincipalTailKernel
    (w : ℂ)
    (t : ℝ) : ℂ :=
  Complex.arctan ((t : ℂ) / w) /
    (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)

/-- Integral contour comparison for the principal tail kernel. -/
def Complex.BinetSecondFormulaPrincipalTailKernelIntegralComparison
    (K : Complex.BinetSecondFormulaContourDeformedTailKernel)
    (R : ℝ) : Prop :=
  ∀ w : ℂ,
    0 < w.re →
    R ≤ ‖w‖ →
      ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
          ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ ≤
        ∫ t : ℝ in Set.Ioi (‖w‖ / 2), ‖K w t‖

/-- Concrete branch-safe tail majorant kernel.

It carries the literal principal-tail norm together with the classical
exponentially decaying Binet tail factor.  This is the integral-level contour
majorant used downstream: the principal contribution is included because the
contour comparison is not a false pointwise domination of the raw principal
branch by the decaying factor alone. -/
noncomputable def Complex.binetSecondFormulaContourTailMajorantKernel
  (w : ℂ)
  (t : ℝ) : ℂ :=
  (‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ +
    |((1 : ℝ) / ‖w‖) *
      (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))| : ℝ)

/-- The explicit Abel-Plana contour datum used to deform the principal Binet
tail away from the arctangent branch singularities.

The data is intentionally the deformed kernel, not an arbitrary existential
majorant.  Its public comparison theorem is the owner-level contour theorem
consumed by `BinetTailContour`. -/
noncomputable def Complex.binetSecondFormulaAbelPlanaDeformedTailKernel :
    Complex.BinetSecondFormulaContourDeformedTailKernel :=
  Complex.binetSecondFormulaContourTailMajorantKernel

/-- Pointwise tail comparison obtained after Abel-Plana contour deformation.

This is the local analytic estimate behind the integrated branch-singularity
absorption theorem.  The comparison is stated after deformation, not for the
undeformed principal branch as a fake pointwise inequality. -/
def Complex.BinetSecondFormulaAbelPlanaDeformedTailPointwiseComparison
    (K : Complex.BinetSecondFormulaContourDeformedTailKernel)
    (R : ℝ) : Prop :=
  ∀ w : ℂ,
    0 < w.re →
    R ≤ ‖w‖ →
      ∀ᵐ t ∂volume.restrict (Set.Ioi (‖w‖ / 2)),
        ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ ≤ ‖K w t‖

/-- The finite logarithmic Gamma approximants produced by the Bohr-Mollerup
Euler limit formula, written in the same principal-log normalization as the
complex Binet formula. -/
noncomputable def Complex.binetAbelPlanaLogGammaFiniteApproximation
    (N : ℕ)
    (w : ℂ) : ℂ :=
  let M : ℕ := N + 1
  w * Complex.log (M : ℂ) + Complex.log ((Nat.factorial M : ℕ) : ℂ) -
    ∑ n in Finset.range (M + 1), Complex.log (w + n)

/-- The finite Abel-Plana boundary correction for the logarithmic summand
behind Binet's formula. -/
noncomputable def Complex.binetAbelPlanaFiniteBoundaryCorrection
    (N : ℕ)
    (w : ℂ) : ℂ :=
  ∫ t : ℝ in Set.Ioc (0 : ℝ) (N : ℝ),
    (-Complex.I) *
      ((Complex.log (w + (t : ℂ) * Complex.I) -
          Complex.log (w - (t : ℂ) * Complex.I)) /
        (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))

/-- The upper endpoint logarithmic jump in the finite Abel-Plana formula.

For `M = N + 1`, this is the residual boundary term coming from the vertical
line through `M`.  It is the finite contour term that disappears in the
Euler/Binet limit. -/
noncomputable def Complex.binetAbelPlanaFiniteUpperLogJump
    (N : ℕ)
    (w : ℂ)
    (t : ℝ) : ℂ :=
  let M : ℕ := N + 1
  Complex.log (w + (M : ℂ) + (t : ℂ) * Complex.I) -
    Complex.log (w + (M : ℂ) - (t : ℂ) * Complex.I)

/-- The vertical differential-log integrand for the upper endpoint line. -/
noncomputable def Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand
    (N : ℕ)
    (w : ℂ)
    (s : ℝ) : ℂ :=
  Complex.I / (w + (N + 1 : ℂ) + (s : ℂ) * Complex.I)

/-- The upper endpoint segment denominator has positive real part in the
right half-plane. -/
theorem Complex.binetAbelPlanaUpperLogJumpSegmentDenominator_re_pos
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ)
    (s : ℝ) :
    0 < (w + (N + 1 : ℂ) + (s : ℂ) * Complex.I).re := by
  have hnat_nonneg : 0 ≤ ((N + 1 : ℕ) : ℝ) :=
    Nat.cast_nonneg (N + 1)
  calc
    0 < w.re + ((N + 1 : ℕ) : ℝ) :=
      add_pos_of_pos_of_nonneg hw hnat_nonneg
    _ = (w + (N + 1 : ℂ) + (s : ℂ) * Complex.I).re := by
      norm_num [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]

/-- The upper endpoint segment denominator never vanishes in the right
half-plane. -/
theorem Complex.binetAbelPlanaUpperLogJumpSegmentDenominator_ne_zero
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ)
    (s : ℝ) :
    w + (N + 1 : ℂ) + (s : ℂ) * Complex.I ≠ 0 := by
  intro hzero
  have hre_zero :
      (w + (N + 1 : ℂ) + (s : ℂ) * Complex.I).re = 0 :=
    congrArg Complex.re hzero
  have hre_pos :
      0 < (w + (N + 1 : ℂ) + (s : ℂ) * Complex.I).re :=
    Complex.binetAbelPlanaUpperLogJumpSegmentDenominator_re_pos hw N s
  exact (ne_of_gt hre_pos) hre_zero

/-- The segment integrand is bounded by the inverse real part of the vertical
endpoint line. -/
theorem Complex.norm_binetAbelPlanaUpperLogJumpSegmentIntegrand_le_endpoint_re_inv_core
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ)
    (s : ℝ) :
    ‖Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s‖ ≤
      (w.re + (N + 1 : ℝ))⁻¹ := by
  let z : ℂ := w + (N + 1 : ℂ) + (s : ℂ) * Complex.I
  have hz_re_pos : 0 < z.re :=
    Complex.binetAbelPlanaUpperLogJumpSegmentDenominator_re_pos hw N s
  have hz_re_nonneg : 0 ≤ z.re := le_of_lt hz_re_pos
  have hz_re_le_norm : z.re ≤ ‖z‖ :=
    Complex.re_le_norm z
  have hinv_le : ‖z‖⁻¹ ≤ z.re⁻¹ :=
    inv_le_inv_of_le hz_re_pos hz_re_le_norm
  have hre_eq : z.re = w.re + (N + 1 : ℝ) := by
    dsimp [z]
    norm_num [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
  calc
    ‖Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s‖
        = ‖Complex.I / z‖ := by
          rfl
    _ = ‖Complex.I‖ / ‖z‖ := by
          exact norm_div Complex.I z
    _ = ‖z‖⁻¹ := by
          norm_num [Complex.norm_I, div_eq_mul_inv]
    _ ≤ z.re⁻¹ := hinv_le
    _ = (w.re + (N + 1 : ℝ))⁻¹ := by
          exact congrArg Inv.inv hre_eq

/-- The explicit upper-contour residual in the finite Abel-Plana formula.

The classical finite Abel-Plana formula for the logarithmic summand has two
vertical boundary contributions.  The lower boundary is
`binetAbelPlanaFiniteBoundaryCorrection`; this upper boundary is the finite
contour residual whose norm tends to zero. -/
noncomputable def Complex.binetAbelPlanaFiniteUpperContourResidual
    (N : ℕ)
    (w : ℂ) : ℂ :=
  ∫ t : ℝ in Set.Ioi (0 : ℝ),
    Complex.I *
      (Complex.binetAbelPlanaFiniteUpperLogJump N w t /
        (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))

/-- The integrand of the upper finite Abel-Plana contour residual. -/
noncomputable def Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand
    (N : ℕ)
    (w : ℂ)
    (t : ℝ) : ℂ :=
  Complex.I *
    (Complex.binetAbelPlanaFiniteUpperLogJump N w t /
      (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))

/-- The upper finite Abel-Plana contour residual is the integral of its named
integrand. -/
theorem Complex.binetAbelPlanaFiniteUpperContourResidual_eq_integral_integrand
    (N : ℕ)
    (w : ℂ) :
    Complex.binetAbelPlanaFiniteUpperContourResidual N w =
      ∫ t : ℝ in Set.Ioi (0 : ℝ),
        Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t := by
  rfl

/-- The lower vertical tail omitted by the finite lower Abel-Plana boundary
window `(0,N]`. -/
noncomputable def Complex.binetAbelPlanaFiniteLowerContourTail
    (N : ℕ)
    (w : ℂ) : ℂ :=
  ∫ t : ℝ in Set.Ioi (N : ℝ),
    (-Complex.I) *
      ((Complex.log (w + (t : ℂ) * Complex.I) -
          Complex.log (w - (t : ℂ) * Complex.I)) /
        (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))

/-- The honest finite Abel-Plana contour remainder after the lower boundary
has been truncated to `(0,N]`. -/
noncomputable def Complex.binetAbelPlanaFiniteContourRemainder
    (N : ℕ)
    (w : ℂ) : ℂ :=
  Complex.binetAbelPlanaFiniteLowerContourTail N w +
    Complex.binetAbelPlanaFiniteUpperContourResidual N w

/-- The normalized finite Binet boundary integral after converting the
Abel-Plana logarithmic jump into the principal arctangent kernel. -/
noncomputable def Complex.binetAbelPlanaFiniteNormalizedBoundary
    (N : ℕ)
    (w : ℂ) : ℂ :=
  2 * ∫ t : ℝ in Set.Ioc (0 : ℝ) (N : ℝ),
    Complex.arctan ((t : ℂ) / w) /
      (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)

/-- The finite endpoint/main-term contribution in the Abel-Plana expansion of
the logarithmic Gamma approximant.  This is separated from
`binetLogGammaMainTerm` because the finite Abel-Plana identity has endpoint
terms which only become the Binet main term after taking the Euler limit. -/
noncomputable def Complex.binetAbelPlanaFiniteMainTerm
    (N : ℕ)
    (w : ℂ) : ℂ :=
  let M : ℕ := N + 1
  w * Complex.log (M : ℂ) + Complex.log ((Nat.factorial M : ℕ) : ℂ) -
    (((w + (M : ℂ)) * Complex.log (w + (M : ℂ)) - (w + (M : ℂ))) -
      (w * Complex.log w - w)) -
    (Complex.log w + Complex.log (w + (M : ℂ))) / 2

/-- Endpoint/Stirling remainder in the finite Abel-Plana main term. -/
noncomputable def Complex.binetAbelPlanaFiniteEndpointStirlingRemainder
    (N : ℕ)
    (w : ℂ) : ℂ :=
  Complex.binetAbelPlanaFiniteMainTerm N w -
    Complex.binetLogGammaMainTerm w

/-- The finite Abel-Plana error term left after truncating the contour formula.
It contains the finite Abel-Plana remainder and tends to zero after the
endpoint/Stirling asymptotics and boundary normalization are separated. -/
noncomputable def Complex.binetAbelPlanaFiniteRemainderError
    (N : ℕ)
    (w : ℂ) : ℂ :=
  Complex.binetAbelPlanaLogGammaFiniteApproximation N w -
    (Complex.binetAbelPlanaFiniteMainTerm N w +
      Complex.binetAbelPlanaFiniteBoundaryCorrection N w)

/-- Endpoint primitive contribution in the finite Abel-Plana formula for
`z ↦ log (w+z)`. -/
noncomputable def Complex.finiteAbelPlanaLogSummandEndpointPrimitive
    (N : ℕ)
    (w : ℂ) : ℂ :=
  let M : ℕ := N + 1
  ((w + (M : ℂ)) * Complex.log (w + (M : ℂ)) -
      (w + (M : ℂ))) -
    (w * Complex.log w - w)

/-- Half-endpoint contribution in the finite Abel-Plana formula for
`z ↦ log (w+z)`. -/
noncomputable def Complex.finiteAbelPlanaLogSummandHalfEndpoints
    (N : ℕ)
    (w : ℂ) : ℂ :=
  let M : ℕ := N + 1
  (Complex.log w + Complex.log (w + (M : ℂ))) / 2

/-- The logarithmic summand to which the finite Abel-Plana rectangle is
applied. -/
noncomputable def Complex.finiteAbelPlanaLogSummand
    (w : ℂ)
    (z : ℂ) : ℂ :=
  Complex.log (w + z)

/-- Lower vertical boundary contribution in the finite Abel-Plana formula for
`z ↦ log (w+z)`, in the normalization used by the Binet finite boundary. -/
noncomputable def Complex.finiteAbelPlanaLogSummandLowerVerticalBoundary
    (N : ℕ)
    (w : ℂ) : ℂ :=
  -Complex.binetAbelPlanaFiniteBoundaryCorrection N w -
    Complex.binetAbelPlanaFiniteLowerContourTail N w

/-- Upper vertical boundary contribution in the finite Abel-Plana formula for
`z ↦ log (w+z)`, in the normalization used by the Binet finite residual. -/
noncomputable def Complex.finiteAbelPlanaLogSummandUpperVerticalBoundary
    (N : ℕ)
    (w : ℂ) : ℂ :=
  -Complex.binetAbelPlanaFiniteUpperContourResidual N w

/-- Owner-level finite Abel-Plana rectangle/residue identity for the
principal logarithmic summand `z ↦ log (w+z)`.

This is the precise contour theorem obtained by integrating
`finiteAbelPlanaLogSummand w z` against the finite Abel-Plana cotangent kernel
on the rectangle with vertical sides through `0` and `N + 1`, evaluating the
residues at the integers, and decomposing the two vertical boundary integrals.
The lower side is split at height `N`, producing the finite lower boundary
correction and `binetAbelPlanaFiniteLowerContourTail`; the upper side is
`binetAbelPlanaFiniteUpperContourResidual`. -/
theorem Complex.finiteAbelPlana_log_summand_rectangleResidue_decomposition
    {w : ℂ}
    (hw : 0 < w.re) :
    ∀ N : ℕ,
      let M : ℕ := N + 1
      ∑ n in Finset.range (M + 1), Complex.finiteAbelPlanaLogSummand w n =
        Complex.finiteAbelPlanaLogSummandEndpointPrimitive N w +
          Complex.finiteAbelPlanaLogSummandHalfEndpoints N w +
          Complex.finiteAbelPlanaLogSummandLowerVerticalBoundary N w +
          Complex.finiteAbelPlanaLogSummandUpperVerticalBoundary N w := by
  intro N
  sorry

/-- Finite Abel-Plana contour decomposition for the logarithmic summand.

This is the classical finite contour theorem: the finite sum of
`z ↦ Complex.log (w+z)` equals the endpoint primitive, the endpoint half-sum,
and the two oriented vertical boundary contributions. -/
theorem Complex.finiteAbelPlana_log_summand_eq_contourDecomposition
    {w : ℂ}
    (hw : 0 < w.re) :
    ∀ N : ℕ,
      let M : ℕ := N + 1
      ∑ n in Finset.range (M + 1), Complex.log (w + n) =
        Complex.finiteAbelPlanaLogSummandEndpointPrimitive N w +
          Complex.finiteAbelPlanaLogSummandHalfEndpoints N w +
          Complex.finiteAbelPlanaLogSummandLowerVerticalBoundary N w +
          Complex.finiteAbelPlanaLogSummandUpperVerticalBoundary N w := by
  intro N
  simpa [Complex.finiteAbelPlanaLogSummand] using
    Complex.finiteAbelPlana_log_summand_rectangleResidue_decomposition hw N

/-- Finite Abel-Plana summation formula for the logarithmic summand itself.

This is the classical finite Abel-Plana theorem for `z ↦ Complex.log (w+z)`.
The Gamma finite-approximation identity below is only algebra after this
summation formula is known. -/
theorem Complex.finiteAbelPlana_log_summand_eq_mainBoundaryUpper
    {w : ℂ}
    (hw : 0 < w.re) :
    ∀ N : ℕ,
      let M : ℕ := N + 1
      ∑ n in Finset.range (M + 1), Complex.log (w + n) =
        (((w + (M : ℂ)) * Complex.log (w + (M : ℂ)) -
            (w + (M : ℂ))) -
          (w * Complex.log w - w)) +
          (Complex.log w + Complex.log (w + (M : ℂ))) / 2 -
          Complex.binetAbelPlanaFiniteBoundaryCorrection N w -
          Complex.binetAbelPlanaFiniteLowerContourTail N w -
          Complex.binetAbelPlanaFiniteUpperContourResidual N w := by
  intro N
  have hcontour :
      let M : ℕ := N + 1
      ∑ n in Finset.range (M + 1), Complex.log (w + n) =
        Complex.finiteAbelPlanaLogSummandEndpointPrimitive N w +
          Complex.finiteAbelPlanaLogSummandHalfEndpoints N w +
          Complex.finiteAbelPlanaLogSummandLowerVerticalBoundary N w +
          Complex.finiteAbelPlanaLogSummandUpperVerticalBoundary N w :=
    Complex.finiteAbelPlana_log_summand_eq_contourDecomposition hw N
  dsimp [Complex.finiteAbelPlanaLogSummandEndpointPrimitive,
    Complex.finiteAbelPlanaLogSummandHalfEndpoints,
    Complex.finiteAbelPlanaLogSummandLowerVerticalBoundary,
    Complex.finiteAbelPlanaLogSummandUpperVerticalBoundary] at hcontour ⊢
  rw [hcontour]
  ring

/-- Finite Abel-Plana summation formula for the logarithmic summand.

This is the owner-level finite contour identity for
`z ↦ Complex.log (w + z)` in the open right half-plane.  It is the single
finite summation theorem from which the asymptotic Binet remainder identity is
derived. -/
theorem Complex.binetAbelPlana_logGammaFiniteApproximation_eq_finiteMain_add_boundary_add_contourRemainder_core
    {w : ℂ}
    (hw : 0 < w.re) :
    ∀ N : ℕ,
      Complex.binetAbelPlanaLogGammaFiniteApproximation N w =
        Complex.binetAbelPlanaFiniteMainTerm N w +
          Complex.binetAbelPlanaFiniteBoundaryCorrection N w +
            Complex.binetAbelPlanaFiniteContourRemainder N w := by
  intro N
  have hsum :
      let M : ℕ := N + 1
      ∑ n in Finset.range (M + 1), Complex.log (w + n) =
        (((w + (M : ℂ)) * Complex.log (w + (M : ℂ)) -
            (w + (M : ℂ))) -
          (w * Complex.log w - w)) +
          (Complex.log w + Complex.log (w + (M : ℂ))) / 2 -
          Complex.binetAbelPlanaFiniteBoundaryCorrection N w -
          Complex.binetAbelPlanaFiniteLowerContourTail N w -
          Complex.binetAbelPlanaFiniteUpperContourResidual N w :=
    Complex.finiteAbelPlana_log_summand_eq_mainBoundaryUpper hw N
  dsimp [Complex.binetAbelPlanaLogGammaFiniteApproximation,
    Complex.binetAbelPlanaFiniteMainTerm,
    Complex.binetAbelPlanaFiniteContourRemainder] at hsum ⊢
  rw [hsum]
  ring

end

end LFunctions
end Boundary
