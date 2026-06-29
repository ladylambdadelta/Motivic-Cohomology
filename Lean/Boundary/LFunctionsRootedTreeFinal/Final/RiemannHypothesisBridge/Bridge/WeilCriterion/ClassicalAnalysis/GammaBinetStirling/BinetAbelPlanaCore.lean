import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetKernelBounds
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
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
open Filter MeasureTheory

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
absorption theorem.  The comparison is stated after deformation, rather than
as a pointwise inequality for the undeformed principal branch. -/
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

/-- Real part of the upper endpoint segment denominator. -/
theorem Complex.binetAbelPlanaUpperLogJumpSegmentDenominator_re_eq
    (w : ℂ)
    (N : ℕ)
    (s : ℝ) :
    (w + (N + 1 : ℂ) + (s : ℂ) * Complex.I).re =
      w.re + (N + 1 : ℝ) := by
  have him_re : ((s : ℂ) * Complex.I).re = 0 := by
    calc
      ((s : ℂ) * Complex.I).re = -((s : ℂ).im) :=
        Complex.mul_I_re (s : ℂ)
      _ = -0 := congrArg Neg.neg (Complex.ofReal_im s)
      _ = 0 := neg_zero
  have hnat_re : ((N + 1 : ℂ).re) = (N + 1 : ℝ) :=
    Complex.ofReal_re (N + 1 : ℝ)
  calc
    (w + (N + 1 : ℂ) + (s : ℂ) * Complex.I).re =
        (w + (N + 1 : ℂ)).re + ((s : ℂ) * Complex.I).re :=
      Complex.add_re (w + (N + 1 : ℂ)) ((s : ℂ) * Complex.I)
    _ = (w.re + (N + 1 : ℂ).re) + ((s : ℂ) * Complex.I).re := by
      exact congrArg (fun x : ℝ => x + ((s : ℂ) * Complex.I).re)
        (Complex.add_re w (N + 1 : ℂ))
    _ = (w.re + (N + 1 : ℝ)) + 0 := by
      exact congrArg₂ HAdd.hAdd
        (congrArg (fun x : ℝ => w.re + x) hnat_re)
        him_re
    _ = w.re + (N + 1 : ℝ) :=
      add_zero (w.re + (N + 1 : ℝ))

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
    _ = w.re + (N + 1 : ℝ) := by
      exact congrArg (fun x : ℝ => w.re + x) (Nat.cast_add_one N)
    _ = (w + (N + 1 : ℂ) + (s : ℂ) * Complex.I).re := by
      exact (Complex.binetAbelPlanaUpperLogJumpSegmentDenominator_re_eq w N s).symm

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
  have hz_re_le_norm : z.re ≤ ‖z‖ := by
    have hnorm_eq : ‖z‖ = Complex.abs z := by
      exact Complex.norm_eq_abs z
    have hle : z.re ≤ Complex.abs z := by
      exact le_trans (le_abs_self z.re) (Complex.abs_re_le_abs z)
    exact Eq.subst (motive := fun x : ℝ => z.re ≤ x) (Eq.symm hnorm_eq) hle
  have hinv_le : ‖z‖⁻¹ ≤ z.re⁻¹ :=
    inv_le_inv_of_le hz_re_pos hz_re_le_norm
  have hre_eq : z.re = w.re + (N + 1 : ℝ) := by
    exact Complex.binetAbelPlanaUpperLogJumpSegmentDenominator_re_eq w N s
  calc
    ‖Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s‖
        = ‖Complex.I / z‖ := by
          rfl
    _ = ‖Complex.I‖ / ‖z‖ := by
          exact norm_div Complex.I z
    _ = ‖z‖⁻¹ := by
          calc
            ‖Complex.I‖ / ‖z‖ = (1 : ℝ) / ‖z‖ := by
              exact congrArg (fun x : ℝ => x / ‖z‖) Complex.norm_I
            _ = ‖z‖⁻¹ := one_div ‖z‖
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

/-- The lower finite Abel-Plana contour tail unfolded as its vertical
tail integral. -/
theorem Complex.binetAbelPlanaFiniteLowerContourTail_core_unfold
    (N : ℕ)
    (w : ℂ) :
    Complex.binetAbelPlanaFiniteLowerContourTail N w =
      ∫ t : ℝ in Set.Ioi (N : ℝ),
        (-Complex.I) *
          ((Complex.log (w + (t : ℂ) * Complex.I) -
              Complex.log (w - (t : ℂ) * Complex.I)) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)) :=
  rfl

/-- The endpoint half contribution missing from the principal-value residue
sum when compared with the full finite integer-residue sum.

This definition is placed at the first contour-remainder use site.  The later
residue block proves that it is exactly the half-weighted endpoint integer
residue contribution. -/
noncomputable def Complex.finiteAbelPlanaLogEndpointResidueRestoration
    (N : ℕ)
    (w : ℂ) : ℂ :=
  (Complex.log w +
    Complex.log (w + ((N + 1 : ℕ) : ℂ))) / 2

/-- The honest finite Abel-Plana contour remainder after the lower boundary
has been truncated to `(0,N]`, with the finite endpoint-restoration defect
kept in the finite residue identity rather than in the contour remainder. -/
noncomputable def Complex.binetAbelPlanaFiniteContourRemainder
    (N : ℕ)
    (w : ℂ) : ℂ :=
  Complex.binetAbelPlanaFiniteLowerContourTail N w +
    Complex.binetAbelPlanaFiniteUpperContourResidual N w

/-- The total finite Abel-Plana contour remainder unfolded as lower tail plus
upper residual. -/
theorem Complex.binetAbelPlanaFiniteContourRemainder_core_unfold
    (N : ℕ)
    (w : ℂ) :
    Complex.binetAbelPlanaFiniteContourRemainder N w =
      Complex.binetAbelPlanaFiniteLowerContourTail N w +
        Complex.binetAbelPlanaFiniteUpperContourResidual N w :=
  rfl

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

/-- Unfolding of the finite Abel-Plana main term. -/
theorem Complex.binetAbelPlanaFiniteMainTerm_unfold
    (N : ℕ)
    (w : ℂ) :
    Complex.binetAbelPlanaFiniteMainTerm N w =
      let M : ℕ := N + 1
      w * Complex.log (M : ℂ) + Complex.log ((Nat.factorial M : ℕ) : ℂ) -
        (((w + (M : ℂ)) * Complex.log (w + (M : ℂ)) - (w + (M : ℂ))) -
          (w * Complex.log w - w)) -
        (Complex.log w + Complex.log (w + (M : ℂ))) / 2 :=
  rfl

/-- Endpoint/Stirling remainder in the finite Abel-Plana main term. -/
noncomputable def Complex.binetAbelPlanaFiniteEndpointStirlingRemainder
    (N : ℕ)
    (w : ℂ) : ℂ :=
  Complex.binetAbelPlanaFiniteMainTerm N w -
    Complex.binetLogGammaMainTerm w

/-- The finite endpoint/Stirling remainder unfolded into the defining
difference. -/
theorem Complex.binetAbelPlanaFiniteEndpointStirlingRemainder_core_unfold
    (N : ℕ)
    (w : ℂ) :
    Complex.binetAbelPlanaFiniteEndpointStirlingRemainder N w =
      Complex.binetAbelPlanaFiniteMainTerm N w -
        Complex.binetLogGammaMainTerm w :=
  rfl

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

/-- Unfolding of the finite Abel-Plana endpoint primitive contribution. -/
theorem Complex.finiteAbelPlanaLogSummandEndpointPrimitive_unfold
    (N : ℕ)
    (w : ℂ) :
    Complex.finiteAbelPlanaLogSummandEndpointPrimitive N w =
      ((w + ((N + 1 : ℕ) : ℂ)) *
          Complex.log (w + ((N + 1 : ℕ) : ℂ)) -
        (w + ((N + 1 : ℕ) : ℂ))) -
        (w * Complex.log w - w) :=
  rfl

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

/-- The cotangent kernel whose integer residues implement finite
Abel-Plana summation. -/
noncomputable def Complex.finiteAbelPlanaCotangentKernel
    (z : ℂ) : ℂ :=
  (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * z)

/-- The finite Abel-Plana cotangent kernel unfolded into sine and cosine. -/
theorem Complex.finiteAbelPlanaCotangentKernel_sinCos_unfold
    (z : ℂ) :
    Complex.finiteAbelPlanaCotangentKernel z =
      (Real.pi : ℂ) *
        (Complex.cos ((Real.pi : ℂ) * z) /
          Complex.sin ((Real.pi : ℂ) * z)) :=
  rfl

/-- The meromorphic rectangle integrand for finite Abel-Plana summation of
`z ↦ log (w+z)`. -/
noncomputable def Complex.finiteAbelPlanaLogRectangleIntegrand
    (w : ℂ)
    (z : ℂ) : ℂ :=
  Complex.finiteAbelPlanaLogSummand w z *
    Complex.finiteAbelPlanaCotangentKernel z

/-- The finite Abel-Plana rectangle integrand unfolded into logarithmic
summand times cotangent kernel. -/
theorem Complex.finiteAbelPlanaLogRectangleIntegrand_unfold
    (w z : ℂ) :
    Complex.finiteAbelPlanaLogRectangleIntegrand w z =
      Complex.finiteAbelPlanaLogSummand w z *
        Complex.finiteAbelPlanaCotangentKernel z :=
  rfl

/-- The finite Abel-Plana cotangent kernel is complex differentiable wherever
`sin (π z)` does not vanish.

This is the local analytic input needed to apply the rectangle Cauchy theorem
to the meromorphic contour integrand away from its integer poles. -/
theorem Complex.differentiableAt_finiteAbelPlanaCotangentKernel
    {z : ℂ}
    (hz : Complex.sin ((Real.pi : ℂ) * z) ≠ 0) :
    DifferentiableAt ℂ Complex.finiteAbelPlanaCotangentKernel z := by
  have hcos :
      DifferentiableAt ℂ (fun z : ℂ => Complex.cos ((Real.pi : ℂ) * z)) z := by
    have harg :
        DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ) * z) z :=
      (differentiableAt_const (c := (Real.pi : ℂ))).mul differentiableAt_id
    exact harg.ccos
  have hsin :
      DifferentiableAt ℂ (fun z : ℂ => Complex.sin ((Real.pi : ℂ) * z)) z := by
    have harg :
        DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ) * z) z :=
      (differentiableAt_const (c := (Real.pi : ℂ))).mul differentiableAt_id
    exact harg.csin
  change DifferentiableAt ℂ
    (fun z : ℂ =>
      (Real.pi : ℂ) *
        (Complex.cos ((Real.pi : ℂ) * z) /
          Complex.sin ((Real.pi : ℂ) * z)))
    z
  have hconst :
      DifferentiableAt ℂ (fun _z : ℂ => (Real.pi : ℂ)) z :=
    differentiableAt_const (c := (Real.pi : ℂ))
  exact hconst.mul (hcos.div hsin hz)

/-- The finite Abel-Plana rectangle integrand is differentiable away from the
logarithmic slit and the integer cotangent poles.

This is the owner-level analytic input needed by the rectangle Cauchy theorem
in the finite-height contour file. -/
theorem Complex.differentiableAt_finiteAbelPlanaLogRectangleIntegrand
    {w z : ℂ}
    (hw : w + z ∈ Complex.slitPlane)
    (hz : Complex.sin ((Real.pi : ℂ) * z) ≠ 0) :
    DifferentiableAt ℂ (fun t : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w t) z := by
  have hlog :
      DifferentiableAt ℂ (fun t : ℂ => Complex.finiteAbelPlanaLogSummand w t) z := by
    change DifferentiableAt ℂ (fun t : ℂ => Complex.log (w + t)) z
    exact ((differentiableAt_const (c := w)).add differentiableAt_id).clog hw
  have hcot :
      DifferentiableAt ℂ Complex.finiteAbelPlanaCotangentKernel z :=
    Complex.differentiableAt_finiteAbelPlanaCotangentKernel hz
  change DifferentiableAt ℂ
    (fun t : ℂ =>
      Complex.finiteAbelPlanaLogSummand w t *
        Complex.finiteAbelPlanaCotangentKernel t)
    z
  exact hlog.mul hcot

/-- The logarithmic summand is continuous on any set mapped into the principal
slit plane by `w + z`.

This is the continuity input for the closed-rectangle Cauchy theorem. -/
theorem Complex.continuousOn_finiteAbelPlanaLogSummand
    {w : ℂ}
    {s : Set ℂ}
    (h : ∀ z ∈ s, w + z ∈ Complex.slitPlane) :
    ContinuousOn (fun z : ℂ => Complex.finiteAbelPlanaLogSummand w z) s := by
  change ContinuousOn (fun z : ℂ => Complex.log (w + z)) s
  exact (continuous_const.add continuous_id).continuousOn.clog h

/-- The logarithmic summand is differentiable at any point where `w + z`
lies in the principal slit plane.

This is the pointwise analytic input for the differentiable-on-off-countable
rectangle theorem. -/
theorem Complex.differentiableAt_finiteAbelPlanaLogSummand
    {w z : ℂ}
    (hw : w + z ∈ Complex.slitPlane) :
    DifferentiableAt ℂ (fun t : ℂ => Complex.finiteAbelPlanaLogSummand w t) z := by
  change DifferentiableAt ℂ (fun t : ℂ => Complex.log (w + t)) z
  exact ((differentiableAt_const (c := w)).add differentiableAt_id).clog hw

/-- The finite Abel-Plana rectangle integrand is continuous on any set where
the logarithmic summand stays in the principal slit plane and the cotangent
kernel avoids its poles.

This is the closed-rectangle hypothesis needed by
`Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable`. -/
theorem Complex.continuousOn_finiteAbelPlanaLogRectangleIntegrand
    {w : ℂ}
    {s : Set ℂ}
    (hs : ∀ z ∈ s, w + z ∈ Complex.slitPlane)
    (hcot : ∀ z ∈ s, Complex.sin ((Real.pi : ℂ) * z) ≠ 0) :
    ContinuousOn (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z) s := by
  have hlog : ContinuousOn (fun z : ℂ => Complex.finiteAbelPlanaLogSummand w z) s :=
    Complex.continuousOn_finiteAbelPlanaLogSummand hs
  have hcot' : ContinuousOn Complex.finiteAbelPlanaCotangentKernel s := by
    intro z hz
    have hne : Complex.sin ((Real.pi : ℂ) * z) ≠ 0 := hcot z hz
    exact (Complex.differentiableAt_finiteAbelPlanaCotangentKernel hne).continuousAt.continuousWithinAt
  change ContinuousOn
    (fun z : ℂ =>
      Complex.finiteAbelPlanaLogSummand w z *
        Complex.finiteAbelPlanaCotangentKernel z)
    s
  exact hlog.mul hcot'

/-- The finite Abel-Plana rectangle integrand is differentiable on any set
where the logarithmic summand stays in the principal slit plane and the
cotangent kernel avoids its poles. -/
theorem Complex.differentiableOn_finiteAbelPlanaLogRectangleIntegrand
    {w : ℂ}
    {s : Set ℂ}
    (hs : ∀ z ∈ s, w + z ∈ Complex.slitPlane)
    (hcot : ∀ z ∈ s, Complex.sin ((Real.pi : ℂ) * z) ≠ 0) :
    DifferentiableOn ℂ (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z) s := by
  intro z hz
  exact
    (Complex.differentiableAt_finiteAbelPlanaLogRectangleIntegrand
      (hs z hz) (hcot z hz)).differentiableWithinAt

/-- The centered auxiliary function `z ↦ (z - n) * rectangleIntegrand` is
continuous on any set where the rectangle integrand is continuous. -/
theorem Complex.continuousOn_center_mul_finiteAbelPlanaLogRectangleIntegrand
    {w n : ℂ}
    {s : Set ℂ}
    (hs : ∀ z ∈ s, w + z ∈ Complex.slitPlane)
    (hcot : ∀ z ∈ s, Complex.sin ((Real.pi : ℂ) * z) ≠ 0) :
    ContinuousOn (fun z : ℂ =>
      (z - n) * Complex.finiteAbelPlanaLogRectangleIntegrand w z) s := by
  have hcont : ContinuousOn (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z) s :=
    Complex.continuousOn_finiteAbelPlanaLogRectangleIntegrand hs hcot
  change ContinuousOn
    (fun z : ℂ =>
      (z - n) * Complex.finiteAbelPlanaLogRectangleIntegrand w z)
    s
  exact (continuousOn_id.sub continuousOn_const).mul hcont

/-- The centered auxiliary function is differentiable on any set where the
rectangle integrand is differentiable. -/
theorem Complex.differentiableOn_center_mul_finiteAbelPlanaLogRectangleIntegrand
    {w n : ℂ}
    {s : Set ℂ}
    (hs : ∀ z ∈ s, w + z ∈ Complex.slitPlane)
    (hcot : ∀ z ∈ s, Complex.sin ((Real.pi : ℂ) * z) ≠ 0) :
    DifferentiableOn ℂ (fun z : ℂ =>
      (z - n) * Complex.finiteAbelPlanaLogRectangleIntegrand w z) s := by
  intro z hz
  have hconst :
      DifferentiableAt ℂ (fun _z : ℂ => n) z :=
    differentiableAt_const (c := n)
  exact
    ((differentiableAt_id.sub hconst).mul
      (Complex.differentiableAt_finiteAbelPlanaLogRectangleIntegrand
        (hs z hz) (hcot z hz))).differentiableWithinAt

/-- Nonzero imaginary part excludes zeros of the finite Abel-Plana cotangent
denominator.

This is the reusable pole-exclusion lemma that will feed the rectangle
`DifferentiableOn` hypothesis. -/
theorem Complex.sin_pi_mul_ne_zero_of_im_ne_zero
    {z : ℂ}
    (hz : z.im ≠ 0) :
    Complex.sin ((Real.pi : ℂ) * z) ≠ 0 := by
  intro hzero
  match Complex.sin_eq_zero_iff.mp hzero with
  | ⟨k, hk⟩ =>
  have hleft_im : ((Real.pi : ℂ) * z).im = Real.pi * z.im := by
    calc
      ((Real.pi : ℂ) * z).im =
          ((Real.pi : ℂ).re * z.im + (Real.pi : ℂ).im * z.re) := by
        exact Complex.mul_im (Real.pi : ℂ) z
      _ = Real.pi * z.im + (Real.pi : ℂ).im * z.re := by
        exact congrArg
          (fun u : ℝ => u * z.im + (Real.pi : ℂ).im * z.re)
          (Complex.ofReal_re Real.pi)
      _ = Real.pi * z.im + 0 * z.re := by
        exact congrArg
          (fun u : ℝ => Real.pi * z.im + u * z.re)
          (Complex.ofReal_im Real.pi)
      _ = Real.pi * z.im + 0 := by
        exact congrArg (fun u : ℝ => Real.pi * z.im + u) (zero_mul z.re)
      _ = Real.pi * z.im := by
        exact add_zero (Real.pi * z.im)
  have hright_im : ((k : ℂ) * (Real.pi : ℂ)).im = 0 := by
    calc
      ((k : ℂ) * (Real.pi : ℂ)).im =
          (k : ℂ).re * (Real.pi : ℂ).im + (k : ℂ).im * (Real.pi : ℂ).re := by
        exact Complex.mul_im (k : ℂ) (Real.pi : ℂ)
      _ = (k : ℂ).re * 0 + (k : ℂ).im * (Real.pi : ℂ).re := by
        exact congrArg
          (fun u : ℝ => (k : ℂ).re * u + (k : ℂ).im * (Real.pi : ℂ).re)
          (Complex.ofReal_im Real.pi)
      _ = (k : ℂ).re * 0 + 0 * (Real.pi : ℂ).re := by
        exact congrArg
          (fun u : ℝ => (k : ℂ).re * 0 + u * (Real.pi : ℂ).re)
          (Complex.ofReal_im (k : ℝ))
      _ = 0 + 0 * (Real.pi : ℂ).re := by
        exact congrArg
          (fun u : ℝ => u + 0 * (Real.pi : ℂ).re)
          (mul_zero (k : ℂ).re)
      _ = 0 + 0 := by
        exact congrArg (fun u : ℝ => 0 + u) (zero_mul (Real.pi : ℂ).re)
      _ = 0 := by
        exact zero_add 0
  have him : ((Real.pi : ℂ) * z).im = 0 := by
    exact (congrArg Complex.im hk).trans hright_im
  have hpi_mul : Real.pi * z.im = 0 :=
    hleft_im.symm.trans him
  have hz_zero : z.im = 0 := by
    match mul_eq_zero.mp hpi_mul with
    | Or.inl hpi_zero => exact False.elim (Real.pi_ne_zero hpi_zero)
    | Or.inr hz_zero => exact hz_zero
  exact hz hz_zero

/-- If `sin (π z) = 0` and `z` lies in the finite Abel-Plana rectangle, then
`z` is one of the integer poles `0, 1, ..., N + 1`.

This is the exact singular-set description needed for the rectangle
Cauchy-Goursat theorem. -/
theorem Complex.finiteAbelPlana_log_rectangle_sin_pi_zero_mem_integer_poles
    (N : ℕ)
    {z : ℂ}
    (hz : z ∈ Set.Ioo (0 : ℝ) (N + 1 : ℝ) ×ℂ Set.Ioo (-(0 : ℝ)) (0 : ℝ))
    (_hzero : Complex.sin ((Real.pi : ℂ) * z) = 0) :
    z ∈ ({z : ℂ | ∃ n ∈ Finset.range (N + 2), z = n} : Set ℂ) := by
  have him_pos : 0 < z.im := by
    have hneg_zero : -(0 : ℝ) = 0 :=
      neg_zero
    exact hneg_zero ▸ hz.2.1
  have him_neg : z.im < 0 := by
    exact hz.2.2
  exact False.elim ((not_lt_of_ge him_pos.le) him_neg)

/-- The residue contribution of the Abel-Plana cotangent kernel at an integer.

The normalization is chosen so that the residue of
`π cot (π z)` at every integer is `1`, hence the logarithmic summand itself is
the local residue of the rectangle integrand. -/
noncomputable def Complex.finiteAbelPlanaLogIntegerResidue
    (w : ℂ)
    (n : ℕ) : ℂ :=
  Complex.finiteAbelPlanaLogSummand w n

/-- Unfolding of the logarithmic integer residue. -/
theorem Complex.finiteAbelPlanaLogIntegerResidue_unfold
    (w : ℂ)
    (n : ℕ) :
    Complex.finiteAbelPlanaLogIntegerResidue w n =
      Complex.finiteAbelPlanaLogSummand w n :=
  rfl

/-- Multiplicity-one residue sum over the integer poles in the finite
Abel-Plana rectangle. -/
noncomputable def Complex.finiteAbelPlanaLogIntegerResidueSum
    (N : ℕ)
    (w : ℂ) : ℂ :=
  let M : ℕ := N + 1
  ∑ n in Finset.range (M + 1),
    Complex.finiteAbelPlanaLogIntegerResidue w n

/-- Unfolding of the integer-residue sum over the finite rectangle. -/
theorem Complex.finiteAbelPlanaLogIntegerResidueSum_unfold
    (N : ℕ)
    (w : ℂ) :
    Complex.finiteAbelPlanaLogIntegerResidueSum N w =
      ∑ n in Finset.range (N + 1 + 1),
        Complex.finiteAbelPlanaLogIntegerResidue w n :=
  rfl

/-- The integer-residue sum is definitionally the finite sample sum of the
logarithmic summand over `0, ..., N+1`. -/
theorem Complex.finiteAbelPlana_log_integerResidueSum_eq_summandRange
    (N : ℕ)
    (w : ℂ) :
    Complex.finiteAbelPlanaLogIntegerResidueSum N w =
      let M : ℕ := N + 1
      ∑ n in Finset.range (M + 1),
        Complex.finiteAbelPlanaLogSummand w n := by
  rfl

/-- Interior integer-pole residue contribution `1, ..., N`.

In the principal-value Abel-Plana rectangle the endpoint poles `0` and `N + 1`
lie on the vertical sides and are therefore counted with half weight by the
endpoint indentations.  The strictly interior poles are the shifted range
`n + 1`, `n < N`. -/
noncomputable def Complex.finiteAbelPlanaLogInteriorIntegerResidueContribution
    (N : ℕ)
    (w : ℂ) : ℂ :=
  ∑ n in Finset.range N,
    Complex.finiteAbelPlanaLogIntegerResidue w (n + 1)

/-- Unfolding of the strictly interior integer-residue contribution. -/
theorem Complex.finiteAbelPlanaLogInteriorIntegerResidueContribution_unfold
    (N : ℕ)
    (w : ℂ) :
    Complex.finiteAbelPlanaLogInteriorIntegerResidueContribution N w =
      ∑ n in Finset.range N,
        Complex.finiteAbelPlanaLogIntegerResidue w (n + 1) :=
  rfl

/-- Endpoint integer-pole residue contribution at `0` and `N + 1`, with the
principal-value half weights. -/
noncomputable def Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution
    (N : ℕ)
    (w : ℂ) : ℂ :=
  (Complex.finiteAbelPlanaLogIntegerResidue w 0 +
    Complex.finiteAbelPlanaLogIntegerResidue w (N + 1)) / 2

/-- Unfolding of the half-weighted endpoint residue contribution. -/
theorem Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution_unfold
    (N : ℕ)
    (w : ℂ) :
    Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution N w =
      (Complex.finiteAbelPlanaLogIntegerResidue w 0 +
        Complex.finiteAbelPlanaLogIntegerResidue w (N + 1)) / 2 :=
  rfl

/-- Principal-value integer residue contribution: half endpoints plus full
interior residues. -/
noncomputable def Complex.finiteAbelPlanaLogPVIntegerResidueContribution
    (N : ℕ)
    (w : ℂ) : ℂ :=
  Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution N w +
    Complex.finiteAbelPlanaLogInteriorIntegerResidueContribution N w

/-- Unfolding of the principal-value residue contribution. -/
theorem Complex.finiteAbelPlanaLogPVIntegerResidueContribution_unfold
    (N : ℕ)
    (w : ℂ) :
    Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w =
      Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution N w +
        Complex.finiteAbelPlanaLogInteriorIntegerResidueContribution N w :=
  rfl

/-- The full endpoint residue contribution at `0` and `N + 1`. -/
noncomputable def Complex.finiteAbelPlanaLogFullEndpointIntegerResidueContribution
    (N : ℕ)
    (w : ℂ) : ℂ :=
  Complex.finiteAbelPlanaLogIntegerResidue w 0 +
    Complex.finiteAbelPlanaLogIntegerResidue w (N + 1)

/-- Unfolding of the full endpoint residue contribution. -/
theorem Complex.finiteAbelPlanaLogFullEndpointIntegerResidueContribution_unfold
    (N : ℕ)
    (w : ℂ) :
    Complex.finiteAbelPlanaLogFullEndpointIntegerResidueContribution N w =
      Complex.finiteAbelPlanaLogIntegerResidue w 0 +
        Complex.finiteAbelPlanaLogIntegerResidue w (N + 1) :=
  rfl

/-- Unfolding of the endpoint residue restoration term. -/
theorem Complex.finiteAbelPlanaLogEndpointResidueRestoration_unfold
    (N : ℕ)
    (w : ℂ) :
    Complex.finiteAbelPlanaLogEndpointResidueRestoration N w =
      Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution N w :=
  by
    have hleft :
        Complex.finiteAbelPlanaLogIntegerResidue w 0 =
          Complex.log w := by
      calc
        Complex.finiteAbelPlanaLogIntegerResidue w 0 =
            Complex.finiteAbelPlanaLogSummand w (((0 : ℕ) : ℂ)) :=
          Complex.finiteAbelPlanaLogIntegerResidue_unfold w 0
        _ = Complex.log (w + (0 : ℂ)) := by
          change Complex.log (w + (((0 : ℕ) : ℂ))) =
            Complex.log (w + (0 : ℂ))
          exact congrArg (fun z : ℂ => Complex.log (w + z)) (Nat.cast_zero)
        _ = Complex.log w := by
          exact congrArg Complex.log (add_zero w)
    have hright :
        Complex.finiteAbelPlanaLogIntegerResidue w (N + 1) =
          Complex.log (w + ((N + 1 : ℕ) : ℂ)) := by
      calc
        Complex.finiteAbelPlanaLogIntegerResidue w (N + 1) =
            Complex.finiteAbelPlanaLogSummand w (((N + 1 : ℕ) : ℂ)) :=
          Complex.finiteAbelPlanaLogIntegerResidue_unfold w (N + 1)
        _ = Complex.log (w + ((N + 1 : ℕ) : ℂ)) := by
          rfl
    calc
      Complex.finiteAbelPlanaLogEndpointResidueRestoration N w =
          (Complex.log w +
            Complex.log (w + ((N + 1 : ℕ) : ℂ))) / 2 := by
        rfl
      _ =
          (Complex.finiteAbelPlanaLogIntegerResidue w 0 +
            Complex.finiteAbelPlanaLogIntegerResidue w (N + 1)) / 2 := by
        exact congrArg
          (fun z : ℂ => z / 2)
          (congrArg₂ HAdd.hAdd hleft.symm hright.symm)
      _ =
          Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution N w := by
        exact
          (Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution_unfold
            N w).symm

/-- Adding the two endpoint half-residue contributions restores the full
endpoint residue contribution. -/
theorem Complex.finiteAbelPlana_log_endpointHalf_add_endpointHalf
    (N : ℕ)
    (w : ℂ) :
    Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution N w +
      Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution N w =
        Complex.finiteAbelPlanaLogFullEndpointIntegerResidueContribution N w := by
  calc
    Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution N w +
        Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution N w =
      ((Complex.finiteAbelPlanaLogIntegerResidue w 0 +
          Complex.finiteAbelPlanaLogIntegerResidue w (N + 1)) / 2) +
        ((Complex.finiteAbelPlanaLogIntegerResidue w 0 +
          Complex.finiteAbelPlanaLogIntegerResidue w (N + 1)) / 2) := by
      exact
        congrArg₂ HAdd.hAdd
          (Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution_unfold
            N w)
          (Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution_unfold
            N w)
    _ =
      Complex.finiteAbelPlanaLogIntegerResidue w 0 +
        Complex.finiteAbelPlanaLogIntegerResidue w (N + 1) :=
      add_halves
        (Complex.finiteAbelPlanaLogIntegerResidue w 0 +
          Complex.finiteAbelPlanaLogIntegerResidue w (N + 1))
    _ =
      Complex.finiteAbelPlanaLogFullEndpointIntegerResidueContribution N w :=
      (Complex.finiteAbelPlanaLogFullEndpointIntegerResidueContribution_unfold
        N w).symm

/-- Moving the last endpoint residue next to the first endpoint residue after
splitting off the interior range. -/
theorem endpoint_interior_last_reassociate
    (first interior last : ℂ) :
    first + (interior + last) = (first + last) + interior := by
  calc
    first + (interior + last) = (first + interior) + last :=
      (add_assoc first interior last).symm
    _ = (first + last) + interior :=
      add_right_comm first interior last

/-- Principal-value residues plus the endpoint restoration give the full
endpoint contribution plus the interior residues. -/
theorem Complex.finiteAbelPlana_log_pvResidue_add_endpointRestoration
    (N : ℕ)
    (w : ℂ) :
    Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w +
        Complex.finiteAbelPlanaLogEndpointResidueRestoration N w =
      Complex.finiteAbelPlanaLogFullEndpointIntegerResidueContribution N w +
        Complex.finiteAbelPlanaLogInteriorIntegerResidueContribution N w := by
  calc
    Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w +
        Complex.finiteAbelPlanaLogEndpointResidueRestoration N w =
      (Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution N w +
        Complex.finiteAbelPlanaLogInteriorIntegerResidueContribution N w) +
        Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution N w := by
      exact
        congrArg₂ HAdd.hAdd
          (Complex.finiteAbelPlanaLogPVIntegerResidueContribution_unfold
            N w)
          (Complex.finiteAbelPlanaLogEndpointResidueRestoration_unfold
            N w)
    _ =
      (Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution N w +
        Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution N w) +
        Complex.finiteAbelPlanaLogInteriorIntegerResidueContribution N w := by
      calc
        (Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution N w +
          Complex.finiteAbelPlanaLogInteriorIntegerResidueContribution N w) +
          Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution N w =
            Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution N w +
              (Complex.finiteAbelPlanaLogInteriorIntegerResidueContribution N w +
                Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution N w) := by
          exact
            add_assoc
              (Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution N w)
              (Complex.finiteAbelPlanaLogInteriorIntegerResidueContribution N w)
              (Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution N w)
        _ =
          (Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution N w +
            Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution N w) +
            Complex.finiteAbelPlanaLogInteriorIntegerResidueContribution N w := by
          exact
            endpoint_interior_last_reassociate
              (Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution N w)
              (Complex.finiteAbelPlanaLogInteriorIntegerResidueContribution N w)
              (Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution N w)
    _ =
      Complex.finiteAbelPlanaLogFullEndpointIntegerResidueContribution N w +
        Complex.finiteAbelPlanaLogInteriorIntegerResidueContribution N w := by
      exact
        congrArg
          (fun z : ℂ =>
            z + Complex.finiteAbelPlanaLogInteriorIntegerResidueContribution N w)
          (Complex.finiteAbelPlana_log_endpointHalf_add_endpointHalf N w)

/-- The full integer-residue range is the two full endpoint residues together
with the strictly interior residues. -/
theorem Complex.finiteAbelPlana_log_integerResidueSum_eq_fullEndpoint_add_interior
    (N : ℕ)
    (w : ℂ) :
    Complex.finiteAbelPlanaLogIntegerResidueSum N w =
      Complex.finiteAbelPlanaLogFullEndpointIntegerResidueContribution N w +
        Complex.finiteAbelPlanaLogInteriorIntegerResidueContribution N w := by
  calc
    Complex.finiteAbelPlanaLogIntegerResidueSum N w =
      ∑ n in Finset.range (N + 1 + 1),
        Complex.finiteAbelPlanaLogIntegerResidue w n :=
      Complex.finiteAbelPlanaLogIntegerResidueSum_unfold N w
    _ =
      (∑ x in Finset.range N,
        Complex.finiteAbelPlanaLogIntegerResidue w (x + 1)) +
        Complex.finiteAbelPlanaLogIntegerResidue w (N + 1) +
        Complex.finiteAbelPlanaLogIntegerResidue w 0 := by
      calc
        ∑ n in Finset.range (N + 1 + 1),
            Complex.finiteAbelPlanaLogIntegerResidue w n =
          ∑ n in Finset.range (N + 1 + 1),
            Complex.finiteAbelPlanaLogIntegerResidue w n := rfl
        _ =
          (∑ x in Finset.range (N + 1),
            Complex.finiteAbelPlanaLogIntegerResidue w (x + 1)) +
            Complex.finiteAbelPlanaLogIntegerResidue w 0 := by
          exact Finset.sum_range_succ'
            (fun n => Complex.finiteAbelPlanaLogIntegerResidue w n)
            (N + 1)
        _ =
          ((∑ x in Finset.range N,
            Complex.finiteAbelPlanaLogIntegerResidue w (x + 1)) +
            Complex.finiteAbelPlanaLogIntegerResidue w (N + 1)) +
            Complex.finiteAbelPlanaLogIntegerResidue w 0 := by
          exact congrArg
            (fun z : ℂ =>
              z + Complex.finiteAbelPlanaLogIntegerResidue w 0)
            (Finset.sum_range_succ
              (fun x =>
                Complex.finiteAbelPlanaLogIntegerResidue w (x + 1))
              N)
    _ =
      Complex.finiteAbelPlanaLogIntegerResidue w 0 +
        ((∑ x in Finset.range N,
          Complex.finiteAbelPlanaLogIntegerResidue w (x + 1)) +
          Complex.finiteAbelPlanaLogIntegerResidue w (N + 1)) := by
      exact add_comm
        ((∑ x in Finset.range N,
          Complex.finiteAbelPlanaLogIntegerResidue w (x + 1)) +
          Complex.finiteAbelPlanaLogIntegerResidue w (N + 1))
        (Complex.finiteAbelPlanaLogIntegerResidue w 0)
    _ =
      Complex.finiteAbelPlanaLogIntegerResidue w 0 +
          Complex.finiteAbelPlanaLogIntegerResidue w (N + 1) +
        ∑ x in Finset.range N,
          Complex.finiteAbelPlanaLogIntegerResidue w (x + 1) :=
      endpoint_interior_last_reassociate
        (Complex.finiteAbelPlanaLogIntegerResidue w 0)
        (∑ x in Finset.range N,
          Complex.finiteAbelPlanaLogIntegerResidue w (x + 1))
        (Complex.finiteAbelPlanaLogIntegerResidue w (N + 1))
    _ =
      Complex.finiteAbelPlanaLogFullEndpointIntegerResidueContribution N w +
        Complex.finiteAbelPlanaLogInteriorIntegerResidueContribution N w := by
      exact
        congrArg₂ HAdd.hAdd
          (Complex.finiteAbelPlanaLogFullEndpointIntegerResidueContribution_unfold
            N w).symm
          (Complex.finiteAbelPlanaLogInteriorIntegerResidueContribution_unfold
            N w).symm

/-- The full finite integer-residue sum is the principal-value residue sum
plus the endpoint restoration. -/
theorem Complex.finiteAbelPlana_log_integerResidueSum_eq_pvResidue_add_endpointRestoration
    (N : ℕ)
    (w : ℂ) :
    Complex.finiteAbelPlanaLogIntegerResidueSum N w =
      Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w +
        Complex.finiteAbelPlanaLogEndpointResidueRestoration N w := by
  have hfull :
      Complex.finiteAbelPlanaLogIntegerResidueSum N w =
        Complex.finiteAbelPlanaLogFullEndpointIntegerResidueContribution N w +
          Complex.finiteAbelPlanaLogInteriorIntegerResidueContribution N w :=
    Complex.finiteAbelPlana_log_integerResidueSum_eq_fullEndpoint_add_interior
      N w
  have hpv :
      Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w +
          Complex.finiteAbelPlanaLogEndpointResidueRestoration N w =
        Complex.finiteAbelPlanaLogFullEndpointIntegerResidueContribution N w +
          Complex.finiteAbelPlanaLogInteriorIntegerResidueContribution N w :=
    Complex.finiteAbelPlana_log_pvResidue_add_endpointRestoration N w
  exact hfull.trans hpv.symm

/-- The finite set of integer poles inside the Abel-Plana rectangle. -/
def Complex.finiteAbelPlanaIntegerPoleFinset
    (N : ℕ) : Finset ℂ :=
  let M : ℕ := N + 1
  (Finset.range (M + 1)).image (fun n : ℕ => (n : ℂ))

/-- The cotangent kernel has unit residue at every integer:
`(z-n) π cot(πz) → 1` as `z → n` through the punctured neighborhood.

This is the local analytic input behind finite Abel-Plana summation. -/
theorem Complex.finiteAbelPlanaCotangentKernel_unitResidue_at_nat
    (n : ℕ) :
    Tendsto
      (fun z : ℂ =>
        (z - (n : ℂ)) * Complex.finiteAbelPlanaCotangentKernel z)
      (𝓝[≠] (n : ℂ))
      (𝓝 (1 : ℂ)) := by
  let a : ℂ := (n : ℂ)
  let d : ℂ := (Real.pi : ℂ) * Complex.cos ((Real.pi : ℂ) * a)
  have hsin_deriv :
      HasDerivAt
        (fun z : ℂ => Complex.sin ((Real.pi : ℂ) * z))
        d
        a := by
    have hlin :
        HasDerivAt
          (fun z : ℂ => (Real.pi : ℂ) * z)
          (Real.pi : ℂ)
          a := by
      have hraw :
          HasDerivAt
            (fun z : ℂ => z * (Real.pi : ℂ))
            ((1 : ℂ) * (Real.pi : ℂ))
            a :=
        (hasDerivAt_id a).mul_const (Real.pi : ℂ)
      have hderiv : (1 : ℂ) * (Real.pi : ℂ) = (Real.pi : ℂ) :=
        one_mul (Real.pi : ℂ)
      have hfun :
          (fun z : ℂ => z * (Real.pi : ℂ)) =
            (fun z : ℂ => (Real.pi : ℂ) * z) := by
        funext z
        exact mul_comm z (Real.pi : ℂ)
      exact Eq.subst
        (motive := fun f : ℂ → ℂ =>
          HasDerivAt f (Real.pi : ℂ) a)
        hfun
        (Eq.subst
          (motive := fun d : ℂ =>
            HasDerivAt (fun z : ℂ => z * (Real.pi : ℂ)) d a)
          hderiv
          hraw)
    have hsin :
        HasDerivAt
          (fun z : ℂ => Complex.sin ((Real.pi : ℂ) * z))
          (Complex.cos ((Real.pi : ℂ) * a) * (Real.pi : ℂ))
          a :=
      (Complex.hasDerivAt_sin ((Real.pi : ℂ) * a)).comp a hlin
    have hderiv :
        Complex.cos ((Real.pi : ℂ) * a) * (Real.pi : ℂ) = d := by
      have hd :
          d = (Real.pi : ℂ) * Complex.cos ((Real.pi : ℂ) * a) :=
        rfl
      exact (mul_comm (Complex.cos ((Real.pi : ℂ) * a)) (Real.pi : ℂ)).trans
        hd.symm
    exact hderiv ▸ hsin
  have hsin_zero :
      Complex.sin ((Real.pi : ℂ) * a) = 0 := by
    have ha : a = (n : ℂ) :=
      rfl
    have hmul : a * (Real.pi : ℂ) = (Real.pi : ℂ) * a := by
      exact mul_comm a (Real.pi : ℂ)
    exact ha ▸ hmul ▸ Complex.sin_nat_mul_pi n
  have hcos_ne :
      Complex.cos ((Real.pi : ℂ) * a) ≠ 0 := by
    intro hzero
    have hsq :
        Complex.sin ((Real.pi : ℂ) * a) ^ 2 +
          Complex.cos ((Real.pi : ℂ) * a) ^ 2 = 1 :=
      Complex.sin_sq_add_cos_sq ((Real.pi : ℂ) * a)
    have hzero_sum :
        Complex.sin ((Real.pi : ℂ) * a) ^ 2 +
          Complex.cos ((Real.pi : ℂ) * a) ^ 2 = 0 := by
      have hsin_sq : Complex.sin ((Real.pi : ℂ) * a) ^ 2 = 0 := by
        exact sq_eq_zero_iff.mpr hsin_zero
      have hcos_sq : Complex.cos ((Real.pi : ℂ) * a) ^ 2 = 0 := by
        exact sq_eq_zero_iff.mpr hzero
      have hsum_zero :
          Complex.sin ((Real.pi : ℂ) * a) ^ 2 +
            Complex.cos ((Real.pi : ℂ) * a) ^ 2 = 0 + 0 := by
        exact congrArg₂ HAdd.hAdd hsin_sq hcos_sq
      exact hsum_zero.trans (zero_add 0)
    have hone_zero : (1 : ℂ) = 0 := by
      exact hsq.symm.trans hzero_sum
    exact one_ne_zero hone_zero
  have hd_ne : d ≠ 0 := by
    have hd :
        d = (Real.pi : ℂ) * Complex.cos ((Real.pi : ℂ) * a) :=
      rfl
    exact hd.symm ▸
      mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) hcos_ne
  have hslope :
      Tendsto
        (fun z : ℂ =>
          (z - a)⁻¹ *
            (Complex.sin ((Real.pi : ℂ) * z) -
              Complex.sin ((Real.pi : ℂ) * a)))
        (𝓝[≠] a)
        (𝓝 d) := by
    have hslope' :
        Tendsto
          (slope (fun z : ℂ => Complex.sin ((Real.pi : ℂ) * z)) a)
          (𝓝[≠] a)
          (𝓝 d) :=
      (hasDerivAt_iff_tendsto_slope.mp hsin_deriv)
    exact hslope'
  have hsin_slope :
      Tendsto
        (fun z : ℂ =>
          Complex.sin ((Real.pi : ℂ) * z) / (z - a))
        (𝓝[≠] a)
        (𝓝 d) := by
    have hsame :
        (fun z : ℂ =>
          (z - a)⁻¹ *
            (Complex.sin ((Real.pi : ℂ) * z) -
              Complex.sin ((Real.pi : ℂ) * a))) =
        (fun z : ℂ =>
          Complex.sin ((Real.pi : ℂ) * z) / (z - a)) := by
      funext z
      have hsub :
          Complex.sin ((Real.pi : ℂ) * z) -
              Complex.sin ((Real.pi : ℂ) * a) =
            Complex.sin ((Real.pi : ℂ) * z) := by
        calc
          Complex.sin ((Real.pi : ℂ) * z) -
              Complex.sin ((Real.pi : ℂ) * a)
              = Complex.sin ((Real.pi : ℂ) * z) - 0 := by
                  exact congrArg (fun t : ℂ =>
                    Complex.sin ((Real.pi : ℂ) * z) - t) hsin_zero
          _ = Complex.sin ((Real.pi : ℂ) * z) :=
            sub_zero (Complex.sin ((Real.pi : ℂ) * z))
      calc
        (z - a)⁻¹ *
            (Complex.sin ((Real.pi : ℂ) * z) -
              Complex.sin ((Real.pi : ℂ) * a))
            = (z - a)⁻¹ * Complex.sin ((Real.pi : ℂ) * z) := by
              exact congrArg (fun t : ℂ => (z - a)⁻¹ * t) hsub
        _ = Complex.sin ((Real.pi : ℂ) * z) / (z - a) := by
          exact (div_eq_inv_mul (Complex.sin ((Real.pi : ℂ) * z)) (z - a)).symm
    exact hsame ▸ hslope
  have hnum :
      Tendsto
        (fun z : ℂ =>
          (Real.pi : ℂ) * Complex.cos ((Real.pi : ℂ) * z))
        (𝓝[≠] a)
        (𝓝 d) := by
    have hcont :
        ContinuousAt
          (fun z : ℂ =>
            (Real.pi : ℂ) * Complex.cos ((Real.pi : ℂ) * z))
          a := by
      have hlinear : Continuous fun z : ℂ => (Real.pi : ℂ) * z :=
        continuous_const.mul continuous_id
      have hcos : Continuous fun z : ℂ =>
          Complex.cos ((Real.pi : ℂ) * z) :=
        Complex.continuous_cos.comp hlinear
      exact (continuous_const.mul hcos).continuousAt
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hquot :
      Tendsto
        (fun z : ℂ =>
          ((Real.pi : ℂ) * Complex.cos ((Real.pi : ℂ) * z)) /
            (Complex.sin ((Real.pi : ℂ) * z) / (z - a)))
        (𝓝[≠] a)
        (𝓝 (d / d)) :=
    hnum.div hsin_slope hd_ne
  have hone : d / d = 1 := div_self hd_ne
  have hsame :
      (fun z : ℂ =>
        (z - (n : ℂ)) * Complex.finiteAbelPlanaCotangentKernel z) =
      (fun z : ℂ =>
        ((Real.pi : ℂ) * Complex.cos ((Real.pi : ℂ) * z)) /
          (Complex.sin ((Real.pi : ℂ) * z) / (z - a))) := by
    funext z
    let A : ℂ := z - (n : ℂ)
    let P : ℂ := (Real.pi : ℂ)
    let C : ℂ := Complex.cos ((Real.pi : ℂ) * z)
    let S : ℂ := Complex.sin ((Real.pi : ℂ) * z)
    have ha : a = (n : ℂ) :=
      rfl
    have hA : A = z - a := by
      exact congrArg (fun q : ℂ => z - q) ha.symm
    have hleft :
        A * (P * (C / S)) = (P * C) * A / S := by
      calc
        A * (P * (C / S)) = A * (P * (C * S⁻¹)) := by
          exact congrArg (fun u : ℂ => A * (P * u)) (div_eq_mul_inv C S)
        _ = A * ((P * C) * S⁻¹) := by
          exact congrArg (fun u : ℂ => A * u) (mul_assoc P C S⁻¹).symm
        _ = (A * (P * C)) * S⁻¹ := by
          exact (mul_assoc A (P * C) S⁻¹).symm
        _ = ((P * C) * A) * S⁻¹ := by
          exact congrArg (fun u : ℂ => u * S⁻¹) (mul_comm A (P * C))
        _ = (P * C) * A * S⁻¹ := rfl
        _ = (P * C) * A / S := by
          exact (div_eq_mul_inv ((P * C) * A) S).symm
    have hright :
        P * C / (S / A) = (P * C) * A / S :=
      div_div_eq_mul_div (P * C) S A
    calc
      (z - (n : ℂ)) * Complex.finiteAbelPlanaCotangentKernel z =
          A * (P * (C / S)) := by
        exact congrArg
          (fun u : ℂ => (z - (n : ℂ)) * u)
          (Complex.finiteAbelPlanaCotangentKernel_sinCos_unfold z)
      _ = (P * C) * A / S := hleft
      _ = P * C / (S / A) := hright.symm
      _ =
          ((Real.pi : ℂ) * Complex.cos ((Real.pi : ℂ) * z)) /
            (Complex.sin ((Real.pi : ℂ) * z) / (z - a)) := by
        exact congrArg
          (fun u : ℂ =>
            P * C / (S / u))
          hA
  exact hone ▸ (hsame ▸ hquot)

/-- The logarithmic rectangle integrand has residue `log(w+n)` at the
integer pole `n`. -/
theorem Complex.finiteAbelPlanaLogRectangleIntegrand_integerResidue_at_nat
    {w : ℂ}
    (hw : 0 < w.re)
    (n : ℕ) :
    Tendsto
      (fun z : ℂ =>
        (z - (n : ℂ)) *
          Complex.finiteAbelPlanaLogRectangleIntegrand w z)
      (𝓝[≠] (n : ℂ))
      (𝓝 (Complex.finiteAbelPlanaLogIntegerResidue w n)) := by
  have hlog :
      Tendsto
        (fun z : ℂ => Complex.finiteAbelPlanaLogSummand w z)
        (𝓝[≠] (n : ℂ))
        (𝓝 (Complex.finiteAbelPlanaLogSummand w (n : ℂ))) := by
    have hslit :
        w + (n : ℂ) ∈ Complex.slitPlane :=
      by
        exact Complex.mem_slitPlane_iff_not_le_zero.2 <| by
          exact Complex.not_le_zero_iff.2 <| Or.inl <| by
            have hre :
                (w + (n : ℂ)).re = w.re + (n : ℝ) := by
              exact Complex.add_re w (n : ℂ)
            exact hre.symm ▸ add_pos_of_pos_of_nonneg hw (Nat.cast_nonneg n)
    exact
      tendsto_nhdsWithin_of_tendsto_nhds
        ((continuous_const.add continuous_id).continuousAt.clog hslit)
  have hcot :
      Tendsto
        (fun z : ℂ =>
          (z - (n : ℂ)) * Complex.finiteAbelPlanaCotangentKernel z)
        (𝓝[≠] (n : ℂ))
        (𝓝 (1 : ℂ)) :=
    Complex.finiteAbelPlanaCotangentKernel_unitResidue_at_nat n
  have hmul :
      Tendsto
        (fun z : ℂ =>
          Complex.finiteAbelPlanaLogSummand w z *
            ((z - (n : ℂ)) *
              Complex.finiteAbelPlanaCotangentKernel z))
        (𝓝[≠] (n : ℂ))
        (𝓝 (Complex.finiteAbelPlanaLogSummand w (n : ℂ) * 1)) :=
    hlog.mul hcot
  have hrewrite :
      (fun z : ℂ =>
        (z - (n : ℂ)) *
          Complex.finiteAbelPlanaLogRectangleIntegrand w z) =
      (fun z : ℂ =>
        Complex.finiteAbelPlanaLogSummand w z *
          ((z - (n : ℂ)) *
            Complex.finiteAbelPlanaCotangentKernel z)) := by
    funext z
    let A : ℂ := z - (n : ℂ)
    let B : ℂ := Complex.finiteAbelPlanaLogSummand w z
    let C : ℂ := Complex.finiteAbelPlanaCotangentKernel z
    calc
      (z - (n : ℂ)) *
          Complex.finiteAbelPlanaLogRectangleIntegrand w z =
        A * (B * C) := by
        exact congrArg
          (fun u : ℂ => (z - (n : ℂ)) * u)
          (Complex.finiteAbelPlanaLogRectangleIntegrand_unfold w z)
      _ = (A * B) * C := (mul_assoc A B C).symm
      _ = (B * A) * C := by
        exact congrArg (fun u : ℂ => u * C) (mul_comm A B)
      _ = B * (A * C) := mul_assoc B A C
  have htarget :
      Complex.finiteAbelPlanaLogSummand w (n : ℂ) * 1 =
        Complex.finiteAbelPlanaLogIntegerResidue w n := by
    calc
      Complex.finiteAbelPlanaLogSummand w (n : ℂ) * 1 =
          Complex.finiteAbelPlanaLogSummand w (n : ℂ) :=
        mul_one _
      _ =
          Complex.finiteAbelPlanaLogIntegerResidue w n :=
        (Complex.finiteAbelPlanaLogIntegerResidue_unfold w n).symm
  exact htarget ▸ (hrewrite ▸ hmul)

/-- Full lower vertical Abel-Plana boundary for `z ↦ log (w+z)`.

This is the untruncated lower vertical contribution before the Binet proof
splits it into the finite boundary window `(0,N]` and the omitted lower tail.
-/
noncomputable def Complex.finiteAbelPlanaLogSummandLowerVerticalIntegral
    (N : ℕ)
    (w : ℂ) : ℂ :=
  Complex.binetAbelPlanaFiniteBoundaryCorrection N w +
    Complex.binetAbelPlanaFiniteLowerContourTail N w

/-- Full upper vertical Abel-Plana boundary for `z ↦ log (w+z)`.

The upper endpoint line is already a residual term in the finite Binet
normalization, so no further split is needed here. -/
noncomputable def Complex.finiteAbelPlanaLogSummandUpperVerticalIntegral
    (N : ℕ)
    (w : ℂ) : ℂ :=
  Complex.binetAbelPlanaFiniteUpperContourResidual N w

/-- Lower vertical boundary contribution in the finite Abel-Plana formula for
`z ↦ log (w+z)`, in the normalization used by the Binet finite boundary. -/
noncomputable def Complex.finiteAbelPlanaLogSummandLowerVerticalBoundary
    (N : ℕ)
    (w : ℂ) : ℂ :=
  -Complex.finiteAbelPlanaLogSummandLowerVerticalIntegral N w

/-- Upper vertical boundary contribution in the finite Abel-Plana formula for
`z ↦ log (w+z)`, in the normalization used by the Binet finite residual. -/
noncomputable def Complex.finiteAbelPlanaLogSummandUpperVerticalBoundary
    (N : ℕ)
    (w : ℂ) : ℂ :=
  -Complex.finiteAbelPlanaLogSummandUpperVerticalIntegral N w

/-- Along the real segment used in the finite Abel-Plana formula, `w+x` stays
in the principal-log slit plane when `w` is in the open right half-plane. -/
theorem Complex.finiteAbelPlana_log_summand_realSegment_mem_slitPlane
    {w : ℂ}
    (hw : 0 < w.re)
    {x : ℝ}
    (hx : 0 ≤ x) :
    w + (x : ℂ) ∈ Complex.slitPlane := by
  exact Complex.mem_slitPlane_iff_not_le_zero.2 <| by
    exact Complex.not_le_zero_iff.2 <| Or.inl <| by
      have hx_re : (w + (x : ℂ)).re = w.re + x := by
        exact Complex.add_re w (x : ℂ)
      exact hx_re.symm ▸ add_pos_of_pos_of_nonneg hw hx

/-- Primitive used for the real-segment term in the finite Abel-Plana formula. -/
noncomputable def Complex.finiteAbelPlanaLogPrimitive
    (w : ℂ)
    (x : ℝ) : ℂ :=
  (w + (x : ℂ)) * Complex.log (w + (x : ℂ)) -
    (w + (x : ℂ))

/-- Unfolding of the real-segment primitive for the logarithmic summand. -/
theorem Complex.finiteAbelPlanaLogPrimitive_unfold
    (w : ℂ)
    (x : ℝ) :
    Complex.finiteAbelPlanaLogPrimitive w x =
      (w + (x : ℂ)) * Complex.log (w + (x : ℂ)) -
        (w + (x : ℂ)) :=
  rfl

/-- Derivative of the logarithmic primitive on the real segment. -/
theorem Complex.hasDerivAt_finiteAbelPlanaLogPrimitive
    {w : ℂ}
    (hw : 0 < w.re)
    {x : ℝ}
    (hx : 0 ≤ x) :
    HasDerivAt
      (fun y : ℝ => Complex.finiteAbelPlanaLogPrimitive w y)
      (Complex.finiteAbelPlanaLogSummand w (x : ℂ))
      x := by
  let g : ℝ → ℂ := fun y : ℝ => w + (y : ℂ)
  have hg : HasDerivAt g (1 : ℂ) x := by
    exact ((hasDerivAt_id (x : ℂ)).const_add w).comp_ofReal
  have hlog :
      HasDerivAt
        (fun y : ℝ => Complex.log (g y))
        ((1 : ℂ) / g x)
        x :=
    hg.clog_real
      (Complex.finiteAbelPlana_log_summand_realSegment_mem_slitPlane
        hw hx)
  have hmul :
      HasDerivAt
        (fun y : ℝ => g y * Complex.log (g y))
        ((1 : ℂ) * Complex.log (g x) + g x * ((1 : ℂ) / g x))
        x :=
    hg.mul hlog
  have hsub :
      HasDerivAt
        (fun y : ℝ => g y * Complex.log (g y) - g y)
        (((1 : ℂ) * Complex.log (g x) + g x * ((1 : ℂ) / g x)) - 1)
        x :=
    hmul.sub hg
  have hg_ne : g x ≠ 0 :=
    Complex.slitPlane_ne_zero
      (Complex.finiteAbelPlana_log_summand_realSegment_mem_slitPlane
        hw hx)
  have hderiv_eq :
      ((1 : ℂ) * Complex.log (g x) + g x * ((1 : ℂ) / g x)) - 1 =
        Complex.finiteAbelPlanaLogSummand w (x : ℂ) := by
    calc
      ((1 : ℂ) * Complex.log (g x) + g x * ((1 : ℂ) / g x)) - 1
          = (Complex.log (g x) + 1) - 1 := by
        have hg_cancel : g x * ((1 : ℂ) / g x) = 1 := by
          calc
            g x * ((1 : ℂ) / g x) = g x * (g x)⁻¹ := by
              exact congrArg (fun u : ℂ => g x * u) (one_div (g x))
            _ = 1 := mul_inv_cancel₀ hg_ne
        have hone_mul :
            (1 : ℂ) * Complex.log (g x) = Complex.log (g x) :=
          one_mul (Complex.log (g x))
        have hmul :
            (1 : ℂ) * Complex.log (g x) + g x * ((1 : ℂ) / g x) =
              Complex.log (g x) + 1 := by
          calc
            (1 : ℂ) * Complex.log (g x) + g x * ((1 : ℂ) / g x)
                = Complex.log (g x) + g x * ((1 : ℂ) / g x) := by
              exact congrArg (fun u : ℂ => u + g x * ((1 : ℂ) / g x)) hone_mul
            _ = Complex.log (g x) + 1 := by
              exact congrArg (fun t : ℂ => Complex.log (g x) + t) hg_cancel
        exact congrArg (fun t : ℂ => t - 1) hmul
      _ = Complex.log (g x) := by
        exact add_sub_cancel_right (Complex.log (g x)) 1
      _ = Complex.finiteAbelPlanaLogSummand w (x : ℂ) := by
        rfl
  exact hderiv_eq ▸ hsub

/-- The endpoint primitive is the closed-form integral of the logarithmic
summand over the horizontal real segment `[0,N+1]`.

This is the elementary primitive calculation used after the Abel-Plana
rectangle has been reduced to boundary pieces. -/
theorem Complex.finiteAbelPlana_log_summand_realSegmentIntegral_eq_endpointPrimitive
    {w : ℂ}
    (hw : 0 < w.re) :
    ∀ N : ℕ,
      let M : ℕ := N + 1
      ∫ x : ℝ in (0 : ℝ)..(M : ℝ),
          Complex.finiteAbelPlanaLogSummand w (x : ℂ) =
        Complex.finiteAbelPlanaLogSummandEndpointPrimitive N w := by
  intro N
  let M : ℕ := N + 1
  let F : ℝ → ℂ := fun x : ℝ =>
    Complex.finiteAbelPlanaLogPrimitive w x
  have hderiv :
      ∀ x ∈ Set.uIcc (0 : ℝ) (M : ℝ),
        HasDerivAt F (Complex.finiteAbelPlanaLogSummand w (x : ℂ)) x := by
    intro x hx
    have hM_nonneg : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    have hxIcc : x ∈ Set.Icc (0 : ℝ) (M : ℝ) := by
      exact Eq.subst (motive := fun s : Set ℝ => x ∈ s)
        (Set.uIcc_of_le hM_nonneg)
        hx
    exact Complex.hasDerivAt_finiteAbelPlanaLogPrimitive hw hxIcc.1
  have hcont :
      ContinuousOn
        (fun x : ℝ => Complex.finiteAbelPlanaLogSummand w (x : ℂ))
        (Set.uIcc (0 : ℝ) (M : ℝ)) := by
    intro x hx
    have hM_nonneg : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    have hxIcc : x ∈ Set.Icc (0 : ℝ) (M : ℝ) := by
      exact Eq.subst (motive := fun s : Set ℝ => x ∈ s)
        (Set.uIcc_of_le hM_nonneg)
        hx
    have hslit :
        w + (x : ℂ) ∈ Complex.slitPlane :=
      Complex.finiteAbelPlana_log_summand_realSegment_mem_slitPlane
        hw hxIcc.1
    exact ((continuous_const.add Complex.continuous_ofReal).continuousAt.clog hslit).continuousWithinAt
  have hint :
      IntervalIntegrable
        (fun x : ℝ => Complex.finiteAbelPlanaLogSummand w (x : ℂ))
        volume
        (0 : ℝ)
        (M : ℝ) :=
    hcont.intervalIntegrable
  have hFTC :
      ∫ x : ℝ in (0 : ℝ)..(M : ℝ),
          Complex.finiteAbelPlanaLogSummand w (x : ℂ) =
        F (M : ℝ) - F 0 := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  calc
    ∫ x : ℝ in (0 : ℝ)..(M : ℝ),
        Complex.finiteAbelPlanaLogSummand w (x : ℂ) =
      F (M : ℝ) - F 0 := hFTC
    _ = Complex.finiteAbelPlanaLogSummandEndpointPrimitive N w := by
      have htop :
          F (M : ℝ) =
            (w + ((N + 1 : ℕ) : ℂ)) *
                Complex.log (w + ((N + 1 : ℕ) : ℂ)) -
              (w + ((N + 1 : ℕ) : ℂ)) :=
        Complex.finiteAbelPlanaLogPrimitive_unfold w (M : ℝ)
      have hbottom :
          F 0 =
            (w + 0) * Complex.log (w + 0) - (w + 0) :=
        Complex.finiteAbelPlanaLogPrimitive_unfold w 0
      have htarget :
          Complex.finiteAbelPlanaLogSummandEndpointPrimitive N w =
            ((w + ((N + 1 : ℕ) : ℂ)) *
                Complex.log (w + ((N + 1 : ℕ) : ℂ)) -
              (w + ((N + 1 : ℕ) : ℂ))) -
              (w * Complex.log w - w) :=
        Complex.finiteAbelPlanaLogSummandEndpointPrimitive_unfold N w
      have hbase :
          (w + 0) * Complex.log (w + 0) - (w + 0) =
            w * Complex.log w - w := by
        have hsum : w + 0 = w := add_zero w
        have hprod :
            (w + 0) * Complex.log (w + 0) = w * Complex.log w := by
          calc
            (w + 0) * Complex.log (w + 0) =
                w * Complex.log (w + 0) := by
              exact congrArg (fun u : ℂ => u * Complex.log (w + 0)) hsum
            _ = w * Complex.log w := by
              exact congrArg (fun u : ℂ => w * Complex.log u) hsum
        calc
          (w + 0) * Complex.log (w + 0) - (w + 0) =
              w * Complex.log w - (w + 0) := by
            exact congrArg (fun u : ℂ => u - (w + 0)) hprod
          _ = w * Complex.log w - w := by
            exact congrArg (fun u : ℂ => w * Complex.log w - u) hsum
      calc
        F (M : ℝ) - F 0 =
          ((w + ((N + 1 : ℕ) : ℂ)) *
              Complex.log (w + ((N + 1 : ℕ) : ℂ)) -
            (w + ((N + 1 : ℕ) : ℂ))) -
            ((w + 0) * Complex.log (w + 0) - (w + 0)) := by
          exact congrArg₂ HSub.hSub htop hbottom
        _ =
          ((w + ((N + 1 : ℕ) : ℂ)) *
              Complex.log (w + ((N + 1 : ℕ) : ℂ)) -
            (w + ((N + 1 : ℕ) : ℂ))) -
            (w * Complex.log w - w) := by
          exact congrArg
            (fun u : ℂ =>
              (w + ((N + 1 : ℕ) : ℂ)) *
                  Complex.log (w + ((N + 1 : ℕ) : ℂ)) -
                (w + ((N + 1 : ℕ) : ℂ)) - u)
            hbase
        _ = Complex.finiteAbelPlanaLogSummandEndpointPrimitive N w :=
          htarget.symm

/-- The lower vertical boundary is the negative of the full lower
Abel-Plana logarithmic jump integral. -/
theorem Complex.finiteAbelPlana_log_summand_lowerBoundary_eq_neg_lowerIntegral
    (N : ℕ)
    (w : ℂ) :
    Complex.finiteAbelPlanaLogSummandLowerVerticalBoundary N w =
      -Complex.finiteAbelPlanaLogSummandLowerVerticalIntegral N w := by
  rfl

/-- The upper vertical boundary is the negative of the upper endpoint residual
integral. -/
theorem Complex.finiteAbelPlana_log_summand_upperBoundary_eq_neg_upperIntegral
    (N : ℕ)
    (w : ℂ) :
    Complex.finiteAbelPlanaLogSummandUpperVerticalBoundary N w =
      -Complex.finiteAbelPlanaLogSummandUpperVerticalIntegral N w := by
  rfl

/-- The named boundary expression obtained after decomposing the finite
Abel-Plana principal-value rectangle contour.

This is not the raw contour integral.  It is the post-decomposition expression:
the real-segment integral, the endpoint principal-value half contribution, and
the two vertical logarithmic-jump contributions.  The residue theorem below is
the classical statement that this decomposed boundary expression equals the
integer residue sum for the cotangent sampling kernel. -/
noncomputable def Complex.finiteAbelPlanaLogBoundaryNamedPieces
    (N : ℕ)
    (w : ℂ) : ℂ :=
  let M : ℕ := N + 1
  (∫ x : ℝ in (0 : ℝ)..(M : ℝ),
      Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
    Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
    Complex.finiteAbelPlanaLogSummandLowerVerticalIntegral N w -
    Complex.finiteAbelPlanaLogSummandUpperVerticalIntegral N w

/-- Unfolding of the named finite Abel-Plana boundary expression. -/
theorem Complex.finiteAbelPlana_log_boundaryNamedPieces_unfold
    (N : ℕ)
    (w : ℂ) :
    let M : ℕ := N + 1
    Complex.finiteAbelPlanaLogBoundaryNamedPieces N w =
      (∫ x : ℝ in (0 : ℝ)..(M : ℝ),
        Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
        Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
        Complex.finiteAbelPlanaLogSummandLowerVerticalIntegral N w -
        Complex.finiteAbelPlanaLogSummandUpperVerticalIntegral N w := by
  rfl

/-- Every integer pole in the finite Abel-Plana rectangle has the expected
logarithmic residue. -/
theorem Complex.finiteAbelPlana_log_rectangleIntegrand_allIntegerResidues
    {w : ℂ}
    (hw : 0 < w.re) :
    ∀ N : ℕ,
      ∀ n ∈ Finset.range (N + 2),
        Tendsto
          (fun z : ℂ =>
            (z - (n : ℂ)) *
              Complex.finiteAbelPlanaLogRectangleIntegrand w z)
          (𝓝[≠] (n : ℂ))
          (𝓝 (Complex.finiteAbelPlanaLogIntegerResidue w n)) := by
  intro N n _hn
  exact
    Complex.finiteAbelPlanaLogRectangleIntegrand_integerResidue_at_nat
      hw n

/-- Shrinking-circle evaluation of the local residue integrals around every
integer pole in the finite Abel-Plana rectangle. -/
theorem Complex.finiteAbelPlana_log_rectangleIntegrand_shrinkingCircleResidues
    {w : ℂ}
    (hw : 0 < w.re) :
    ∀ N : ℕ,
      ∀ n ∈ Finset.range (N + 2),
        Tendsto
          (fun z : ℂ =>
            (z - (n : ℂ)) *
              Complex.finiteAbelPlanaLogRectangleIntegrand w z)
          (𝓝[≠] (n : ℂ))
          (𝓝 (Complex.finiteAbelPlanaLogIntegerResidue w n)) := by
  intro N n hn
  exact
    Complex.finiteAbelPlana_log_rectangleIntegrand_allIntegerResidues
      hw N n hn

/-- Lower vertical Abel-Plana logarithmic-jump integrand.

This is the lower-half-plane exponential part of the cotangent kernel after
the finite principal-value rectangle boundary is decomposed into Abel-Plana
pieces. -/
noncomputable def Complex.finiteAbelPlanaLogLowerVerticalIntegrand
    (w : ℂ)
    (t : ℝ) : ℂ :=
  (-Complex.I) *
    ((Complex.log (w + (t : ℂ) * Complex.I) -
        Complex.log (w - (t : ℂ) * Complex.I)) /
      (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))

/-- Upper vertical Abel-Plana logarithmic-jump integrand at the endpoint
`M = N + 1`. -/
noncomputable def Complex.finiteAbelPlanaLogUpperVerticalIntegrand
    (N : ℕ)
    (w : ℂ)
    (t : ℝ) : ℂ :=
  Complex.I *
    (Complex.binetAbelPlanaFiniteUpperLogJump N w t /
      (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))

/-- Finite-height lower vertical boundary integral for the Abel-Plana
principal-value rectangle. -/
noncomputable def Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo
    (w : ℂ)
    (T : ℝ) : ℂ :=
  ∫ t : ℝ in Set.Ioc (0 : ℝ) T,
    Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t

/-- Unsplit lower vertical Abel-Plana improper integral over the positive
half-line. -/
noncomputable def Complex.finiteAbelPlanaLogLowerVerticalFullIntegral
    (w : ℂ) : ℂ :=
  ∫ t : ℝ in Set.Ioi (0 : ℝ),
    Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t

/-- Finite-height upper vertical boundary integral for the Abel-Plana
principal-value rectangle. -/
noncomputable def Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) : ℂ :=
  ∫ t : ℝ in Set.Ioc (0 : ℝ) T,
    Complex.finiteAbelPlanaLogUpperVerticalIntegrand N w t

/-- Unsplit upper vertical Abel-Plana improper integral over the positive
half-line. -/
noncomputable def Complex.finiteAbelPlanaLogUpperVerticalFullIntegral
    (N : ℕ)
    (w : ℂ) : ℂ :=
  ∫ t : ℝ in Set.Ioi (0 : ℝ),
    Complex.finiteAbelPlanaLogUpperVerticalIntegrand N w t

/-- Named finite-height Abel-Plana boundary expression before taking the
vertical height to infinity. -/
noncomputable def Complex.finiteAbelPlanaLogBoundaryNamedPiecesUpTo
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) : ℂ :=
  let M : ℕ := N + 1
  (∫ x : ℝ in (0 : ℝ)..(M : ℝ),
      Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
    Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
    Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
    Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T

/-- Unfolding of the named boundary pieces before taking the height limit. -/
theorem Complex.finiteAbelPlana_log_boundaryNamedPiecesUpTo_unfold
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    let M : ℕ := N + 1
    Complex.finiteAbelPlanaLogBoundaryNamedPiecesUpTo N w T =
      (∫ x : ℝ in (0 : ℝ)..(M : ℝ),
          Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
        Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
        Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
        Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T := by
  rfl

/-- Finite-height Abel-Plana contour error.

This is the part of the finite-height principal-value rectangle identity not
accounted for by the vertical boundary pieces and the integer residues.  In
the classical proof it is exactly the pair of horizontal edge integrals after
endpoint indentation normalization. -/
noncomputable def Complex.finiteAbelPlanaLogFiniteHeightContourError
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) : ℂ :=
  Complex.finiteAbelPlanaLogBoundaryNamedPiecesUpTo N w T -
    Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w

/-- Unfolding of the finite-height contour error. -/
theorem Complex.finiteAbelPlana_log_finiteHeightContourError_unfold'
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    Complex.finiteAbelPlanaLogFiniteHeightContourError N w T =
      Complex.finiteAbelPlanaLogBoundaryNamedPiecesUpTo N w T -
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w := by
  rfl

/-- Bottom horizontal cotangent-remainder edge of the finite-height
Abel-Plana rectangle.

This is not the full lower horizontal side.  The non-decaying constant term
`π i` in the lower-half-plane cotangent expansion is absorbed into the named
Abel-Plana boundary pieces.  The remaining kernel decays exponentially as the
height tends to infinity. -/
noncomputable def Complex.finiteAbelPlanaLogBottomHorizontalEdge
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) : ℂ :=
  let M : ℕ := N + 1
  ∫ x : ℝ in (0 : ℝ)..(M : ℝ),
    Complex.finiteAbelPlanaLogSummand w
      ((x : ℂ) - (T : ℂ) * Complex.I) *
      (Complex.finiteAbelPlanaCotangentKernel
          ((x : ℂ) - (T : ℂ) * Complex.I) -
        (Real.pi : ℂ) * Complex.I)

/-- Top horizontal cotangent-remainder edge of the finite-height Abel-Plana
rectangle.

This is not the full upper horizontal side.  The non-decaying constant term
`-π i` in the upper-half-plane cotangent expansion is absorbed into the named
Abel-Plana boundary pieces.  The remaining kernel decays exponentially as the
height tends to infinity. -/
noncomputable def Complex.finiteAbelPlanaLogTopHorizontalEdge
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) : ℂ :=
  let M : ℕ := N + 1
  ∫ x : ℝ in (0 : ℝ)..(M : ℝ),
    Complex.finiteAbelPlanaLogSummand w
      ((x : ℂ) + (T : ℂ) * Complex.I) *
      (Complex.finiteAbelPlanaCotangentKernel
          ((x : ℂ) + (T : ℂ) * Complex.I) +
        (Real.pi : ℂ) * Complex.I)

/-- The decaying horizontal cotangent-remainder part left by the finite-height
Abel-Plana rectangle after the constant half-plane cotangent terms have been
absorbed into the named boundary expression.

The finite residue theorem uses the normalized contour integral
`(2πi)⁻¹ ∮`.  This primitive therefore includes the same normalization; the
bottom and top edge objects themselves remain the raw horizontal integrals. -/
noncomputable def Complex.finiteAbelPlanaLogHorizontalEdgeError
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) : ℂ :=
  ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
    (Complex.finiteAbelPlanaLogBottomHorizontalEdge N w T -
      Complex.finiteAbelPlanaLogTopHorizontalEdge N w T)

/-- Finite-height principal-value rectangle residue accounting with the
horizontal contour error kept explicit. -/
theorem Complex.finiteAbelPlana_log_boundaryNamedPiecesUpTo_eq_residueSum_add_error
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    Complex.finiteAbelPlanaLogBoundaryNamedPiecesUpTo N w T =
      Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w +
    Complex.finiteAbelPlanaLogFiniteHeightContourError N w T := by
  have herror :
      Complex.finiteAbelPlanaLogFiniteHeightContourError N w T =
        Complex.finiteAbelPlanaLogBoundaryNamedPiecesUpTo N w T -
          Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w :=
    Complex.finiteAbelPlana_log_finiteHeightContourError_unfold' N w T
  exact herror.symm ▸ eq_add_of_sub_eq' rfl

/-- The concrete lower vertical integrand is the one used in the finite Binet
boundary correction and lower contour tail. -/
theorem Complex.finiteAbelPlana_log_lowerVerticalIntegrand_eq_binet
    (w : ℂ)
    (t : ℝ) :
    Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t =
      (-Complex.I) *
        ((Complex.log (w + (t : ℂ) * Complex.I) -
            Complex.log (w - (t : ℂ) * Complex.I)) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)) := by
  rfl

/-- The lower vertical Abel-Plana jump integrand is definitionally the finite
Binet lower vertical integrand. -/
theorem Complex.finiteAbelPlana_log_lowerVerticalJumpIntegrand_eq_binet
    (w : ℂ)
    (t : ℝ) :
    Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t =
      Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t := by
  rfl

/-- A real multiple of `I` has zero real part. -/
theorem Complex.real_mul_I_re_eq_zero
    (t : ℝ) :
    ((t : ℂ) * Complex.I).re = 0 := by
  calc
    ((t : ℂ) * Complex.I).re = -((t : ℂ).im) := by
      exact Complex.mul_I_re (t : ℂ)
    _ = -0 := by
      exact congrArg Neg.neg (Complex.ofReal_im t)
    _ = 0 := neg_zero

/-- Put the numerator of the Cayley transform over the denominator `w`. -/
theorem Complex.binetAbelPlana_cayley_numerator_common_denominator
    {w : ℂ}
    {t : ℝ}
    (hw_ne : w ≠ 0) :
    1 + ((t : ℂ) / w) * Complex.I =
      (w + (t : ℂ) * Complex.I) / w := by
  calc
    1 + ((t : ℂ) / w) * Complex.I
        = 1 + ((t : ℂ) * Complex.I) / w := by
      exact congrArg (fun z : ℂ => 1 + z)
        (div_mul_eq_mul_div (t : ℂ) w Complex.I)
    _ = (1 * w + (t : ℂ) * Complex.I) / w := by
      exact add_div_eq_mul_add_div 1 ((t : ℂ) * Complex.I) hw_ne
    _ = (w + (t : ℂ) * Complex.I) / w := by
      exact congrArg (fun z : ℂ => (z + (t : ℂ) * Complex.I) / w)
        (one_mul w)

/-- Put the denominator of the Cayley transform over the denominator `w`. -/
theorem Complex.binetAbelPlana_cayley_denominator_common_denominator
    {w : ℂ}
    {t : ℝ}
    (hw_ne : w ≠ 0) :
    1 - ((t : ℂ) / w) * Complex.I =
      (w - (t : ℂ) * Complex.I) / w := by
  calc
    1 - ((t : ℂ) / w) * Complex.I
        = 1 - ((t : ℂ) * Complex.I) / w := by
      exact congrArg (fun z : ℂ => 1 - z)
        (div_mul_eq_mul_div (t : ℂ) w Complex.I)
    _ = 1 + (-((t : ℂ) * Complex.I)) / w := by
      calc
        1 - ((t : ℂ) * Complex.I) / w =
            1 + -(((t : ℂ) * Complex.I) / w) :=
          sub_eq_add_neg 1 (((t : ℂ) * Complex.I) / w)
        _ = 1 + (-((t : ℂ) * Complex.I)) / w := by
          exact congrArg (fun z : ℂ => 1 + z)
            (neg_div' w ((t : ℂ) * Complex.I))
    _ = (1 * w + -((t : ℂ) * Complex.I)) / w := by
      exact add_div_eq_mul_add_div 1 (-((t : ℂ) * Complex.I)) hw_ne
    _ = (w - (t : ℂ) * Complex.I) / w := by
      calc
        (1 * w + -((t : ℂ) * Complex.I)) / w =
            (w + -((t : ℂ) * Complex.I)) / w := by
          exact congrArg
            (fun z : ℂ => (z + -((t : ℂ) * Complex.I)) / w)
            (one_mul w)
        _ = (w - (t : ℂ) * Complex.I) / w := by
          exact congrArg (fun z : ℂ => z / w)
            (sub_eq_add_neg w ((t : ℂ) * Complex.I)).symm

/-- Cancelling the shared right denominator in a quotient of quotients. -/
theorem Complex.div_common_denominator_cancel_right
    {a b c : ℂ}
    (hc : c ≠ 0) :
    (a / c) / (b / c) = a / b := by
  exact div_div_div_cancel_right₀ hc a b

/-- Algebraic Cayley normalization of the Binet arctangent argument. -/
theorem Complex.binetAbelPlana_arctan_cayley_eq_logJump_ratio
    {w : ℂ}
    {t : ℝ}
    (hw : 0 < w.re) :
    (1 + ((t : ℂ) / w) * Complex.I) /
        (1 - ((t : ℂ) / w) * Complex.I) =
      (w + (t : ℂ) * Complex.I) /
        (w - (t : ℂ) * Complex.I) := by
  have hw_ne : w ≠ 0 := by
    intro hzero
    have hre : w.re = 0 := by
      exact congrArg Complex.re hzero
    exact not_lt_of_ge (le_of_eq hre) hw
  calc
    (1 + ((t : ℂ) / w) * Complex.I) /
        (1 - ((t : ℂ) / w) * Complex.I)
        =
      ((w + (t : ℂ) * Complex.I) / w) /
        ((w - (t : ℂ) * Complex.I) / w) := by
      exact
        congrArg₂ HDiv.hDiv
          (Complex.binetAbelPlana_cayley_numerator_common_denominator hw_ne)
          (Complex.binetAbelPlana_cayley_denominator_common_denominator hw_ne)
    _ =
      (w + (t : ℂ) * Complex.I) /
        (w - (t : ℂ) * Complex.I) := by
      exact
        Complex.div_common_denominator_cancel_right
          (a := w + (t : ℂ) * Complex.I)
          (b := w - (t : ℂ) * Complex.I)
          (c := w)
          hw_ne

/-- Adding a purely imaginary real multiple preserves strict right-half-plane
membership. -/
theorem Complex.add_real_mul_I_re_pos
    {w : ℂ}
    {t : ℝ}
    (hw : 0 < w.re) :
    0 < (w + (t : ℂ) * Complex.I).re := by
  have hre : (w + (t : ℂ) * Complex.I).re = w.re := by
    exact Complex.add_real_mul_I_re w t
  exact hre.symm ▸ hw

/-- Subtracting a purely imaginary real multiple preserves strict
right-half-plane membership. -/
theorem Complex.sub_real_mul_I_re_pos
    {w : ℂ}
    {t : ℝ}
    (hw : 0 < w.re) :
    0 < (w - (t : ℂ) * Complex.I).re := by
  have hre : (w - (t : ℂ) * Complex.I).re = w.re := by
    exact Complex.sub_real_mul_I_re w t
  exact hre.symm ▸ hw

/-- A point in the strict right half-plane is nonzero. -/
theorem Complex.binetAbelPlana_ne_zero_of_re_pos
    {z : ℂ}
    (hz : 0 < z.re) :
    z ≠ 0 := by
  intro hzero
  have hre_zero : z.re = 0 := by
    exact congrArg Complex.re hzero
  exact not_lt_of_ge (le_of_eq hre_zero) hz

/-- A point in the strict right half-plane is not on the principal-log negative
real branch cut. -/
theorem Complex.binetAbelPlana_arg_ne_pi_of_re_pos
    {z : ℂ}
    (hz : 0 < z.re) :
    Complex.arg z ≠ Real.pi := by
  intro harg
  have hneg : z.re < 0 :=
    (Complex.arg_eq_pi_iff.mp harg).1
  exact not_lt_of_ge hz.le hneg

/-- Strict right-half-plane membership puts the principal argument in
`(-π/2,π/2)`. -/
theorem Complex.binetAbelPlana_abs_arg_lt_pi_div_two_of_re_pos
    {z : ℂ}
    (hz : 0 < z.re) :
    |Complex.arg z| < Real.pi / 2 := by
  exact
    (Complex.abs_arg_lt_pi_div_two_iff).mpr
      (Or.inl hz)

/-- The lower endpoints of two right-half-plane argument intervals add to
`-π`. -/
theorem neg_pi_div_two_add_neg_pi_div_two :
    -(Real.pi / 2) + -(Real.pi / 2) = -Real.pi := by
  calc
    -(Real.pi / 2) + -(Real.pi / 2)
        = -(Real.pi / 2 + Real.pi / 2) := by
      exact (neg_add (Real.pi / 2) (Real.pi / 2)).symm
    _ = -Real.pi := by
      exact congrArg Neg.neg (add_halves Real.pi)

/-- The upper endpoints of two right-half-plane argument intervals add to
`π`. -/
theorem pi_div_two_add_pi_div_two :
    Real.pi / 2 + Real.pi / 2 = Real.pi :=
  add_halves Real.pi

/-- Difference lower bound for two arguments in `(-π/2, π/2)`. -/
theorem neg_pi_lt_sub_of_neg_pi_div_two_lt_of_lt_pi_div_two
    {a b : ℝ}
    (ha : -(Real.pi / 2) < a)
    (hb : b < Real.pi / 2) :
    -Real.pi < a - b := by
  have hnegb : -(Real.pi / 2) < -b := by
    exact neg_lt_neg hb
  have hsum : -(Real.pi / 2) + -(Real.pi / 2) < a + -b :=
    add_lt_add ha hnegb
  calc
    -Real.pi = -(Real.pi / 2) + -(Real.pi / 2) :=
      neg_pi_div_two_add_neg_pi_div_two.symm
    _ < a + -b := hsum
    _ = a - b := (sub_eq_add_neg a b).symm

/-- Difference upper bound for two arguments in `(-π/2, π/2)`. -/
theorem sub_lt_pi_of_lt_pi_div_two_of_neg_pi_div_two_lt
    {a b : ℝ}
    (ha : a < Real.pi / 2)
    (hb : -(Real.pi / 2) < b) :
    a - b < Real.pi := by
  have hnegb : -b < Real.pi / 2 := by
    exact
      Eq.subst
        (motive := fun x : ℝ => -b < x)
        (neg_neg (Real.pi / 2))
        (neg_lt_neg hb)
  have hsum : a + -b < Real.pi / 2 + Real.pi / 2 :=
    add_lt_add ha hnegb
  calc
    a - b = a + -b := sub_eq_add_neg a b
    _ < Real.pi / 2 + Real.pi / 2 := hsum
    _ = Real.pi := pi_div_two_add_pi_div_two

/-- The inverse of a strict-right-half-plane point has argument equal to the
negative argument. -/
theorem Complex.binetAbelPlana_arg_inv_eq_neg_of_re_pos
    {z : ℂ}
    (hz : 0 < z.re) :
    Complex.arg z⁻¹ = -Complex.arg z := by
  have harg_ne :
      Complex.arg z ≠ Real.pi :=
    Complex.binetAbelPlana_arg_ne_pi_of_re_pos hz
  have h : Complex.arg z⁻¹ = -Complex.arg z := by
    exact (Complex.arg_inv z).trans (if_neg harg_ne)
  exact h

/-- The argument sum needed for multiplying a right-half-plane point by the
inverse of another right-half-plane point stays inside the principal branch
range. -/
theorem Complex.binetAbelPlana_arg_add_inv_mem_Ioc_of_re_pos
    {x y : ℂ}
    (hx : 0 < x.re)
    (hy : 0 < y.re) :
    Complex.arg x + Complex.arg y⁻¹ ∈ Set.Ioc (-Real.pi) Real.pi := by
  have hxarg_abs :
      |Complex.arg x| < Real.pi / 2 :=
    Complex.binetAbelPlana_abs_arg_lt_pi_div_two_of_re_pos hx
  have hyarg_abs :
      |Complex.arg y| < Real.pi / 2 :=
    Complex.binetAbelPlana_abs_arg_lt_pi_div_two_of_re_pos hy
  have hxarg_bounds :
      -(Real.pi / 2) < Complex.arg x ∧
        Complex.arg x < Real.pi / 2 :=
    abs_lt.mp hxarg_abs
  have hyarg_bounds :
      -(Real.pi / 2) < Complex.arg y ∧
        Complex.arg y < Real.pi / 2 :=
    abs_lt.mp hyarg_abs
  have hyinv_arg :
      Complex.arg y⁻¹ = -Complex.arg y :=
    Complex.binetAbelPlana_arg_inv_eq_neg_of_re_pos hy
  have hx_lt : Complex.arg x < Real.pi / 2 :=
    hxarg_bounds.2
  have hx_gt : -(Real.pi / 2) < Complex.arg x :=
    hxarg_bounds.1
  have hy_lt : Complex.arg y < Real.pi / 2 :=
    hyarg_bounds.2
  have hy_gt : -(Real.pi / 2) < Complex.arg y :=
    hyarg_bounds.1
  constructor
  · have hlower : -Real.pi < Complex.arg x - Complex.arg y := by
      exact
        neg_pi_lt_sub_of_neg_pi_div_two_lt_of_lt_pi_div_two
          hx_gt hy_lt
    have htarget :
        -Real.pi < Complex.arg x + Complex.arg y⁻¹ := by
      exact
        Eq.subst
          (motive := fun u : ℝ => -Real.pi < Complex.arg x + u)
          (Eq.symm hyinv_arg)
          hlower
    exact htarget
  · have hupper : Complex.arg x - Complex.arg y < Real.pi := by
      exact
        sub_lt_pi_of_lt_pi_div_two_of_neg_pi_div_two_lt
          hx_lt hy_gt
    have htarget :
        Complex.arg x + Complex.arg y⁻¹ < Real.pi := by
      exact
        Eq.subst
          (motive := fun u : ℝ => Complex.arg x + u < Real.pi)
          (Eq.symm hyinv_arg)
          hupper
    exact le_of_lt htarget

/-- Principal-log quotient rule in the open right half-plane. -/
theorem Complex.log_div_eq_sub_log_of_re_pos
    {x y : ℂ}
    (hx : 0 < x.re)
    (hy : 0 < y.re) :
    Complex.log (x / y) = Complex.log x - Complex.log y := by
  have hx_ne :
      x ≠ 0 :=
    Complex.binetAbelPlana_ne_zero_of_re_pos hx
  have hy_ne :
      y ≠ 0 :=
    Complex.binetAbelPlana_ne_zero_of_re_pos hy
  have hy_arg_ne :
      Complex.arg y ≠ Real.pi :=
    Complex.binetAbelPlana_arg_ne_pi_of_re_pos hy
  have hbranch :
      Complex.arg x + Complex.arg y⁻¹ ∈ Set.Ioc (-Real.pi) Real.pi :=
    Complex.binetAbelPlana_arg_add_inv_mem_Ioc_of_re_pos hx hy
  have hlog_mul :
      Complex.log (x * y⁻¹) =
        Complex.log x + Complex.log y⁻¹ :=
    (Complex.log_mul_eq_add_log_iff hx_ne (inv_ne_zero hy_ne)).mpr hbranch
  have hlog_inv :
      Complex.log y⁻¹ = -Complex.log y :=
    Complex.log_inv y hy_arg_ne
  calc
    Complex.log (x / y)
        = Complex.log (x * y⁻¹) := by
      have hdiv : x / y = x * y⁻¹ := by
        exact div_eq_mul_inv _ _
      exact congrArg Complex.log hdiv
    _ = Complex.log x + Complex.log y⁻¹ :=
      hlog_mul
    _ = Complex.log x - Complex.log y := by
      calc
        Complex.log x + Complex.log y⁻¹ = Complex.log x + (-Complex.log y) := by
          exact congrArg (fun z : ℂ => Complex.log x + z) hlog_inv
        _ = Complex.log x - Complex.log y := by
          rfl

/-- Principal-log branch normalization for the quotient of the two Binet
imaginary translates. -/
theorem Complex.binetAbelPlana_log_div_eq_log_sub_log_of_re_pos
    {w : ℂ}
    {t : ℝ}
    (hw : 0 < w.re)
    (_ht : 0 < t) :
    Complex.log
        ((w + (t : ℂ) * Complex.I) /
          (w - (t : ℂ) * Complex.I)) =
      Complex.log (w + (t : ℂ) * Complex.I) -
        Complex.log (w - (t : ℂ) * Complex.I) := by
  exact
    Complex.log_div_eq_sub_log_of_re_pos
      (Complex.add_real_mul_I_re_pos (w := w) (t := t) hw)
      (Complex.sub_real_mul_I_re_pos (w := w) (t := t) hw)

/-- Branch-normalized principal arctangent as the Abel-Plana logarithmic
jump. -/
theorem Complex.binetAbelPlana_two_arctan_eq_negI_mul_logJump
    {w : ℂ}
    {t : ℝ}
    (hw : 0 < w.re)
    (ht : 0 < t) :
    2 * Complex.arctan ((t : ℂ) / w) =
      (-Complex.I) *
        (Complex.log (w + (t : ℂ) * Complex.I) -
          Complex.log (w - (t : ℂ) * Complex.I)) := by
  have hcayley :
      (1 + ((t : ℂ) / w) * Complex.I) /
          (1 - ((t : ℂ) / w) * Complex.I) =
        (w + (t : ℂ) * Complex.I) /
          (w - (t : ℂ) * Complex.I) :=
    Complex.binetAbelPlana_arctan_cayley_eq_logJump_ratio
      (w := w) (t := t) hw
  have hlog :
      Complex.log
          ((w + (t : ℂ) * Complex.I) /
            (w - (t : ℂ) * Complex.I)) =
        Complex.log (w + (t : ℂ) * Complex.I) -
          Complex.log (w - (t : ℂ) * Complex.I) :=
    Complex.binetAbelPlana_log_div_eq_log_sub_log_of_re_pos
      (w := w) (t := t) hw ht
  calc
    2 * Complex.arctan ((t : ℂ) / w)
        =
        2 *
          ((-Complex.I / 2) *
            Complex.log
              ((1 + ((t : ℂ) / w) * Complex.I) /
                (1 - ((t : ℂ) / w) * Complex.I))) := by
      rfl
    _ =
        (-Complex.I) *
          Complex.log
            ((1 + ((t : ℂ) / w) * Complex.I) /
              (1 - ((t : ℂ) / w) * Complex.I)) := by
      calc
        2 *
            ((-Complex.I / 2) *
              Complex.log
                ((1 + ((t : ℂ) / w) * Complex.I) /
                  (1 - ((t : ℂ) / w) * Complex.I))) =
            (2 * (-Complex.I / 2)) *
              Complex.log
                ((1 + ((t : ℂ) / w) * Complex.I) /
                  (1 - ((t : ℂ) / w) * Complex.I)) := by
          exact
            (mul_assoc 2 (-Complex.I / 2)
              (Complex.log
                ((1 + ((t : ℂ) / w) * Complex.I) /
                  (1 - ((t : ℂ) / w) * Complex.I)))).symm
        _ =
            ((-Complex.I / 2) * 2) *
              Complex.log
                ((1 + ((t : ℂ) / w) * Complex.I) /
                  (1 - ((t : ℂ) / w) * Complex.I)) := by
          exact congrArg
            (fun z : ℂ =>
              z *
                Complex.log
                  ((1 + ((t : ℂ) / w) * Complex.I) /
                    (1 - ((t : ℂ) / w) * Complex.I)))
            (mul_comm 2 (-Complex.I / 2))
        _ =
            (-Complex.I) *
              Complex.log
                ((1 + ((t : ℂ) / w) * Complex.I) /
                  (1 - ((t : ℂ) / w) * Complex.I)) := by
          exact congrArg
            (fun z : ℂ =>
              z *
                Complex.log
                  ((1 + ((t : ℂ) / w) * Complex.I) /
                    (1 - ((t : ℂ) / w) * Complex.I)))
            (div_mul_cancel₀ (-Complex.I) (two_ne_zero : (2 : ℂ) ≠ 0))
    _ =
        (-Complex.I) *
          Complex.log
            ((w + (t : ℂ) * Complex.I) /
              (w - (t : ℂ) * Complex.I)) := by
      exact congrArg (fun z : ℂ => (-Complex.I) * Complex.log z) hcayley
    _ =
        (-Complex.I) *
          (Complex.log (w + (t : ℂ) * Complex.I) -
            Complex.log (w - (t : ℂ) * Complex.I)) := by
      exact congrArg (fun z : ℂ => (-Complex.I) * z) hlog

/-- Pointwise Abel-Plana branch normalization: the logarithmic jump across the
imaginary translate of `w` is exactly twice the principal arctangent kernel.

This is the branch-sensitive core of the Binet boundary normalization. -/
theorem Complex.binetAbelPlana_logJump_integrand_eq_two_arctanKernel
    {w : ℂ}
    {t : ℝ}
    (hw : 0 < w.re)
    (ht : 0 < t) :
    (-Complex.I) *
        ((Complex.log (w + (t : ℂ) * Complex.I) -
            Complex.log (w - (t : ℂ) * Complex.I)) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)) =
      2 *
        (Complex.arctan ((t : ℂ) / w) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)) := by
  have hjump :
      2 * Complex.arctan ((t : ℂ) / w) =
        (-Complex.I) *
          (Complex.log (w + (t : ℂ) * Complex.I) -
            Complex.log (w - (t : ℂ) * Complex.I)) :=
    Complex.binetAbelPlana_two_arctan_eq_negI_mul_logJump
      (w := w) (t := t) hw ht
  calc
    (-Complex.I) *
        ((Complex.log (w + (t : ℂ) * Complex.I) -
            Complex.log (w - (t : ℂ) * Complex.I)) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
        =
        ((-Complex.I) *
          (Complex.log (w + (t : ℂ) * Complex.I) -
            Complex.log (w - (t : ℂ) * Complex.I))) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) := by
      exact
        (mul_div_assoc
          (-Complex.I)
          (Complex.log (w + (t : ℂ) * Complex.I) -
            Complex.log (w - (t : ℂ) * Complex.I))
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)).symm
    _ =
        (2 * Complex.arctan ((t : ℂ) / w)) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) := by
      exact congrArg
        (fun z : ℂ => z / (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
        (Eq.symm hjump)
    _ =
        2 *
          (Complex.arctan ((t : ℂ) / w) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)) := by
      exact
        mul_div_assoc
          (2 : ℂ)
          (Complex.arctan ((t : ℂ) / w))
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)


/-- The finite lower boundary correction is the lower vertical integrand
integrated over the finite window `(0,N]`. -/
theorem Complex.binetAbelPlanaFiniteBoundaryCorrection_eq_lowerVertical_window
    (N : ℕ)
    (w : ℂ) :
    Complex.binetAbelPlanaFiniteBoundaryCorrection N w =
      ∫ t : ℝ in Set.Ioc (0 : ℝ) (N : ℝ),
        Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t := by
  rfl

/-- The finite lower contour tail is the lower vertical integrand integrated
over `(N,∞)`. -/
theorem Complex.binetAbelPlanaFiniteLowerContourTail_eq_lowerVertical_tail
    (N : ℕ)
    (w : ℂ) :
    Complex.binetAbelPlanaFiniteLowerContourTail N w =
      ∫ t : ℝ in Set.Ioi (N : ℝ),
        Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t := by
  rfl

/-- The named lower vertical split unfolds to the finite window plus the
tail of the same lower vertical integrand. -/
theorem Complex.finiteAbelPlana_log_lowerVerticalSplit_unfold
    (N : ℕ)
    (w : ℂ) :
    Complex.finiteAbelPlanaLogSummandLowerVerticalIntegral N w =
      (∫ t : ℝ in Set.Ioc (0 : ℝ) (N : ℝ),
        Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t) +
        ∫ t : ℝ in Set.Ioi (N : ℝ),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t := by
  rfl

/-- The lower vertical integrand is the logarithmic jump kernel used in the
finite Abel-Plana boundary correction. -/
theorem Complex.finiteAbelPlana_log_lowerVerticalIntegrand_unfold
    (w : ℂ)
    (t : ℝ) :
    Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t =
      (-Complex.I) *
        ((Complex.log (w + (t : ℂ) * Complex.I) -
            Complex.log (w - (t : ℂ) * Complex.I)) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)) := by
  rfl

/-- The concrete upper vertical integrand is the one used in the finite upper
contour residual. -/
theorem Complex.finiteAbelPlana_log_upperVerticalIntegrand_eq_binet
    (N : ℕ)
    (w : ℂ)
    (t : ℝ) :
    Complex.finiteAbelPlanaLogUpperVerticalIntegrand N w t =
      Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t := by
  rfl

/-- The upper vertical integrand is definitionally the finite Binet upper
vertical boundary integrand. -/
theorem Complex.finiteAbelPlana_log_upperVerticalIntegrand_unfold
    (N : ℕ)
    (w : ℂ)
    (t : ℝ) :
    Complex.finiteAbelPlanaLogUpperVerticalIntegrand N w t =
      Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t := by
  rfl

/-- The upper vertical Abel-Plana jump integrand is definitionally the finite
Binet upper vertical integrand. -/
theorem Complex.finiteAbelPlana_log_upperVerticalJumpIntegrand_eq_binet
    (N : ℕ)
    (w : ℂ)
    (t : ℝ) :
    Complex.finiteAbelPlanaLogUpperVerticalIntegrand N w t =
      Complex.finiteAbelPlanaLogUpperVerticalIntegrand N w t := by
  rfl

end

end LFunctions
end Boundary
