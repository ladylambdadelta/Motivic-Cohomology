import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ArchimedeanGammaBinetKernels
import Mathlib.Topology.Basic

/-!
# Centered archimedean Weil functional

This file owns the Gamma-factor distribution on the centered spectral line.
Affine contour values and time-side Binet formulas are representations of this
functional; they must not replace it by a point evaluation.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open LSeries ArithmeticFunction
open MeasureTheory
open Filter
open scoped ArithmeticFunction
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The contour branch uses the analytic-core critical spectral line. -/
abbrev zetaCompletedExplicitFormulaCenteredSpectralLine (t : ℝ) : ℂ :=
  zetaCompletedCenteredSpectralLine t

/-- The genuine archimedean term in the completed Weil explicit formula.

The argument of `Phi` is centered because `Phi` is the bilateral Laplace
transform of the logarithmic-line probe.  This functional is generally
nonlocal in the probe and therefore cannot be represented by `Phi f 0`.
-/
abbrev zetaCompletedArchimedeanWeilFunctional
    (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaArchimedeanContribution f

/-- The centered archimedean functional unfolds to its defining vertical
integral. -/
theorem zetaCompletedArchimedeanWeilFunctional_eq_centeredIntegral
    (f : ZetaAdmissibleFunction) :
    zetaCompletedArchimedeanWeilFunctional f =
      ∫ t : ℝ,
        zetaCompletedArchimedeanHermitianKernel t *
          zetaCompletedExplicitFormulaPhi f (t * Complex.I) := by
  exact zetaCompletedExplicitFormulaArchimedeanContribution_eq f

/-- The right affine-line representation of the archimedean functional. -/
noncomputable def zetaCompletedArchimedeanRightAffineFunctional
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) : ℂ :=
  ∫ t : ℝ,
    zetaCompletedExplicitFormulaArchimedeanRightAffineKernel f F t

/-- The left affine-line representation of the archimedean functional. -/
noncomputable def zetaCompletedArchimedeanLeftAffineFunctional
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) : ℂ :=
  ∫ t : ℝ,
    zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel f F t

/-- The right affine functional unfolds to the existing right Gamma kernel. -/
theorem zetaCompletedArchimedeanRightAffineFunctional_eq_integral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) :
    zetaCompletedArchimedeanRightAffineFunctional f F =
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightAffineKernel f F t := by
  rfl

/-- The left affine functional unfolds to the existing left Gamma kernel. -/
theorem zetaCompletedArchimedeanLeftAffineFunctional_eq_integral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) :
    zetaCompletedArchimedeanLeftAffineFunctional f F =
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel f F t := by
  rfl

/-- The `n`th zero of the reciprocal real Gamma factor. -/
noncomputable def zetaCompletedGammaTrivialZero (n : ℕ) : ℂ :=
  -((2 * n : ℕ) : ℂ)

/-- The centered transform coordinate contributed by the `n`th reciprocal
Gamma zero. -/
noncomputable def zetaCompletedGammaTrivialZeroResidueCoordinate
    (f : ZetaAdmissibleFunction) (n : ℕ) : ℂ :=
  zetaCompletedExplicitFormulaPhi f
    (zetaCompletedGammaTrivialZero n - (1 / 2 : ℂ))

/-- The finite Gamma trivial-zero residue sum occurring in a bounded contour
window.  No infinite residue expansion is asserted for bilateral probes. -/
noncomputable def zetaCompletedGammaTrivialZeroFiniteResidueSum
    (f : ZetaAdmissibleFunction) (N : ℕ) : ℂ :=
  ∑ n in Finset.range N,
    zetaCompletedGammaTrivialZeroResidueCoordinate f n

/-- A safe finite search window containing every reciprocal-Gamma zero in the
affine contour strip. -/
noncomputable def zetaCompletedGammaTrivialZeroContourSearchBound
    (F : ExplicitFormulaContourFamily) : ℕ :=
  Nat.ceil ((F.c - 1) / 2) + 1

/-- The reciprocal-Gamma zeros lying strictly inside the affine contour
strip. The explicit filter records the geometric ownership condition rather
than relying on a fixed list of poles. -/
noncomputable def zetaCompletedGammaTrivialZeroContourIndexSet
    (F : ExplicitFormulaContourFamily) : Finset ℕ :=
  (Finset.range (zetaCompletedGammaTrivialZeroContourSearchBound F)).filter
    (fun n : ℕ =>
      1 - F.c < -((2 * n : ℕ) : ℝ) ∧
        -((2 * n : ℕ) : ℝ) < F.c)

/-- The finite reciprocal-Gamma residue packet enclosed by an affine contour. -/
noncomputable def zetaCompletedGammaTrivialZeroContourResidueSum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) : ℂ :=
  ∑ n in zetaCompletedGammaTrivialZeroContourIndexSet F,
    zetaCompletedGammaTrivialZeroResidueCoordinate f n

/-- The centered coordinate of the elementary pole at zero. -/
noncomputable def zetaCompletedArchimedeanZeroPoleResidueCoordinate
    (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))

/-- The centered coordinate of the elementary pole at one. -/
noncomputable def zetaCompletedArchimedeanOnePoleResidueCoordinate
    (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaPhi f (1 / 2 : ℂ)

/-- The raw finite residue packet for the archimedean logarithmic derivative.
The reciprocal Gamma zero at zero and the elementary zero-pole correction are
distinct residues and therefore both occur. -/
noncomputable def zetaCompletedArchimedeanAffineContourResidueSum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) : ℂ :=
  zetaCompletedGammaTrivialZeroContourResidueSum f F +
    zetaCompletedArchimedeanZeroPoleResidueCoordinate f +
    zetaCompletedArchimedeanOnePoleResidueCoordinate f

/-- A Gamma-zero residue coordinate is the transform sampled at the literal
centered negative-even coordinate. -/
theorem zetaCompletedGammaTrivialZeroResidueCoordinate_eq
    (f : ZetaAdmissibleFunction) (n : ℕ) :
    zetaCompletedGammaTrivialZeroResidueCoordinate f n =
      zetaCompletedExplicitFormulaPhi f
        (-((2 * n : ℕ) : ℂ) - (1 / 2 : ℂ)) := by
  rfl

/-- The reciprocal real Gamma factor vanishes at every named Gamma trivial
zero. -/
theorem zetaCompletedGammaTrivialZero_inverseGammaReal_eq_zero
    (n : ℕ) :
    (Complex.Gammaℝ (zetaCompletedGammaTrivialZero n))⁻¹ = 0 := by
  have gammaZero :
      Complex.Gammaℝ (zetaCompletedGammaTrivialZero n) = 0 := by
    exact Complex.Gammaℝ_eq_zero_iff.mpr
      ⟨n, congrArg Neg.neg (Nat.cast_mul 2 n)⟩
  exact Eq.trans (congrArg Inv.inv gammaZero) inv_zero

/-- The punctured derivative slope of reciprocal Gamma at zero is the inverse
of the standard Gamma residue kernel. -/
theorem reciprocalGamma_zero_slope_eq_inverse_residueKernel :
    (fun t : ℂ =>
        t⁻¹ •
          ((Complex.Gamma ((0 : ℂ) + t))⁻¹ -
            (Complex.Gamma 0)⁻¹)) =
      fun t : ℂ => (t * Complex.Gamma t)⁻¹ := by
  funext t
  have gammaAtZero : Complex.Gamma (0 : ℂ) = 0 :=
    Complex.Gamma_zero
  have inverseGammaAtZero : (Complex.Gamma (0 : ℂ))⁻¹ = 0 :=
    Eq.trans (congrArg Inv.inv gammaAtZero) inv_zero
  have gammaAtZeroAdd :
      Complex.Gamma ((0 : ℂ) + t) = Complex.Gamma t :=
    congrArg Complex.Gamma (zero_add t)
  calc
    t⁻¹ •
        ((Complex.Gamma ((0 : ℂ) + t))⁻¹ -
          (Complex.Gamma 0)⁻¹) =
        t⁻¹ * ((Complex.Gamma t)⁻¹ - 0) := by
      have subtractionEquality :
          (Complex.Gamma ((0 : ℂ) + t))⁻¹ -
              (Complex.Gamma 0)⁻¹ =
            (Complex.Gamma t)⁻¹ - 0 :=
        congrArg₂ HSub.hSub
          (congrArg Inv.inv gammaAtZeroAdd)
          inverseGammaAtZero
      exact congrArg
        (fun value : ℂ => t⁻¹ * value)
        subtractionEquality
    _ = t⁻¹ * (Complex.Gamma t)⁻¹ := by
      exact congrArg (fun z : ℂ => t⁻¹ * z)
        (sub_zero (Complex.Gamma t)⁻¹)
    _ = (Complex.Gamma t)⁻¹ * t⁻¹ :=
      mul_comm t⁻¹ (Complex.Gamma t)⁻¹
    _ = (t * Complex.Gamma t)⁻¹ := by
      exact (mul_inv_rev t (Complex.Gamma t)).symm

/-- Reciprocal Gamma has derivative one at its zero at the origin. -/
theorem reciprocalGamma_hasDerivAt_zero :
    HasDerivAt (fun z : ℂ => (Complex.Gamma z)⁻¹) 1 0 := by
  have inverseResidueLimit :
      Tendsto (fun z : ℂ => (z * Complex.Gamma z)⁻¹)
        (𝓝[≠] (0 : ℂ)) (𝓝 (1 : ℂ)) := by
    have rawInverseLimit :
        Tendsto (fun z : ℂ => (z * Complex.Gamma z)⁻¹)
          (𝓝[≠] (0 : ℂ)) (𝓝 ((1 : ℂ)⁻¹)) :=
      Complex.tendsto_self_mul_Gamma_nhds_zero.inv₀ one_ne_zero
    exact Eq.subst
      (motive := fun value : ℂ =>
        Tendsto (fun z : ℂ => (z * Complex.Gamma z)⁻¹)
          (𝓝[≠] (0 : ℂ)) (𝓝 value))
      (inv_one : (1 : ℂ)⁻¹ = 1)
      rawInverseLimit
  have slopeLimit :
      Tendsto
        (fun t : ℂ =>
          t⁻¹ •
            ((Complex.Gamma ((0 : ℂ) + t))⁻¹ -
              (Complex.Gamma 0)⁻¹))
        (𝓝[≠] (0 : ℂ)) (𝓝 (1 : ℂ)) := by
    exact Eq.subst
      (motive := fun slope : ℂ → ℂ =>
        Tendsto slope (𝓝[≠] (0 : ℂ)) (𝓝 (1 : ℂ)))
      reciprocalGamma_zero_slope_eq_inverse_residueKernel.symm
      inverseResidueLimit
  exact hasDerivAt_iff_tendsto_slope_zero.mpr slopeLimit

/-- Reciprocal Gamma written globally in recurrence form. -/
theorem reciprocalGamma_eq_self_mul_shift :
    (fun z : ℂ => (Complex.Gamma z)⁻¹) =
      fun z : ℂ => z * (Complex.Gamma (z + 1))⁻¹ := by
  funext z
  exact Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one z

/-- A simple zero of reciprocal Gamma at `z + 1` transports through the
Gamma recurrence to a derivative multiplied by `z` at `z`. -/
theorem reciprocalGamma_recurrence_hasDerivAt
    {z derivativeValue : ℂ}
    (nextDerivative :
      HasDerivAt (fun w : ℂ => (Complex.Gamma w)⁻¹)
        derivativeValue (z + 1))
    (nextValue : (Complex.Gamma (z + 1))⁻¹ = 0) :
    HasDerivAt (fun w : ℂ => (Complex.Gamma w)⁻¹)
      (z * derivativeValue) z := by
  have shiftDerivative :
      HasDerivAt
        (fun w : ℂ => (Complex.Gamma (w + 1))⁻¹)
        derivativeValue z := by
    have rawShiftDerivative :
        HasDerivAt
          ((fun w : ℂ => (Complex.Gamma w)⁻¹) ∘
            fun w : ℂ => w + 1)
          (derivativeValue * 1) z :=
      nextDerivative.comp z ((hasDerivAt_id z).add_const (1 : ℂ))
    have normalizedShiftDerivative :
        HasDerivAt
          ((fun w : ℂ => (Complex.Gamma w)⁻¹) ∘
            fun w : ℂ => w + 1)
          derivativeValue z :=
      rawShiftDerivative.congr_deriv (mul_one derivativeValue)
    have functionEquality :
        ((fun w : ℂ => (Complex.Gamma w)⁻¹) ∘
            fun w : ℂ => w + 1) =
          fun w : ℂ => (Complex.Gamma (w + 1))⁻¹ :=
      rfl
    exact Eq.subst
      (motive := fun shiftedFunction : ℂ → ℂ =>
        HasDerivAt shiftedFunction derivativeValue z)
      functionEquality
      normalizedShiftDerivative
  have identityDerivative : HasDerivAt (fun w : ℂ => w) 1 z :=
    hasDerivAt_id z
  have productDerivativeRaw :
      HasDerivAt
        (fun w : ℂ => w * (Complex.Gamma (w + 1))⁻¹)
        (1 * (Complex.Gamma (z + 1))⁻¹ + z * derivativeValue) z :=
    identityDerivative.mul shiftDerivative
  have derivativeNormalization :
      1 * (Complex.Gamma (z + 1))⁻¹ + z * derivativeValue =
        z * derivativeValue := by
    calc
      1 * (Complex.Gamma (z + 1))⁻¹ + z * derivativeValue =
          1 * 0 + z * derivativeValue := by
        exact congrArg
          (fun value : ℂ => 1 * value + z * derivativeValue)
          nextValue
      _ = 0 + z * derivativeValue := by
        exact congrArg (fun value : ℂ => value + z * derivativeValue)
          (mul_zero (1 : ℂ))
      _ = z * derivativeValue :=
        zero_add (z * derivativeValue)
  have productDerivative :
      HasDerivAt
        (fun w : ℂ => w * (Complex.Gamma (w + 1))⁻¹)
        (z * derivativeValue) z :=
    productDerivativeRaw.congr_deriv derivativeNormalization
  exact Eq.subst
    (motive := fun gammaRecurrence : ℂ → ℂ =>
      HasDerivAt gammaRecurrence (z * derivativeValue) z)
    reciprocalGamma_eq_self_mul_shift.symm
    productDerivative

/-- Reciprocal Gamma has a simple zero at every nonpositive integer. -/
theorem reciprocalGamma_exists_nonzero_derivative_at_neg_nat
    (n : ℕ) :
    ∃ derivativeValue : ℂ,
      HasDerivAt (fun w : ℂ => (Complex.Gamma w)⁻¹)
        derivativeValue (-((n : ℂ))) ∧
      derivativeValue ≠ 0 := by
  induction n with
  | zero =>
      have pointNormalization : -(((0 : ℕ) : ℂ)) = 0 :=
        Eq.trans
          (congrArg Neg.neg (Nat.cast_zero : (((0 : ℕ) : ℂ)) = 0))
          (neg_zero : -(0 : ℂ) = 0)
      have derivativeAtPoint :
          HasDerivAt (fun w : ℂ => (Complex.Gamma w)⁻¹) 1
            (-(((0 : ℕ) : ℂ))) :=
        Eq.subst
          (motive := fun point : ℂ =>
            HasDerivAt (fun w : ℂ => (Complex.Gamma w)⁻¹) 1 point)
          pointNormalization.symm
          reciprocalGamma_hasDerivAt_zero
      exact ⟨1, derivativeAtPoint, one_ne_zero⟩
  | succ n inductionHypothesis =>
      match inductionHypothesis with
      | ⟨derivativeValue, derivativeAtPrevious, derivativeValueNonzero⟩ =>
          let currentPoint : ℂ := -(((Nat.succ n : ℕ) : ℂ))
          have castSuccessor :
              (((Nat.succ n : ℕ) : ℂ)) = (n : ℂ) + 1 :=
            Nat.cast_succ n
          have shiftedPoint : currentPoint + 1 = -((n : ℂ)) := by
            calc
              currentPoint + 1 = -(((Nat.succ n : ℕ) : ℂ)) + 1 := by
                rfl
              _ = -((n : ℂ) + 1) + 1 := by
                exact congrArg (fun value : ℂ => -value + 1) castSuccessor
              _ = (-(n : ℂ) - 1) + 1 := by
                exact congrArg (fun value : ℂ => value + 1)
                  (neg_add (n : ℂ) 1)
              _ = -(n : ℂ) :=
                sub_add_cancel (-(n : ℂ)) 1
          have derivativeAtShiftedPoint :
              HasDerivAt (fun w : ℂ => (Complex.Gamma w)⁻¹)
                derivativeValue (currentPoint + 1) :=
            Eq.subst
              (motive := fun point : ℂ =>
                HasDerivAt (fun w : ℂ => (Complex.Gamma w)⁻¹)
                  derivativeValue point)
              shiftedPoint.symm
              derivativeAtPrevious
          have gammaAtPrevious :
              Complex.Gamma (-((n : ℂ))) = 0 :=
            Complex.Gamma_neg_nat_eq_zero n
          have reciprocalGammaAtPrevious :
              (Complex.Gamma (-((n : ℂ))))⁻¹ = 0 :=
            Eq.trans (congrArg Inv.inv gammaAtPrevious) inv_zero
          have reciprocalGammaAtShiftedPoint :
              (Complex.Gamma (currentPoint + 1))⁻¹ = 0 :=
            Eq.subst
              (motive := fun point : ℂ =>
                (Complex.Gamma point)⁻¹ = 0)
              shiftedPoint.symm
              reciprocalGammaAtPrevious
          have derivativeAtCurrent :
              HasDerivAt (fun w : ℂ => (Complex.Gamma w)⁻¹)
                (currentPoint * derivativeValue) currentPoint :=
            reciprocalGamma_recurrence_hasDerivAt
              derivativeAtShiftedPoint reciprocalGammaAtShiftedPoint
          have currentPointNonzero : currentPoint ≠ 0 := by
            have castNonzero : (((Nat.succ n : ℕ) : ℂ)) ≠ 0 :=
              Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
            exact neg_ne_zero.mpr castNonzero
          have derivativeAtCurrentNonzero :
              currentPoint * derivativeValue ≠ 0 :=
            mul_ne_zero currentPointNonzero derivativeValueNonzero
          exact
            ⟨currentPoint * derivativeValue,
              derivativeAtCurrent,
              derivativeAtCurrentNonzero⟩

/-- Halving the `n`th real-Gamma zero gives the corresponding reciprocal
Gamma zero. -/
theorem zetaCompletedGammaTrivialZero_div_two
    (n : ℕ) :
    zetaCompletedGammaTrivialZero n / 2 = -((n : ℂ)) := by
  have castProduct :
      (((2 * n : ℕ) : ℂ)) = (2 : ℂ) * (n : ℂ) :=
    Nat.cast_mul 2 n
  calc
    zetaCompletedGammaTrivialZero n / 2 =
        -(((2 * n : ℕ) : ℂ)) / 2 := by
      rfl
    _ = -((2 : ℂ) * (n : ℂ)) / 2 := by
      exact congrArg (fun value : ℂ => -value / 2) castProduct
    _ = -(((2 : ℂ) * (n : ℂ)) / 2) :=
      neg_div (2 : ℂ) ((2 : ℂ) * (n : ℂ))
    _ = -((n : ℂ)) := by
      exact congrArg Neg.neg
        (mul_div_cancel_left₀ (n : ℂ) (two_ne_zero' ℂ))

/-- Reciprocal `Gammaℝ` as the product of the reciprocal power factor and
reciprocal Gamma at the half argument. -/
theorem inverseGammaReal_eq_powerFactor_mul_reciprocalGamma :
    (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) =
      fun s : ℂ =>
        ((Real.pi : ℂ) ^ (-s / 2))⁻¹ *
          (Complex.Gamma (s / 2))⁻¹ := by
  funext s
  have gammaRealExpansion :
      Complex.Gammaℝ s =
        (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) :=
    Complex.Gammaℝ_def s
  calc
    (Complex.Gammaℝ s)⁻¹ =
        (((Real.pi : ℂ) ^ (-s / 2) *
          Complex.Gamma (s / 2)))⁻¹ := by
      exact congrArg Inv.inv gammaRealExpansion
    _ = (Complex.Gamma (s / 2))⁻¹ *
        ((Real.pi : ℂ) ^ (-s / 2))⁻¹ :=
      mul_inv_rev
        ((Real.pi : ℂ) ^ (-s / 2))
        (Complex.Gamma (s / 2))
    _ = ((Real.pi : ℂ) ^ (-s / 2))⁻¹ *
        (Complex.Gamma (s / 2))⁻¹ :=
      mul_comm
        (Complex.Gamma (s / 2))⁻¹
        ((Real.pi : ℂ) ^ (-s / 2))⁻¹

/-- Every reciprocal real-Gamma zero has a nonzero derivative. -/
theorem inverseGammaReal_exists_nonzero_derivative_at_trivialZero
    (n : ℕ) :
    ∃ derivativeValue : ℂ,
      HasDerivAt (fun s : ℂ => (Complex.Gammaℝ s)⁻¹)
        derivativeValue (zetaCompletedGammaTrivialZero n) ∧
      derivativeValue ≠ 0 := by
  match reciprocalGamma_exists_nonzero_derivative_at_neg_nat n with
  | ⟨gammaDerivative, gammaHasDerivative, gammaDerivativeNonzero⟩ =>
      let point : ℂ := zetaCompletedGammaTrivialZero n
      let powerFactor : ℂ → ℂ := fun s : ℂ =>
        ((Real.pi : ℂ) ^ (-s / 2))⁻¹
      have halfPoint : point / 2 = -((n : ℂ)) := by
        unfold point
        exact zetaCompletedGammaTrivialZero_div_two n
      have gammaHasDerivativeAtHalfPoint :
          HasDerivAt (fun w : ℂ => (Complex.Gamma w)⁻¹)
            gammaDerivative (point / 2) :=
        Eq.subst
          (motive := fun gammaPoint : ℂ =>
            HasDerivAt (fun w : ℂ => (Complex.Gamma w)⁻¹)
              gammaDerivative gammaPoint)
          halfPoint.symm
          gammaHasDerivative
      have halfMapHasDerivative :
          HasDerivAt (fun s : ℂ => s / 2) (1 / 2 : ℂ) point :=
        (hasDerivAt_id point).div_const 2
      have reciprocalGammaHalfHasDerivative :
          HasDerivAt (fun s : ℂ => (Complex.Gamma (s / 2))⁻¹)
            (gammaDerivative * (1 / 2 : ℂ)) point :=
        gammaHasDerivativeAtHalfPoint.comp point halfMapHasDerivative
      have gammaAtNegativeInteger :
          Complex.Gamma (-((n : ℂ))) = 0 :=
        Complex.Gamma_neg_nat_eq_zero n
      have reciprocalGammaAtNegativeInteger :
          (Complex.Gamma (-((n : ℂ))))⁻¹ = 0 :=
        Eq.trans (congrArg Inv.inv gammaAtNegativeInteger) inv_zero
      have reciprocalGammaHalfValue :
          (Complex.Gamma (point / 2))⁻¹ = 0 :=
        Eq.subst
          (motive := fun gammaPoint : ℂ =>
            (Complex.Gamma gammaPoint)⁻¹ = 0)
          halfPoint.symm
          reciprocalGammaAtNegativeInteger
      have piComplexNonzero : (Real.pi : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      have powerValueNonzeroRaw :
          (Real.pi : ℂ) ^ (-point / 2) ≠ 0 := by
        exact fun powerZero : (Real.pi : ℂ) ^ (-point / 2) = 0 =>
          piComplexNonzero
            ((Complex.cpow_eq_zero_iff
              (Real.pi : ℂ) (-point / 2)).mp powerZero).1
      have powerValueNonzero : powerFactor point ≠ 0 := by
        unfold powerFactor
        exact inv_ne_zero powerValueNonzeroRaw
      have exponentDifferentiable :
          DifferentiableAt ℂ (fun s : ℂ => -s / 2) point :=
        differentiableAt_id.neg.div_const 2
      have powerRawDifferentiable :
          DifferentiableAt ℂ
            (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) point :=
        exponentDifferentiable.const_cpow (Or.inl piComplexNonzero)
      have powerFactorDifferentiable :
          DifferentiableAt ℂ powerFactor point := by
        unfold powerFactor
        exact powerRawDifferentiable.inv powerValueNonzeroRaw
      let powerDerivative : ℂ := deriv powerFactor point
      have powerFactorHasDerivative :
          HasDerivAt powerFactor powerDerivative point := by
        unfold powerDerivative
        exact powerFactorDifferentiable.hasDerivAt
      have productDerivativeRaw :
          HasDerivAt
            (fun s : ℂ =>
              powerFactor s * (Complex.Gamma (s / 2))⁻¹)
            (powerDerivative * (Complex.Gamma (point / 2))⁻¹ +
              powerFactor point *
                (gammaDerivative * (1 / 2 : ℂ))) point :=
        powerFactorHasDerivative.mul reciprocalGammaHalfHasDerivative
      have productDerivativeNormalization :
          powerDerivative * (Complex.Gamma (point / 2))⁻¹ +
              powerFactor point *
                (gammaDerivative * (1 / 2 : ℂ)) =
            powerFactor point *
              (gammaDerivative * (1 / 2 : ℂ)) := by
        calc
          powerDerivative * (Complex.Gamma (point / 2))⁻¹ +
                powerFactor point *
                  (gammaDerivative * (1 / 2 : ℂ)) =
              powerDerivative * 0 +
                powerFactor point *
                  (gammaDerivative * (1 / 2 : ℂ)) := by
            exact congrArg
              (fun value : ℂ =>
                powerDerivative * value +
                  powerFactor point *
                    (gammaDerivative * (1 / 2 : ℂ)))
              reciprocalGammaHalfValue
          _ = 0 + powerFactor point *
                (gammaDerivative * (1 / 2 : ℂ)) := by
            exact congrArg
              (fun value : ℂ =>
                value + powerFactor point *
                  (gammaDerivative * (1 / 2 : ℂ)))
              (mul_zero powerDerivative)
          _ = powerFactor point *
                (gammaDerivative * (1 / 2 : ℂ)) :=
            zero_add
              (powerFactor point *
                (gammaDerivative * (1 / 2 : ℂ)))
      have productDerivative :
          HasDerivAt
            (fun s : ℂ =>
              powerFactor s * (Complex.Gamma (s / 2))⁻¹)
            (powerFactor point *
              (gammaDerivative * (1 / 2 : ℂ))) point :=
        productDerivativeRaw.congr_deriv productDerivativeNormalization
      have inverseGammaRealDerivative :
          HasDerivAt (fun s : ℂ => (Complex.Gammaℝ s)⁻¹)
            (powerFactor point *
              (gammaDerivative * (1 / 2 : ℂ))) point := by
        have factorizedFunctionEquality :
            (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) =
              fun s : ℂ =>
                powerFactor s * (Complex.Gamma (s / 2))⁻¹ := by
          unfold powerFactor
          exact inverseGammaReal_eq_powerFactor_mul_reciprocalGamma
        exact Eq.subst
          (motive := fun factorizedFunction : ℂ → ℂ =>
            HasDerivAt factorizedFunction
              (powerFactor point *
                (gammaDerivative * (1 / 2 : ℂ))) point)
          factorizedFunctionEquality.symm
          productDerivative
      have halfNonzero : (1 / 2 : ℂ) ≠ 0 :=
        div_ne_zero one_ne_zero (two_ne_zero' ℂ)
      have scaledGammaDerivativeNonzero :
          gammaDerivative * (1 / 2 : ℂ) ≠ 0 :=
        mul_ne_zero gammaDerivativeNonzero halfNonzero
      have inverseGammaRealDerivativeNonzero :
          powerFactor point *
              (gammaDerivative * (1 / 2 : ℂ)) ≠ 0 :=
        mul_ne_zero powerValueNonzero scaledGammaDerivativeNonzero
      exact
        ⟨powerFactor point *
            (gammaDerivative * (1 / 2 : ℂ)),
          inverseGammaRealDerivative,
          inverseGammaRealDerivativeNonzero⟩

/-- A germ with a nonzero derivative cannot vanish identically on a
neighborhood of its base point. -/
theorem not_eventually_zero_of_hasDerivAt_ne_zero
    {g : ℂ → ℂ} {point derivativeValue : ℂ}
    (hasDerivative : HasDerivAt g derivativeValue point)
    (derivativeNonzero : derivativeValue ≠ 0) :
    ¬ ∀ᶠ z in 𝓝 point, g z = 0 := by
  exact fun eventuallyZero =>
    let zeroDerivative :
        HasDerivAt (fun _z : ℂ => (0 : ℂ)) 0 point :=
      hasDerivAt_const point 0
    let functionEventuallyEqZero :
        g =ᶠ[𝓝 point] fun _z : ℂ => (0 : ℂ) :=
      eventuallyZero
    let forcedZeroDerivative : HasDerivAt g 0 point :=
      zeroDerivative.congr_of_eventuallyEq functionEventuallyEqZero
    derivativeNonzero (hasDerivative.unique forcedZeroDerivative)

/-- Reciprocal real Gamma is not locally the zero function at any Gamma
trivial zero. -/
theorem inverseGammaReal_not_eventually_zero_at_trivialZero
    (n : ℕ) :
    ¬ ∀ᶠ z in 𝓝 (zetaCompletedGammaTrivialZero n),
      (Complex.Gammaℝ z)⁻¹ = 0 := by
  match inverseGammaReal_exists_nonzero_derivative_at_trivialZero n with
  | ⟨derivativeValue, hasDerivative, derivativeNonzero⟩ =>
      exact not_eventually_zero_of_hasDerivAt_ne_zero
        hasDerivative derivativeNonzero

/-- An analytic zero with nonzero derivative has analytic order one. -/
theorem analyticAt_order_eq_one_of_hasDerivAt_ne_zero
    {g : ℂ → ℂ} {point derivativeValue : ℂ}
    (analyticAtPoint : AnalyticAt ℂ g point)
    (valueZero : g point = 0)
    (hasDerivative : HasDerivAt g derivativeValue point)
    (derivativeNonzero : derivativeValue ≠ 0) :
    analyticAtPoint.order = (1 : ℕ∞) := by
  let firstFactor : ℂ → ℂ := dslope g point
  have firstFactorAnalytic : AnalyticAt ℂ firstFactor point := by
    unfold firstFactor
    match analyticAtPoint with
    | ⟨series, hasSeries⟩ =>
        exact ⟨series.fslope,
          hasSeries.has_fpower_series_dslope_fslope⟩
  have firstFactorValue : firstFactor point = derivativeValue := by
    unfold firstFactor
    exact Eq.trans (dslope_same g point) hasDerivative.deriv
  have firstFactorNonzero : firstFactor point ≠ 0 :=
    fun firstFactorZero =>
      derivativeNonzero (Eq.trans firstFactorValue.symm firstFactorZero)
  have factorization :
      ∀ᶠ z in 𝓝 point,
        g z = (z - point) ^ (1 : ℕ) • firstFactor z := by
    exact eventually_of_forall fun z => by
      calc
        g z = g z - 0 :=
          (sub_zero (g z)).symm
        _ = g z - g point := by
          exact congrArg (fun value : ℂ => g z - value) valueZero.symm
        _ = (z - point) • dslope g point z :=
          (sub_smul_dslope g point z).symm
        _ = (z - point) • firstFactor z := by
          rfl
        _ = (z - point) ^ (1 : ℕ) • firstFactor z := by
          exact congrArg (fun scalar : ℂ => scalar • firstFactor z)
            (pow_one (z - point)).symm
  exact (analyticAtPoint.order_eq_nat_iff 1).mpr
    ⟨firstFactor, firstFactorAnalytic, firstFactorNonzero, factorization⟩

/-- Reciprocal real Gamma has analytic order one at each Gamma trivial zero. -/
theorem inverseGammaReal_order_eq_one_at_trivialZero
    (n : ℕ) :
    (Complex.differentiable_Gammaℝ_inv.analyticAt
      (zetaCompletedGammaTrivialZero n)).order = (1 : ℕ∞) := by
  match inverseGammaReal_exists_nonzero_derivative_at_trivialZero n with
  | ⟨derivativeValue, hasDerivative, derivativeNonzero⟩ =>
      exact analyticAt_order_eq_one_of_hasDerivAt_ne_zero
        (Complex.differentiable_Gammaℝ_inv.analyticAt
          (zetaCompletedGammaTrivialZero n))
        (zetaCompletedGammaTrivialZero_inverseGammaReal_eq_zero n)
        hasDerivative
        derivativeNonzero

/-- The finite Gamma residue sum unfolds to its named coordinate sum. -/
theorem zetaCompletedGammaTrivialZeroFiniteResidueSum_eq_sum
    (f : ZetaAdmissibleFunction) (N : ℕ) :
    zetaCompletedGammaTrivialZeroFiniteResidueSum f N =
      ∑ n in Finset.range N,
        zetaCompletedGammaTrivialZeroResidueCoordinate f n := by
  rfl

/-- The empty Gamma residue window has value zero. -/
theorem zetaCompletedGammaTrivialZeroFiniteResidueSum_zero
    (f : ZetaAdmissibleFunction) :
    zetaCompletedGammaTrivialZeroFiniteResidueSum f 0 = 0 := by
  unfold zetaCompletedGammaTrivialZeroFiniteResidueSum
  exact
    Finset.sum_range_zero
      (fun n : ℕ => zetaCompletedGammaTrivialZeroResidueCoordinate f n)

/-- Enlarging a Gamma residue window by one appends the next named residue
coordinate. -/
theorem zetaCompletedGammaTrivialZeroFiniteResidueSum_succ
    (f : ZetaAdmissibleFunction) (N : ℕ) :
    zetaCompletedGammaTrivialZeroFiniteResidueSum f (N + 1) =
      zetaCompletedGammaTrivialZeroFiniteResidueSum f N +
        zetaCompletedGammaTrivialZeroResidueCoordinate f N := by
  unfold zetaCompletedGammaTrivialZeroFiniteResidueSum
  exact
    Finset.sum_range_succ
      (fun n : ℕ => zetaCompletedGammaTrivialZeroResidueCoordinate f n)
      N

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
