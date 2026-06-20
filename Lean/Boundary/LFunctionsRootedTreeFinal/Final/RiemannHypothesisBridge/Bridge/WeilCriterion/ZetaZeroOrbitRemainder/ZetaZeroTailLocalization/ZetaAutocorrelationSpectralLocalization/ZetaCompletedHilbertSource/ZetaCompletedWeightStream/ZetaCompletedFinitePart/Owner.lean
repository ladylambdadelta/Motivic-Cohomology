import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaCompletedWeightStream.ZetaCompletedFinitePart.ZetaCompletedSquareLedger.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaCompletedWeightStream.ZetaCompletedFinitePart.ZetaPrimeDistributionTransport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.Owner

/-!
# Completed finite-part boundary layer

This file owns the finite-part boundary windows, finite lower-weight absorption
certificates, and the finite-part convergence bridge used by completed boundary
descent.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The renormalized finite-part completed boundary window.  This is the object whose limit is
the completed boundary channel; the positive square-energy window is related to it only after
adding the diagonal debt. -/
def finitePartBoundaryWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  finitePartPrimeOffDiagonalWindow N f +
    zetaPrimeDiagonalDebt N f +
    finitePartDebtAbsorptionWindow N f +
    finitePartArchimedeanCorrectionWindow N f

/-- The finite boundary weight packet for one cutoff.  It keeps the positive square object,
the prime cross term, the diagonal debt, its absorption channel, and the archimedean/correction
term as separate coordinates. -/
structure FiniteBoundaryWeightObject where
  positiveSquare : ℝ
  primeCross : ℝ
  diagonalDebt : ℝ
  debtAbsorption : ℝ
  archCorrection : ℝ

/-- The concrete finite boundary weight packet attached to a cutoff and admissible seed. -/
def finiteBoundaryWeightObject
    (N : ℕ) (f : ZetaAdmissibleFunction) : FiniteBoundaryWeightObject :=
  { positiveSquare := finitePositiveSquareEnergyWindow N f
    primeCross := finitePartPrimeOffDiagonalWindow N f
    diagonalDebt := zetaPrimeDiagonalDebt N f
    debtAbsorption := finitePartDebtAbsorptionWindow N f
    archCorrection := finitePartArchimedeanCorrectionWindow N f }

namespace FiniteBoundaryWeightObject

/-- The finite square representative scalar. -/
def squareRepresentative (x : FiniteBoundaryWeightObject) : ℝ :=
  x.positiveSquare

/-- The finite-part representative scalar after triangular debt absorption. -/
def finitePartRepresentative (x : FiniteBoundaryWeightObject) : ℝ :=
  x.primeCross + x.diagonalDebt + x.debtAbsorption + x.archCorrection

/-- The absorbed square representative scalar. -/
def absorbedSquareRepresentative (x : FiniteBoundaryWeightObject) : ℝ :=
  x.positiveSquare + x.debtAbsorption

/-- The finite diagonal-plus-absorption lower-weight scalar component. -/
def lowerWeightExactRepresentative (x : FiniteBoundaryWeightObject) : ℝ :=
  x.diagonalDebt + x.debtAbsorption

end FiniteBoundaryWeightObject

/-- A concrete lower-weight absorption certificate for a finite boundary packet.  It records
only proved scalar identities: diagonal debt cancels with the absorption channel, and the
absorbed square representative is the finite-part representative. -/
structure FiniteBoundaryLowerWeightAbsorptionCert
    (x : FiniteBoundaryWeightObject) where
  debt_absorption_cancel :
    x.diagonalDebt + x.debtAbsorption = 0
  absorbed_square_eq_finitePart :
    FiniteBoundaryWeightObject.absorbedSquareRepresentative x =
      FiniteBoundaryWeightObject.finitePartRepresentative x

namespace FiniteBoundaryLowerWeightAbsorptionCert

/-- A finite lower-weight absorption certificate says that the lower-weight representative is
exact. -/
theorem lowerWeightExactRepresentative_eq_zero
    {x : FiniteBoundaryWeightObject}
    (h : FiniteBoundaryLowerWeightAbsorptionCert x) :
    FiniteBoundaryWeightObject.lowerWeightExactRepresentative x = 0 := by
  unfold FiniteBoundaryWeightObject.lowerWeightExactRepresentative
  exact h.debt_absorption_cancel

/-- A finite lower-weight absorption certificate transports the positive square representative
to the finite-part representative. -/
theorem weightTriangularTransport
    {x : FiniteBoundaryWeightObject}
    (h : FiniteBoundaryLowerWeightAbsorptionCert x) :
    FiniteBoundaryWeightObject.squareRepresentative x + x.debtAbsorption =
      FiniteBoundaryWeightObject.finitePartRepresentative x := by
  change FiniteBoundaryWeightObject.absorbedSquareRepresentative x =
    FiniteBoundaryWeightObject.finitePartRepresentative x
  exact h.absorbed_square_eq_finitePart

end FiniteBoundaryLowerWeightAbsorptionCert

/-- The completed renormalized boundary channel after passing from the finite triangular
presentation to the positive Hermitian defect-kernel realization.  This is the positive
defect-square channel, not the raw finite-part/off-diagonal boundary scalar. -/
noncomputable def completedRenormalizedDefectKernelBoundaryChannel
    (f : ZetaAdmissibleFunction) : ℝ :=
  completedPrimeDefectKernelPositiveChannel f +
    ZetaHermitianPacketEnsemble.archimedeanPacketGram
      (zetaCompletedHermitianBoundaryDefect f) +
    ZetaHermitianPacketEnsemble.correctionPacketGram
      (zetaCompletedHermitianBoundaryDefect f)

/-- The completed physical finite-part boundary channel.  This is the limit object of the
renormalized square-energy windows before comparing it with the explicit-formula boundary
functional. -/
noncomputable def completedFinitePartBoundaryChannel
    (f : ZetaAdmissibleFunction) : ℝ :=
  completedPrimeDefectKernelRenormalizedChannel f +
    zetaArchimedeanAutocorrelationSquareEnergy f +
    zetaCorrectionAutocorrelationSquareEnergy f

/-- The prime finite-part tail: finite prime off-diagonal window minus the completed prime
off-diagonal channel. -/
def finitePartPrimeTail
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  finitePartPrimeOffDiagonalWindow N f -
    completedPrimeOffDiagonalChannel f

/-- The grouped finite-part tail of the prime defect package: cross term, diagonal debt, and
debt absorption are kept together because the positive prime object is the defect square, not
the raw cross term alone. -/
def finitePartPrimeDefectRenormalizedTail
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  (finitePartPrimeOffDiagonalWindow N f +
      zetaPrimeDiagonalDebt N f +
      finitePartDebtAbsorptionWindow N f) -
    completedPrimeDefectKernelRenormalizedChannel f

/-- The archimedean finite-part tail: the finite archimedean square channel minus the completed
archimedean boundary channel. -/
def finitePartArchimedeanTail
    (_N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  zetaArchimedeanAutocorrelationSquareEnergy f -
    Complex.re (archimedeanBoundaryChannel (convolutionAutocorrelation f))

/-- The pole/completion finite-part tail: the finite correction square channel minus the
completed pole and residual completion channels. -/
def finitePartCorrectionTail
    (_N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  zetaCorrectionAutocorrelationSquareEnergy f -
    Complex.re (poleBoundaryChannel (convolutionAutocorrelation f))

/-- The pole/completion residual tail.  In the current normalization the completion channel is
zero, but it remains a named tail so later refinements of the completed normalization do not
hide pole/completion estimates in the correction theorem. -/
def finitePartPoleTail
    (_N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  - Complex.re (completionBoundaryChannel (convolutionAutocorrelation f))

/-- The total named tail in the finite-part convergence certificate. -/
def finitePartBoundaryTail
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  finitePartPrimeDefectRenormalizedTail N f +
    finitePartArchimedeanTail N f +
    finitePartCorrectionTail N f +
    finitePartPoleTail N f

/-- The literal remainder of the finite-part window after subtracting the completed boundary
channel.  The named tail decomposition refines this remainder into prime, archimedean, and
pole/completion pieces. -/
def finitePartBoundaryRemainder
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  finitePartBoundaryWindow N f -
    completedFinitePartBoundaryChannel f

/-- Four-term subtraction bookkeeping for the finite-part tail certificate. -/
theorem finitePart_three_sub_four_eq_tail_sum
    (P A C p a q r : ℝ) :
    P + A + C - (p + a + q + r) =
      (P - p) + (A - a) + (C - q) + -r := by
  calc
    P + A + C - (p + a + q + r) =
        P + A + C + -(p + a + q + r) := by
      exact sub_eq_add_neg (P + A + C) (p + a + q + r)
    _ = P + A + C + (-(p + a + q) + -r) := by
      exact congrArg
        (fun x : ℝ => P + A + C + x)
        (neg_add (p + a + q) r)
    _ = P + A + C + (-(p + a) + -q + -r) := by
      exact congrArg
        (fun x : ℝ => P + A + C + (x + -r))
        (neg_add (p + a) q)
    _ = P + A + C + ((-p + -a) + -q + -r) := by
      exact congrArg
        (fun x : ℝ => P + A + C + (x + -q + -r))
        (neg_add p a)
    _ = (((P + A + C) + -p) + -a) + -q + -r := by
      calc
        P + A + C + ((-p + -a) + -q + -r) =
            (P + A + C + ((-p + -a) + -q)) + -r := by
          exact (add_assoc (P + A + C) ((-p + -a) + -q) (-r)).symm
        _ = ((P + A + C + (-p + -a)) + -q) + -r := by
          exact congrArg (fun x : ℝ => x + -r)
            ((add_assoc (P + A + C) (-p + -a) (-q)).symm)
        _ = (((P + A + C) + -p) + -a) + -q + -r := by
          exact congrArg (fun x : ℝ => (x + -q) + -r)
            ((add_assoc (P + A + C) (-p) (-a)).symm)
    _ = (((P + -p) + A + C) + -a) + -q + -r := by
      have hmove :
          (P + A + C) + -p = (P + -p) + A + C := by
        calc
          (P + A + C) + -p = ((P + A) + C) + -p := by
            rfl
          _ = (P + A) + (C + -p) := by
            exact add_assoc (P + A) C (-p)
          _ = (P + A) + (-p + C) := by
            exact congrArg (fun x : ℝ => (P + A) + x) (add_comm C (-p))
          _ = ((P + A) + -p) + C := by
            exact (add_assoc (P + A) (-p) C).symm
          _ = (P + (A + -p)) + C := by
            exact congrArg (fun x : ℝ => x + C) (add_assoc P A (-p))
          _ = (P + (-p + A)) + C := by
            exact congrArg (fun x : ℝ => (P + x) + C) (add_comm A (-p))
          _ = ((P + -p) + A) + C := by
            exact congrArg (fun x : ℝ => x + C) ((add_assoc P (-p) A).symm)
          _ = (P + -p) + A + C := by
            rfl
      exact congrArg (fun x : ℝ => ((x + -a) + -q) + -r) hmove
    _ = ((P - p + A + C) + -a) + -q + -r := by
      exact congrArg (fun x : ℝ => ((x + A + C + -a) + -q) + -r)
        (sub_eq_add_neg P p).symm
    _ = (P - p + (A + -a) + C) + -q + -r := by
      have hmove :
          (P - p + A + C) + -a = P - p + (A + -a) + C := by
        calc
          (P - p + A + C) + -a = ((P - p + A) + C) + -a := by
            rfl
          _ = (P - p + A) + (C + -a) := by
            exact add_assoc (P - p + A) C (-a)
          _ = (P - p + A) + (-a + C) := by
            exact congrArg (fun x : ℝ => (P - p + A) + x) (add_comm C (-a))
          _ = ((P - p + A) + -a) + C := by
            exact (add_assoc (P - p + A) (-a) C).symm
          _ = (P - p + (A + -a)) + C := by
            exact congrArg (fun x : ℝ => x + C) (add_assoc (P - p) A (-a))
          _ = P - p + (A + -a) + C := by
            rfl
      exact congrArg (fun x : ℝ => (x + -q) + -r) hmove
    _ = (P - p + (A - a) + C) + -q + -r := by
      exact congrArg (fun x : ℝ => (P - p + x + C + -q) + -r)
        (sub_eq_add_neg A a).symm
    _ = (P - p + (A - a) + (C + -q)) + -r := by
      exact congrArg (fun x : ℝ => x + -r)
        (add_assoc (P - p + (A - a)) C (-q))
    _ = (P - p + (A - a) + (C - q)) + -r := by
      exact congrArg (fun x : ℝ => (P - p + (A - a) + x) + -r)
        (sub_eq_add_neg C q).symm
    _ = (P - p) + (A - a) + (C - q) + -r := by
      rfl

/-- The finite-part window is the completed boundary channel plus its literal remainder. -/
theorem finitePartBoundaryWindow_eq_boundaryChannel_add_remainder
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePartBoundaryWindow N f =
      completedFinitePartBoundaryChannel f +
        finitePartBoundaryRemainder N f := by
  unfold finitePartBoundaryRemainder
  exact zetaBoundaryDebt_add_sub_cancel
    (finitePartBoundaryWindow N f)
    (completedFinitePartBoundaryChannel f)

/-- The named finite-part tails assemble to the literal boundary remainder.  This is the
finite-part cancellation certificate: the prime-defect package is kept grouped as cross term,
diagonal debt, and debt absorption, while archimedean, correction, and completion tails remain
separate. -/
theorem finitePartBoundaryRemainder_eq_tail
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePartBoundaryRemainder N f =
      finitePartBoundaryTail N f := by
  let g : ZetaAdmissibleFunction := convolutionAutocorrelation f
  let P : ℝ :=
    finitePartPrimeOffDiagonalWindow N f +
      zetaPrimeDiagonalDebt N f +
      finitePartDebtAbsorptionWindow N f
  let A : ℝ := zetaArchimedeanAutocorrelationSquareEnergy f
  let C : ℝ := zetaCorrectionAutocorrelationSquareEnergy f
  let p : ℝ :=
    completedPrimeDefectKernelRenormalizedChannel f
  let a : ℝ := Complex.re (archimedeanBoundaryChannel g)
  let q : ℝ := Complex.re (poleBoundaryChannel g)
  let r : ℝ := Complex.re (completionBoundaryChannel g)
  have hfinite :
      finitePartBoundaryWindow N f = P + A + C := by
    unfold finitePartBoundaryWindow
    unfold finitePartPrimeOffDiagonalWindow
    unfold finitePartArchimedeanCorrectionWindow
    unfold finitePartDebtAbsorptionWindow
    unfold zetaArchimedeanCorrectionAutocorrelationChannel
    calc
      zetaPrimeOffDiagonalChannel N f + zetaPrimeDiagonalDebt N f +
          -zetaPrimeDiagonalDebt N f +
          zetaArchimedeanCorrectionAutocorrelationChannel f =
          (zetaPrimeOffDiagonalChannel N f + zetaPrimeDiagonalDebt N f +
            -zetaPrimeDiagonalDebt N f) +
            zetaArchimedeanCorrectionAutocorrelationChannel f := by
        rfl
      _ =
          (zetaPrimeOffDiagonalChannel N f + zetaPrimeDiagonalDebt N f +
            -zetaPrimeDiagonalDebt N f) +
            (zetaArchimedeanAutocorrelationSquareEnergy f +
              zetaCorrectionAutocorrelationSquareEnergy f) := by
        exact congrArg
          (fun x : ℝ =>
            (zetaPrimeOffDiagonalChannel N f + zetaPrimeDiagonalDebt N f +
              -zetaPrimeDiagonalDebt N f) + x)
          (zetaArchimedeanCorrectionAutocorrelationChannel_eq_squareEnergy f)
      _ = P + A + C := by
        unfold P
        unfold A
        unfold C
        exact
          (add_assoc
            (zetaPrimeOffDiagonalChannel N f + zetaPrimeDiagonalDebt N f +
              -zetaPrimeDiagonalDebt N f)
            (zetaArchimedeanAutocorrelationSquareEnergy f)
            (zetaCorrectionAutocorrelationSquareEnergy f)).symm
  have hchannel :
      completedFinitePartBoundaryChannel f = p + a + q + r := by
    have harch :
        a = A := by
      unfold a
      unfold g
      unfold archimedeanBoundaryChannel
      exact zetaArchimedeanAutocorrelationChannel_eq_squareEnergy f
    have hcorr :
        q = C := by
      unfold q
      unfold g
      unfold poleBoundaryChannel
      exact zetaCorrectionAutocorrelationChannel_eq_squareEnergy f
    have hr :
        r = 0 := by
      unfold r
      unfold g
      unfold completionBoundaryChannel
      exact Complex.zero_re
    unfold completedFinitePartBoundaryChannel
    calc
      completedPrimeOffDiagonalChannel f +
          zetaArchimedeanAutocorrelationSquareEnergy f +
          zetaCorrectionAutocorrelationSquareEnergy f =
          p + A + C := by
        unfold p
        unfold completedPrimeDefectKernelRenormalizedChannel
        rfl
      _ = p + a + C := by
        exact congrArg (fun x : ℝ => p + x + C) harch.symm
      _ = p + a + q := by
        exact congrArg (fun x : ℝ => p + a + x) hcorr.symm
      _ = p + a + q + 0 := by
        exact (add_zero (p + a + q)).symm
      _ = p + a + q + r := by
        exact congrArg (fun x : ℝ => p + a + q + x) hr.symm
  unfold finitePartBoundaryRemainder
  unfold finitePartBoundaryTail
  unfold finitePartPrimeDefectRenormalizedTail
  unfold finitePartArchimedeanTail
  unfold finitePartCorrectionTail
  unfold finitePartPoleTail
  change finitePartBoundaryWindow N f - completedFinitePartBoundaryChannel f =
    (P - p) + (A - a) + (C - q) + -r
  calc
    finitePartBoundaryWindow N f - completedFinitePartBoundaryChannel f =
        (P + A + C) - completedFinitePartBoundaryChannel f := by
      exact congrArg (fun x : ℝ => x - completedFinitePartBoundaryChannel f) hfinite
    _ = (P + A + C) - (p + a + q + r) := by
      exact congrArg (fun x : ℝ => (P + A + C) - x) hchannel
    _ = (P - p) + (A - a) + (C - q) + -r := by
      exact finitePart_three_sub_four_eq_tail_sum P A C p a q r

/-- Prime/off-diagonal finite-part tails tend to zero because the growing finite prime windows
converge to the completed prime translation-defect energy.  The analytic content is the
preceding completed-prime convergence theorem. -/
theorem finitePartPrimeTail_tendsto_zero
    (f : ZetaAdmissibleFunction) :
    Tendsto (fun N : ℕ => finitePartPrimeTail N f) atTop (𝓝 0) := by
  have hprime :
      Tendsto
        (fun N : ℕ => zetaPrimeOffDiagonalChannel N f)
        atTop
        (𝓝 (completedPrimeOffDiagonalChannel f)) :=
    zetaPrimeOffDiagonalChannel_tendsto_completedPrimeOffDiagonalChannel f
  have htail :
      Tendsto
        (fun N : ℕ =>
          zetaPrimeOffDiagonalChannel N f -
            completedPrimeOffDiagonalChannel f)
        atTop
        (𝓝 (completedPrimeOffDiagonalChannel f -
          completedPrimeOffDiagonalChannel f)) := by
    exact hprime.sub tendsto_const_nhds
  have hzero :
      completedPrimeOffDiagonalChannel f -
        completedPrimeOffDiagonalChannel f = 0 := by
    exact sub_self (completedPrimeOffDiagonalChannel f)
  unfold finitePartPrimeTail
  unfold finitePartPrimeOffDiagonalWindow
  exact Eq.subst
    (motive := fun x : ℝ =>
      Tendsto
        (fun N : ℕ =>
          zetaPrimeOffDiagonalChannel N f -
            completedPrimeOffDiagonalChannel f)
        atTop (𝓝 x))
    hzero
    htail

/-- The grouped prime-defect renormalized tail tends to zero. -/
theorem finitePartPrimeDefectRenormalizedTail_tendsto_zero
    (f : ZetaAdmissibleFunction) :
    Tendsto (fun N : ℕ => finitePartPrimeDefectRenormalizedTail N f) atTop (𝓝 0) := by
  have hprime : Tendsto (fun N : ℕ => finitePartPrimeTail N f) atTop (𝓝 0) :=
    finitePartPrimeTail_tendsto_zero f
  have hfun :
      (fun N : ℕ => finitePartPrimeDefectRenormalizedTail N f) =
        (fun N : ℕ => finitePartPrimeTail N f) := by
    funext N
    have hcancel :=
      finitePartPrimeDefectRenormalizedWindow_eq_primeOffDiagonalWindow N f
    unfold finitePartPrimeDefectRenormalizedTail
    unfold finitePartPrimeTail
    let P : ℝ := finitePartPrimeOffDiagonalWindow N f
    let D : ℝ := zetaPrimeDiagonalDebt N f
    let E : ℝ := finitePartDebtAbsorptionWindow N f
    let p : ℝ := completedPrimeOffDiagonalChannel f
    change (P + D + E) - completedPrimeDefectKernelRenormalizedChannel f = P - p
    have hrenorm :
        completedPrimeDefectKernelRenormalizedChannel f = p :=
      completedPrimeDefectKernelRenormalizedChannel_eq_primeOffDiagonalChannel f
    have hfinite : P + D + E = P := hcancel
    calc
      (P + D + E) - completedPrimeDefectKernelRenormalizedChannel f =
          P - completedPrimeDefectKernelRenormalizedChannel f := by
        exact congrArg
          (fun x : ℝ => x - completedPrimeDefectKernelRenormalizedChannel f)
          hfinite
      _ = P - p := by
        exact congrArg (fun x : ℝ => P - x) hrenorm
  exact Eq.subst
    (motive := fun u : ℕ → ℝ => Tendsto u atTop (𝓝 0))
    hfun.symm
    hprime

/-- In the current completed normalization the archimedean finite-part tail is identically
zero: the finite square channel is exactly the archimedean channel on the autocorrelation
probe. -/
theorem finitePartArchimedeanTail_eq_zero
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePartArchimedeanTail N f = 0 := by
  have harch :
      Complex.re (archimedeanBoundaryChannel (convolutionAutocorrelation f)) =
        zetaArchimedeanAutocorrelationSquareEnergy f := by
    unfold archimedeanBoundaryChannel
    exact zetaArchimedeanAutocorrelationChannel_eq_squareEnergy f
  unfold finitePartArchimedeanTail
  calc
    zetaArchimedeanAutocorrelationSquareEnergy f -
        Complex.re (archimedeanBoundaryChannel (convolutionAutocorrelation f)) =
        zetaArchimedeanAutocorrelationSquareEnergy f -
          zetaArchimedeanAutocorrelationSquareEnergy f := by
      exact congrArg
        (fun x : ℝ => zetaArchimedeanAutocorrelationSquareEnergy f - x)
        harch
    _ = 0 := by
      exact sub_self (zetaArchimedeanAutocorrelationSquareEnergy f)

/-- Archimedean finite-part tails tend to zero by the completed archimedean kernel bound and
integrable-tail convergence. -/
theorem finitePartArchimedeanTail_tendsto_zero
    (f : ZetaAdmissibleFunction) :
    Tendsto (fun N : ℕ => finitePartArchimedeanTail N f) atTop (𝓝 0) := by
  have hfun :
      (fun N : ℕ => finitePartArchimedeanTail N f) =
        (fun _N : ℕ => (0 : ℝ)) := by
    funext N
    exact finitePartArchimedeanTail_eq_zero N f
  exact Eq.subst
    (motive := fun u : ℕ → ℝ => Tendsto u atTop (𝓝 0))
    hfun.symm
    tendsto_const_nhds

/-- In the current completed normalization the correction finite-part tail is identically
zero: the correction square energy is the completed pole correction on the autocorrelation
probe.  Diagonal-debt absorption is handled by its own channel. -/
theorem finitePartCorrectionTail_eq_zero
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePartCorrectionTail N f = 0 := by
  have hcorr :
      Complex.re (poleBoundaryChannel (convolutionAutocorrelation f)) =
        zetaCorrectionAutocorrelationSquareEnergy f := by
    unfold poleBoundaryChannel
    exact zetaCorrectionAutocorrelationChannel_eq_squareEnergy f
  unfold finitePartCorrectionTail
  calc
    zetaCorrectionAutocorrelationSquareEnergy f -
        Complex.re (poleBoundaryChannel (convolutionAutocorrelation f)) =
        zetaCorrectionAutocorrelationSquareEnergy f -
          zetaCorrectionAutocorrelationSquareEnergy f := by
      exact congrArg
        (fun x : ℝ => zetaCorrectionAutocorrelationSquareEnergy f - x)
        hcorr
    _ = 0 := by
      exact sub_self (zetaCorrectionAutocorrelationSquareEnergy f)

/-- Correction finite-part tails tend to zero. -/
theorem finitePartCorrectionTail_tendsto_zero
    (f : ZetaAdmissibleFunction) :
    Tendsto (fun N : ℕ => finitePartCorrectionTail N f) atTop (𝓝 0) := by
  have hfun :
      (fun N : ℕ => finitePartCorrectionTail N f) =
        (fun _N : ℕ => (0 : ℝ)) := by
    funext N
    exact finitePartCorrectionTail_eq_zero N f
  exact Eq.subst
    (motive := fun u : ℕ → ℝ => Tendsto u atTop (𝓝 0))
    hfun.symm
    tendsto_const_nhds

/-- In the current completed normalization the residual completion tail is identically zero. -/
theorem finitePartPoleTail_eq_zero
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePartPoleTail N f = 0 := by
  have hcompletion :
      completionBoundaryChannel (convolutionAutocorrelation f) = 0 := by
    unfold completionBoundaryChannel
    rfl
  have hreal :
      Complex.re (completionBoundaryChannel (convolutionAutocorrelation f)) = 0 := by
    calc
      Complex.re (completionBoundaryChannel (convolutionAutocorrelation f)) =
          Complex.re 0 := by
        exact congrArg Complex.re hcompletion
      _ = 0 := by
        exact Complex.zero_re
  unfold finitePartPoleTail
  calc
    -Complex.re (completionBoundaryChannel (convolutionAutocorrelation f)) =
        -0 := by
      exact congrArg Neg.neg hreal
    _ = 0 := by
      exact neg_zero

/-- Pole/completion finite-part tails tend to zero by the pole-kernel tail estimate. -/
theorem finitePartPoleTail_tendsto_zero
    (f : ZetaAdmissibleFunction) :
    Tendsto (fun N : ℕ => finitePartPoleTail N f) atTop (𝓝 0) := by
  have hfun :
      (fun N : ℕ => finitePartPoleTail N f) =
        (fun _N : ℕ => (0 : ℝ)) := by
    funext N
    exact finitePartPoleTail_eq_zero N f
  exact Eq.subst
    (motive := fun u : ℕ → ℝ => Tendsto u atTop (𝓝 0))
    hfun.symm
    tendsto_const_nhds

/-- The explicit total finite-part tail tends to zero once its four named channel tails do. -/
theorem finitePartBoundaryTail_tendsto_zero
    (f : ZetaAdmissibleFunction) :
    Tendsto (fun N : ℕ => finitePartBoundaryTail N f) atTop (𝓝 0) := by
  have hprime :
      Tendsto (fun N : ℕ => finitePartPrimeDefectRenormalizedTail N f) atTop (𝓝 0) :=
    finitePartPrimeDefectRenormalizedTail_tendsto_zero f
  have harch : Tendsto (fun N : ℕ => finitePartArchimedeanTail N f) atTop (𝓝 0) :=
    finitePartArchimedeanTail_tendsto_zero f
  have hcorr : Tendsto (fun N : ℕ => finitePartCorrectionTail N f) atTop (𝓝 0) :=
    finitePartCorrectionTail_tendsto_zero f
  have hpole : Tendsto (fun N : ℕ => finitePartPoleTail N f) atTop (𝓝 0) :=
    finitePartPoleTail_tendsto_zero f
  have hprime_arch :
      Tendsto
        (fun N : ℕ =>
          finitePartPrimeDefectRenormalizedTail N f + finitePartArchimedeanTail N f)
        atTop (𝓝 (0 + 0)) := by
    exact hprime.add harch
  have hprime_arch_zero :
      Tendsto
        (fun N : ℕ =>
          finitePartPrimeDefectRenormalizedTail N f + finitePartArchimedeanTail N f)
        atTop (𝓝 0) := by
    exact Eq.subst
      (motive := fun x : ℝ =>
        Tendsto
          (fun N : ℕ =>
            finitePartPrimeDefectRenormalizedTail N f + finitePartArchimedeanTail N f)
          atTop (𝓝 x))
      (add_zero 0)
      hprime_arch
  have hthree :
      Tendsto
        (fun N : ℕ =>
          finitePartPrimeDefectRenormalizedTail N f + finitePartArchimedeanTail N f +
            finitePartCorrectionTail N f)
        atTop (𝓝 (0 + 0)) := by
    exact hprime_arch_zero.add hcorr
  have hthree_zero :
      Tendsto
        (fun N : ℕ =>
          finitePartPrimeDefectRenormalizedTail N f + finitePartArchimedeanTail N f +
            finitePartCorrectionTail N f)
        atTop (𝓝 0) := by
    exact Eq.subst
      (motive := fun x : ℝ =>
        Tendsto
          (fun N : ℕ =>
            finitePartPrimeDefectRenormalizedTail N f + finitePartArchimedeanTail N f +
              finitePartCorrectionTail N f)
          atTop (𝓝 x))
      (add_zero 0)
      hthree
  unfold finitePartBoundaryTail
  have hall :
      Tendsto
        (fun N : ℕ =>
          finitePartPrimeDefectRenormalizedTail N f + finitePartArchimedeanTail N f +
            finitePartCorrectionTail N f + finitePartPoleTail N f)
        atTop (𝓝 (0 + 0)) := by
    exact hthree_zero.add hpole
  exact Eq.subst
    (motive := fun x : ℝ =>
      Tendsto
        (fun N : ℕ =>
          finitePartPrimeDefectRenormalizedTail N f + finitePartArchimedeanTail N f +
            finitePartCorrectionTail N f + finitePartPoleTail N f)
        atTop (𝓝 x))
    (add_zero 0)
    hall

/-- The literal finite-part remainder tends to zero because the named tail certificate tends to
zero. -/
theorem finitePartBoundaryRemainder_tendsto_zero
    (f : ZetaAdmissibleFunction) :
    Tendsto (fun N : ℕ => finitePartBoundaryRemainder N f) atTop (𝓝 0) := by
  have htail : Tendsto (fun N : ℕ => finitePartBoundaryTail N f) atTop (𝓝 0) :=
    finitePartBoundaryTail_tendsto_zero f
  have hrem :
      (fun N : ℕ => finitePartBoundaryRemainder N f) =
        (fun N : ℕ => finitePartBoundaryTail N f) := by
    funext N
    exact finitePartBoundaryRemainder_eq_tail N f
  exact Eq.subst
    (motive := fun u : ℕ → ℝ => Tendsto u atTop (𝓝 0))
    hrem.symm
    htail

/-- The finite-part boundary window is the raw completed physical boundary window after the
finite diagonal debt has been added and cancelled inside the completed normalization. -/
theorem finitePartBoundaryWindow_eq_completedBoundaryWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePartBoundaryWindow N f =
      completedBoundaryWindow N f := by
  unfold finitePartBoundaryWindow
  unfold finitePartPrimeOffDiagonalWindow
  unfold finitePartArchimedeanCorrectionWindow
  unfold finitePartDebtAbsorptionWindow
  unfold completedBoundaryWindow
  unfold zetaCompletedPhysicalAutocorrelationBoundaryChannel
  unfold zetaArchimedeanCorrectionAutocorrelationChannel
  let P : ℝ := zetaPrimeOffDiagonalChannel N f
  let D : ℝ := zetaPrimeDiagonalDebt N f
  let A : ℝ := zetaArchimedeanCorrectionAutocorrelationChannel f
  have hcancel : D + -D = 0 := by
    exact add_neg_cancel D
  calc
    P + D + -D + A =
        P + (D + -D) + A := by
      exact congrArg (fun x : ℝ => x + A) (add_assoc P D (-D))
    _ = P + 0 + A := by
      exact congrArg (fun x : ℝ => P + x + A)
        hcancel
    _ = P + A := by
      exact congrArg (fun x : ℝ => x + A) (add_zero P)

/-- The positive corrected window plus its finite debt absorption is exactly the finite-part
boundary window. -/
theorem finitePositiveRenormalizedBoundaryWindow_eq_finitePartBoundaryWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePositiveRenormalizedBoundaryWindow N f =
      finitePartBoundaryWindow N f := by
  unfold finitePositiveRenormalizedBoundaryWindow
  unfold completedCorrectedBoundaryWindow
  unfold finitePartDebtAbsorptionWindow
  have hsub :
      completedBoundaryWindow N f + zetaPrimeDiagonalDebt N f +
          -zetaPrimeDiagonalDebt N f =
        completedBoundaryWindow N f + zetaPrimeDiagonalDebt N f -
          zetaPrimeDiagonalDebt N f := by
    exact (sub_eq_add_neg
      (completedBoundaryWindow N f + zetaPrimeDiagonalDebt N f)
      (zetaPrimeDiagonalDebt N f)).symm
  calc
    completedBoundaryWindow N f + zetaPrimeDiagonalDebt N f +
        -zetaPrimeDiagonalDebt N f =
        completedBoundaryWindow N f + zetaPrimeDiagonalDebt N f -
          zetaPrimeDiagonalDebt N f := hsub
    _ = completedBoundaryWindow N f := by
      exact completedBoundaryWindow_add_diagonalDebt_sub_diagonalDebt N f
    _ = finitePartBoundaryWindow N f := by
      exact (finitePartBoundaryWindow_eq_completedBoundaryWindow N f).symm

/-- The finite boundary weight object's square representative is the positive square-energy
window. -/
theorem finiteBoundaryWeightObject_squareRepresentative_eq_squareEnergyWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    FiniteBoundaryWeightObject.squareRepresentative
        (finiteBoundaryWeightObject N f) =
      finitePositiveSquareEnergyWindow N f := by
  rfl

/-- The square representative of the finite boundary weight object is nonnegative. -/
theorem finiteBoundaryWeightObject_squareRepresentative_nonnegative
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    0 ≤
      FiniteBoundaryWeightObject.squareRepresentative
        (finiteBoundaryWeightObject N f) := by
  unfold FiniteBoundaryWeightObject.squareRepresentative
  unfold finiteBoundaryWeightObject
  unfold finitePositiveSquareEnergyWindow
  unfold zetaCompletedPhysicalAutocorrelationSquareEnergy
  exact add_nonneg
    (zetaPrimeTranslationDefectEnergy_nonnegative N f)
    (zetaArchimedeanCorrectionAutocorrelationSquareEnergy_nonnegative f)

/-- The finite boundary weight object's finite-part representative is the finite-part
boundary window. -/
theorem finiteBoundaryWeightObject_finitePartRepresentative_eq_finitePartBoundaryWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    FiniteBoundaryWeightObject.finitePartRepresentative
        (finiteBoundaryWeightObject N f) =
      finitePartBoundaryWindow N f := by
  rfl

/-- The finite boundary weight object's absorbed square representative is the positive
renormalized boundary window. -/
theorem finiteBoundaryWeightObject_absorbedSquareRepresentative_eq_renormalizedWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    FiniteBoundaryWeightObject.absorbedSquareRepresentative
        (finiteBoundaryWeightObject N f) =
      finitePositiveRenormalizedBoundaryWindow N f := by
  unfold FiniteBoundaryWeightObject.absorbedSquareRepresentative
  unfold finiteBoundaryWeightObject
  unfold finitePositiveRenormalizedBoundaryWindow
  have hcorrected :
      completedCorrectedBoundaryWindow N f =
        finitePositiveSquareEnergyWindow N f :=
    completedCorrectedBoundaryWindow_eq_finitePositiveSquareEnergyWindow N f
  calc
    finitePositiveSquareEnergyWindow N f + finitePartDebtAbsorptionWindow N f =
        completedCorrectedBoundaryWindow N f + finitePartDebtAbsorptionWindow N f := by
      exact congrArg
        (fun x : ℝ => x + finitePartDebtAbsorptionWindow N f)
        hcorrected.symm

/-- The diagonal debt and its absorption channel cancel inside the finite boundary weight
object. -/
theorem finiteBoundaryWeightObject_debt_absorption_cancel
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (finiteBoundaryWeightObject N f).diagonalDebt +
        (finiteBoundaryWeightObject N f).debtAbsorption =
      0 := by
  unfold finiteBoundaryWeightObject
  unfold finitePartDebtAbsorptionWindow
  exact add_neg_cancel (zetaPrimeDiagonalDebt N f)

/-- The concrete finite lower-weight exact representative is zero. -/
theorem finiteBoundaryWeightObject_lowerWeightExactRepresentative_eq_zero
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    FiniteBoundaryWeightObject.lowerWeightExactRepresentative
        (finiteBoundaryWeightObject N f) =
      0 := by
  unfold FiniteBoundaryWeightObject.lowerWeightExactRepresentative
  exact finiteBoundaryWeightObject_debt_absorption_cancel N f

/-- The finite absorption channel is the negative face of the finite diagonal debt. -/
theorem finiteBoundaryWeightObject_debtAbsorption_eq_neg_diagonalDebt
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (finiteBoundaryWeightObject N f).debtAbsorption =
      - (finiteBoundaryWeightObject N f).diagonalDebt := by
  unfold finiteBoundaryWeightObject
  unfold finitePartDebtAbsorptionWindow
  rfl

/-- The absorbed square representative equals the finite-part representative.  This is the
finite triangular transport identity: the positive square is transported to the finite-part
window by adding the lower-weight debt absorption channel. -/
theorem finiteBoundaryWeightObject_absorbedSquare_eq_finitePartRepresentative
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    FiniteBoundaryWeightObject.absorbedSquareRepresentative
        (finiteBoundaryWeightObject N f) =
      FiniteBoundaryWeightObject.finitePartRepresentative
        (finiteBoundaryWeightObject N f) := by
  exact
    (finiteBoundaryWeightObject_absorbedSquareRepresentative_eq_renormalizedWindow
      N f).trans
      ((finitePositiveRenormalizedBoundaryWindow_eq_finitePartBoundaryWindow N f).trans
        (finiteBoundaryWeightObject_finitePartRepresentative_eq_finitePartBoundaryWindow
          N f).symm)

/-- Weight-triangular transport at a finite cutoff: adding the absorption face to the positive
square representative gives the finite-part representative. -/
theorem finiteBoundaryWeightObject_weightTriangularTransport
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    FiniteBoundaryWeightObject.squareRepresentative
        (finiteBoundaryWeightObject N f) +
      (finiteBoundaryWeightObject N f).debtAbsorption =
    FiniteBoundaryWeightObject.finitePartRepresentative
        (finiteBoundaryWeightObject N f) := by
  exact finiteBoundaryWeightObject_absorbedSquare_eq_finitePartRepresentative N f

/-- The finite triangular transport may equivalently replace the diagonal face by its
lower-weight exact absorption partner. -/
theorem finiteBoundaryWeightObject_square_add_neg_diagonalDebt_eq_finitePartRepresentative
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    FiniteBoundaryWeightObject.squareRepresentative
        (finiteBoundaryWeightObject N f) -
      (finiteBoundaryWeightObject N f).diagonalDebt =
    FiniteBoundaryWeightObject.finitePartRepresentative
        (finiteBoundaryWeightObject N f) := by
  have habs :
      (finiteBoundaryWeightObject N f).debtAbsorption =
        - (finiteBoundaryWeightObject N f).diagonalDebt :=
    finiteBoundaryWeightObject_debtAbsorption_eq_neg_diagonalDebt N f
  calc
    FiniteBoundaryWeightObject.squareRepresentative
        (finiteBoundaryWeightObject N f) -
      (finiteBoundaryWeightObject N f).diagonalDebt =
        FiniteBoundaryWeightObject.squareRepresentative
          (finiteBoundaryWeightObject N f) +
        - (finiteBoundaryWeightObject N f).diagonalDebt := by
      exact sub_eq_add_neg
        (FiniteBoundaryWeightObject.squareRepresentative
          (finiteBoundaryWeightObject N f))
        ((finiteBoundaryWeightObject N f).diagonalDebt)
    _ =
        FiniteBoundaryWeightObject.squareRepresentative
          (finiteBoundaryWeightObject N f) +
        (finiteBoundaryWeightObject N f).debtAbsorption := by
      exact congrArg
        (fun x : ℝ =>
          FiniteBoundaryWeightObject.squareRepresentative
            (finiteBoundaryWeightObject N f) + x)
        habs.symm
    _ =
        FiniteBoundaryWeightObject.finitePartRepresentative
          (finiteBoundaryWeightObject N f) := by
      exact finiteBoundaryWeightObject_weightTriangularTransport N f

/-- The concrete lower-weight absorption certificate for the finite boundary weight object. -/
def finiteBoundaryWeightObject_lowerWeightAbsorptionCert
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    FiniteBoundaryLowerWeightAbsorptionCert (finiteBoundaryWeightObject N f) :=
  { debt_absorption_cancel :=
      finiteBoundaryWeightObject_debt_absorption_cancel N f
    absorbed_square_eq_finitePart :=
      finiteBoundaryWeightObject_absorbedSquare_eq_finitePartRepresentative N f }

/-- The finite diagonal-debt absorption defect: the difference between the absorbed positive
window and the original positive square-energy window. -/
def finiteDiagonalDebtAbsorptionDefect
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  finitePositiveRenormalizedBoundaryWindow N f -
    finitePositiveSquareEnergyWindow N f

/-- The finite absorption defect is exactly the finite debt-absorption channel. -/
theorem finiteDiagonalDebtAbsorptionDefect_eq_finitePartDebtAbsorptionWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finiteDiagonalDebtAbsorptionDefect N f =
      finitePartDebtAbsorptionWindow N f := by
  unfold finiteDiagonalDebtAbsorptionDefect
  unfold finitePositiveRenormalizedBoundaryWindow
  let Q : ℝ := finitePositiveSquareEnergyWindow N f
  let A : ℝ := finitePartDebtAbsorptionWindow N f
  have hcorrected :
      completedCorrectedBoundaryWindow N f = Q := by
    exact completedCorrectedBoundaryWindow_eq_finitePositiveSquareEnergyWindow N f
  change (completedCorrectedBoundaryWindow N f + A) - Q = A
  calc
    (completedCorrectedBoundaryWindow N f + A) - Q =
        (Q + A) - Q := by
      exact congrArg (fun x : ℝ => (x + A) - Q) hcorrected
    _ = (Q + A) + -Q := by
      exact sub_eq_add_neg (Q + A) Q
    _ = (A + Q) + -Q := by
      exact congrArg (fun x : ℝ => x + -Q) (add_comm Q A)
    _ = A + (Q + -Q) := by
      exact add_assoc A Q (-Q)
    _ = A + 0 := by
      exact congrArg (fun x : ℝ => A + x) (add_neg_cancel Q)
    _ = A := by
      exact add_zero A

/-- The completed corrected boundary window is nonnegative. -/
theorem completedCorrectedBoundaryWindow_nonnegative
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    0 ≤ completedCorrectedBoundaryWindow N f := by
  unfold completedCorrectedBoundaryWindow
  exact zetaCompletedPhysicalAutocorrelationBoundaryChannel_add_diagonalDebt_nonnegative N f

/-- Finite-part convergence to the completed physical finite-part boundary channel. This is the
genuine completed-normalization theorem before comparison with the explicit-formula boundary
functional. -/
theorem finitePartBoundaryWindow_tendsto_completedFinitePartBoundaryChannel
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ => finitePartBoundaryWindow N f)
      atTop
      (𝓝 (completedFinitePartBoundaryChannel f)) := by
  let c : ℝ := completedFinitePartBoundaryChannel f
  have hrem :
      Tendsto (fun N : ℕ => finitePartBoundaryRemainder N f) atTop (𝓝 0) :=
    finitePartBoundaryRemainder_tendsto_zero f
  have hsum :
      Tendsto
        (fun N : ℕ => c + finitePartBoundaryRemainder N f)
        atTop
        (𝓝 (c + 0)) := by
    exact (tendsto_const_nhds.add hrem)
  have htarget : c + 0 = c := by
    exact add_zero c
  have hfinite :
      (fun N : ℕ => finitePartBoundaryWindow N f) =
      (fun N : ℕ => c + finitePartBoundaryRemainder N f) := by
    funext N
    exact finitePartBoundaryWindow_eq_boundaryChannel_add_remainder N f
  exact Eq.subst
    (motive := fun u : ℕ → ℝ => Tendsto u atTop (𝓝 c))
    hfinite.symm
    (Eq.subst
      (motive := fun x : ℝ =>
        Tendsto (fun N : ℕ => c + finitePartBoundaryRemainder N f) atTop (𝓝 x))
      htarget
      hsum)

/-- The completed physical finite-part channel is the real explicit-formula completed boundary
channel on the convolution-autocorrelation probe.  This is the owner bridge between the
renormalized square-energy completion and the explicit-formula boundary functional. -/
theorem completedFinitePartBoundaryChannel_eq_completedBoundaryChannel
    (f : ZetaAdmissibleFunction) :
    completedFinitePartBoundaryChannel f =
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) := by
  let g : ZetaAdmissibleFunction := convolutionAutocorrelation f
  have hprime :
      completedPrimeOffDiagonalChannel f =
        Complex.re (primeBoundaryChannel g) := by
    unfold g
    exact completedPrimeOffDiagonalChannel_eq_primeBoundaryChannel f
  have harch :
      zetaArchimedeanAutocorrelationSquareEnergy f =
        Complex.re (archimedeanBoundaryChannel g) := by
    unfold g
    unfold archimedeanBoundaryChannel
    exact (zetaArchimedeanAutocorrelationChannel_eq_squareEnergy f).symm
  have hcorr :
      zetaCorrectionAutocorrelationSquareEnergy f =
        Complex.re (poleBoundaryChannel g) := by
    unfold g
    unfold poleBoundaryChannel
    exact (zetaCorrectionAutocorrelationChannel_eq_squareEnergy f).symm
  have hcompletion :
      Complex.re (completionBoundaryChannel g) = 0 := by
    unfold g
    unfold completionBoundaryChannel
    exact Complex.zero_re
  have hboundary :
      Complex.re (completedBoundaryChannel g) =
        Complex.re (primeBoundaryChannel g) +
          Complex.re (archimedeanBoundaryChannel g) +
          Complex.re (poleBoundaryChannel g) +
          Complex.re (completionBoundaryChannel g) := by
    have hdecomp :
        completedBoundaryChannel g =
          primeBoundaryChannel g +
            archimedeanBoundaryChannel g +
            poleBoundaryChannel g +
            completionBoundaryChannel g :=
      completedBoundaryChannel_eq_prime_add_archimedean_add_pole_add_completion g
    calc
      Complex.re (completedBoundaryChannel g) =
          Complex.re
            (primeBoundaryChannel g +
              archimedeanBoundaryChannel g +
              poleBoundaryChannel g +
              completionBoundaryChannel g) := by
        exact congrArg Complex.re hdecomp
      _ =
          Complex.re
              (primeBoundaryChannel g +
                archimedeanBoundaryChannel g +
                poleBoundaryChannel g) +
            Complex.re (completionBoundaryChannel g) := by
        exact Complex.add_re
          (primeBoundaryChannel g +
            archimedeanBoundaryChannel g +
            poleBoundaryChannel g)
          (completionBoundaryChannel g)
      _ =
          (Complex.re (primeBoundaryChannel g + archimedeanBoundaryChannel g) +
              Complex.re (poleBoundaryChannel g)) +
            Complex.re (completionBoundaryChannel g) := by
        exact congrArg
          (fun x : ℝ => x + Complex.re (completionBoundaryChannel g))
          (Complex.add_re
            (primeBoundaryChannel g + archimedeanBoundaryChannel g)
            (poleBoundaryChannel g))
      _ =
          ((Complex.re (primeBoundaryChannel g) +
              Complex.re (archimedeanBoundaryChannel g)) +
            Complex.re (poleBoundaryChannel g)) +
            Complex.re (completionBoundaryChannel g) := by
        exact congrArg
          (fun x : ℝ =>
            (x + Complex.re (poleBoundaryChannel g)) +
              Complex.re (completionBoundaryChannel g))
          (Complex.add_re (primeBoundaryChannel g) (archimedeanBoundaryChannel g))
      _ =
          Complex.re (primeBoundaryChannel g) +
            Complex.re (archimedeanBoundaryChannel g) +
            Complex.re (poleBoundaryChannel g) +
            Complex.re (completionBoundaryChannel g) := by
        rfl
  unfold completedFinitePartBoundaryChannel
  calc
    completedPrimeOffDiagonalChannel f +
        zetaArchimedeanAutocorrelationSquareEnergy f +
        zetaCorrectionAutocorrelationSquareEnergy f =
        Complex.re (primeBoundaryChannel g) +
          Complex.re (archimedeanBoundaryChannel g) +
          Complex.re (poleBoundaryChannel g) := by
      exact congrArg₂ (fun x y : ℝ => x + y)
        (congrArg₂ (fun x y : ℝ => x + y) hprime harch)
        hcorr
    _ =
        Complex.re (primeBoundaryChannel g) +
          Complex.re (archimedeanBoundaryChannel g) +
          Complex.re (poleBoundaryChannel g) +
          0 := by
      exact (add_zero
        (Complex.re (primeBoundaryChannel g) +
          Complex.re (archimedeanBoundaryChannel g) +
          Complex.re (poleBoundaryChannel g))).symm
    _ =
        Complex.re (primeBoundaryChannel g) +
          Complex.re (archimedeanBoundaryChannel g) +
          Complex.re (poleBoundaryChannel g) +
          Complex.re (completionBoundaryChannel g) := by
      exact congrArg
        (fun x : ℝ =>
          Complex.re (primeBoundaryChannel g) +
            Complex.re (archimedeanBoundaryChannel g) +
            Complex.re (poleBoundaryChannel g) + x)
        hcompletion.symm
    _ = Complex.re (completedBoundaryChannel g) := by
      exact hboundary.symm

/-- Finite-part convergence to the completed boundary channel. This is the genuine completed
normalization theorem: diagonal debt cancellation has already happened inside
`finitePartBoundaryWindow`, so no separate convergence of the raw prime window is asserted. -/
theorem finitePartBoundaryWindow_tendsto_boundaryChannel
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ => finitePartBoundaryWindow N f)
      atTop
      (𝓝 (Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)))) := by
  have hfinite :
      Tendsto
        (fun N : ℕ => finitePartBoundaryWindow N f)
        atTop
        (𝓝 (completedFinitePartBoundaryChannel f)) :=
    finitePartBoundaryWindow_tendsto_completedFinitePartBoundaryChannel f
  exact Eq.subst
    (motive := fun x : ℝ =>
      Tendsto (fun N : ℕ => finitePartBoundaryWindow N f) atTop (𝓝 x))
    (completedFinitePartBoundaryChannel_eq_completedBoundaryChannel f)
    hfinite

/-- The finite positive square-energy windows, after finite diagonal-debt absorption, converge
to the completed boundary channel.  This is pure assembly: the absorption-renormalized positive
window is the finite-part window, and the finite-part window has the tail convergence
certificate above. -/
theorem finitePositiveRenormalizedBoundaryWindow_tendsto_boundaryChannel
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ => finitePositiveRenormalizedBoundaryWindow N f)
      atTop
      (𝓝 (Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)))) := by
  have hfinite :
      (fun N : ℕ => finitePositiveRenormalizedBoundaryWindow N f) =
        (fun N : ℕ => finitePartBoundaryWindow N f) := by
    funext N
    exact finitePositiveRenormalizedBoundaryWindow_eq_finitePartBoundaryWindow N f
  exact Eq.subst
    (motive := fun u : ℕ → ℝ =>
      Tendsto u atTop
        (𝓝 (Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)))))
    hfinite.symm
    (finitePartBoundaryWindow_tendsto_boundaryChannel f)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
