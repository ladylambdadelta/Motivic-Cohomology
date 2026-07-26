import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaCompletedWeightStream.ZetaCompletedFinitePart.OwnerParts.Part01

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

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
end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
