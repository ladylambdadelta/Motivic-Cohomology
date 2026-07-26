import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaCompletedWeightStream.ZetaCompletedFinitePart.ZetaCompletedSquareLedger.OwnerParts.Part02

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

open Filter
open ZetaPrimePowerIndex

def completedCorrectedBoundaryWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  completedBoundaryWindow N f + zetaPrimeDiagonalDebt N f

/-- The finite positive square-energy window after adding diagonal debt.  This object is used
for positivity; it is not itself the renormalized finite-part distribution unless the diagonal
debt has also been cancelled by a completed normalization channel. -/
def finitePositiveSquareEnergyWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  zetaCompletedPhysicalAutocorrelationSquareEnergy N f

/-- The prime off-diagonal finite-part window.  This is the prime channel after diagonal debt
has been removed from the finite-part distribution. -/
def finitePartPrimeOffDiagonalWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  zetaPrimeOffDiagonalChannel N f

/-- The finite diagonal-debt absorption channel. This is deliberately separate from the
archimedean and correction channels: it is the normalization channel that cancels the diagonal
part of the prime defect square after the positive prime kernel has been expanded. -/
def finitePartDebtAbsorptionWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  - zetaPrimeDiagonalDebt N f

/-- Backwards-compatible name for the finite diagonal-debt absorption channel. -/
def finitePartDiagonalDebtCancellationWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  finitePartDebtAbsorptionWindow N f

/-- The archimedean/correction finite channel.  Diagonal-debt absorption is not hidden here;
it is a separate normalization channel. -/
def finitePartArchimedeanCorrectionWindow
    (_N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  zetaArchimedeanCorrectionAutocorrelationChannel f

/-- The positive square-energy window after applying the finite diagonal-debt absorption
normalization.  This is the bridge object between finite positivity and the finite-part
completed boundary window. -/
def finitePositiveRenormalizedBoundaryWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  completedCorrectedBoundaryWindow N f +
    finitePartDebtAbsorptionWindow N f

/-- The completed prime off-diagonal finite-part channel. -/
noncomputable def completedPrimeOffDiagonalChannel
    (f : ZetaAdmissibleFunction) : ℝ :=
  zetaCompletedPrimeOffDiagonalChannel f

/-- The completed prime finite-part channel obtained after finite diagonal-debt cancellation.

There is no standalone completed diagonal-debt summand here: the finite debt and finite
absorption terms cancel before taking the completed prime finite-part limit. -/
noncomputable def completedPrimeDefectKernelRenormalizedChannel
    (f : ZetaAdmissibleFunction) : ℝ :=
  completedPrimeOffDiagonalChannel f

/-- Diagonal debt cancellation is algebraic and happens before taking the finite-part limit. -/
theorem completedBoundaryWindow_add_diagonalDebt_sub_diagonalDebt
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    completedBoundaryWindow N f + zetaPrimeDiagonalDebt N f -
        zetaPrimeDiagonalDebt N f =
      completedBoundaryWindow N f := by
  have hcancel :
      zetaPrimeDiagonalDebt N f + -zetaPrimeDiagonalDebt N f = 0 := by
    exact add_neg_cancel (zetaPrimeDiagonalDebt N f)
  calc
    completedBoundaryWindow N f + zetaPrimeDiagonalDebt N f -
        zetaPrimeDiagonalDebt N f =
        completedBoundaryWindow N f + zetaPrimeDiagonalDebt N f +
          -zetaPrimeDiagonalDebt N f := by
      exact sub_eq_add_neg
        (completedBoundaryWindow N f + zetaPrimeDiagonalDebt N f)
        (zetaPrimeDiagonalDebt N f)
    _ =
        completedBoundaryWindow N f +
          (zetaPrimeDiagonalDebt N f + -zetaPrimeDiagonalDebt N f) := by
      exact add_assoc
        (completedBoundaryWindow N f)
        (zetaPrimeDiagonalDebt N f)
        (-zetaPrimeDiagonalDebt N f)
    _ = completedBoundaryWindow N f + 0 := by
      exact congrArg (fun x : ℝ => completedBoundaryWindow N f + x) hcancel
    _ = completedBoundaryWindow N f := by
      exact add_zero (completedBoundaryWindow N f)

/-- The prime off-diagonal coordinates are summable against the completed prime-power weights.
This is the exact admissibility/decay input needed for the completed prime finite-part limit. -/
theorem summable_primeOffDiagonalCoordinate
    (f : ZetaAdmissibleFunction) :
    Summable (fun ι : ZetaPrimePowerIndex =>
      zetaPrimeOffDiagonalCoordinate ι f) := by
  exact summable_zetaPrimeOffDiagonalCoordinate f

/-- The growing finite prime off-diagonal windows converge to the completed prime off-diagonal
channel.  This is the window-exhaustion theorem built from prime weighted-kernel summability
and the completed-prime realization theorem. -/
theorem zetaPrimeOffDiagonalChannel_tendsto_completedPrimeOffDiagonalChannel
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ => zetaPrimeOffDiagonalChannel N f)
      atTop
      (nhds (completedPrimeOffDiagonalChannel f)) := by
  unfold completedPrimeOffDiagonalChannel
  exact zetaPrimeOffDiagonalChannel_tendsto_completed f

/-- Debt and debt-absorption cancel in each finite prime-defect renormalized window. -/
theorem finitePartPrimeDefectRenormalizedWindow_eq_primeOffDiagonalWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePartPrimeOffDiagonalWindow N f +
        zetaPrimeDiagonalDebt N f +
        finitePartDebtAbsorptionWindow N f =
      finitePartPrimeOffDiagonalWindow N f := by
  unfold finitePartDebtAbsorptionWindow
  let P : ℝ := finitePartPrimeOffDiagonalWindow N f
  let D : ℝ := zetaPrimeDiagonalDebt N f
  change P + D + -D = P
  have hcancel : D + -D = 0 := by
    exact add_neg_cancel D
  calc
    P + D + -D = P + (D + -D) := by
      exact add_assoc P D (-D)
    _ = P + 0 := by
      exact congrArg (fun x : ℝ => P + x) hcancel
    _ = P := by
      exact add_zero P

/-- The absorbed finite prime defect-square window is exactly the finite prime
off-diagonal window.

This is the prime-only triangular transport: the positive translation-defect square expands
as off-diagonal plus diagonal debt, and the finite lower-weight absorption channel cancels
that diagonal debt before any completed limit is taken. -/
theorem zetaPrimeTranslationDefectEnergy_add_debtAbsorption_eq_offDiagonal
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    zetaPrimeTranslationDefectEnergy N f +
        finitePartDebtAbsorptionWindow N f =
      zetaPrimeOffDiagonalChannel N f := by
  let P : ℝ := zetaPrimeOffDiagonalChannel N f
  let D : ℝ := zetaPrimeDiagonalDebt N f
  let Q : ℝ := zetaPrimeTranslationDefectEnergy N f
  have hsquare : P + D = Q :=
    zetaPrimeOffDiagonal_add_diagonalDebt_eq_translationDefectEnergy N f
  have hcancel : D + -D = 0 := by
    exact add_neg_cancel D
  unfold finitePartDebtAbsorptionWindow
  calc
    Q + -D = (P + D) + -D := by
      exact congrArg (fun x : ℝ => x + -D) hsquare.symm
    _ = P + (D + -D) := by
      exact add_assoc P D (-D)
    _ = P + 0 := by
      exact congrArg (fun x : ℝ => P + x) hcancel
    _ = P := by
      exact add_zero P

/-- The absorbed finite prime defect-square windows converge to the completed prime
off-diagonal channel.

This is the prime-only finite-window limit supplied by the square-ledger owner.  It keeps the
positive square and the lower-weight absorption visible, rather than replacing them by a
pointwise physical/spectral equality. -/
theorem zetaPrimeTranslationDefectEnergy_add_debtAbsorption_tendsto_completedPrimeOffDiagonalChannel
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ =>
        zetaPrimeTranslationDefectEnergy N f +
          finitePartDebtAbsorptionWindow N f)
      atTop
      (nhds (completedPrimeOffDiagonalChannel f)) := by
  have hwindow :
      (fun N : ℕ =>
        zetaPrimeTranslationDefectEnergy N f +
          finitePartDebtAbsorptionWindow N f) =
        (fun N : ℕ => zetaPrimeOffDiagonalChannel N f) := by
    exact funext
      (fun N : ℕ =>
        zetaPrimeTranslationDefectEnergy_add_debtAbsorption_eq_offDiagonal N f)
  exact Eq.subst
    (motive := fun u : ℕ → ℝ =>
      Tendsto u atTop (nhds (completedPrimeOffDiagonalChannel f)))
    hwindow.symm
    (zetaPrimeOffDiagonalChannel_tendsto_completedPrimeOffDiagonalChannel f)

/-- The completed renormalized prime-defect package is exactly the completed prime
off-diagonal finite part. -/
theorem completedPrimeDefectKernelRenormalizedChannel_eq_primeOffDiagonalChannel
    (f : ZetaAdmissibleFunction) :
    completedPrimeDefectKernelRenormalizedChannel f =
      completedPrimeOffDiagonalChannel f := by
  rfl

/-- The completed corrected boundary window is the finite completed square energy. -/
theorem completedCorrectedBoundaryWindow_eq_squareEnergy
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    completedCorrectedBoundaryWindow N f =
      zetaCompletedPhysicalAutocorrelationSquareEnergy N f := by
  unfold completedCorrectedBoundaryWindow
  unfold completedBoundaryWindow
  exact zetaCompletedPhysicalAutocorrelationBoundaryChannel_add_diagonalDebt_eq_squareEnergy N f

/-- The completed corrected boundary window is the finite positive square-energy window. -/
theorem completedCorrectedBoundaryWindow_eq_finitePositiveSquareEnergyWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    completedCorrectedBoundaryWindow N f =
      finitePositiveSquareEnergyWindow N f := by
  unfold finitePositiveSquareEnergyWindow
  exact completedCorrectedBoundaryWindow_eq_squareEnergy N f

/-- The finite positive square-energy window is nonnegative. -/
theorem finitePositiveSquareEnergyWindow_nonnegative
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    0 ≤ finitePositiveSquareEnergyWindow N f := by
  unfold finitePositiveSquareEnergyWindow
  unfold zetaCompletedPhysicalAutocorrelationSquareEnergy
  exact add_nonneg
    (zetaPrimeTranslationDefectEnergy_nonnegative N f)
    (zetaArchimedeanCorrectionAutocorrelationSquareEnergy_nonnegative f)

/-- A real limit of nonnegative finite windows is nonnegative. -/
theorem nonnegative_of_tendsto_nonnegative_owner
    {u : ℕ → ℝ} {x : ℝ}
    (hu : Tendsto u atTop (nhds x))
    (hnonneg : ∀ N : ℕ, 0 ≤ u N) :
    0 ≤ x := by
  have hclosed : IsClosed (Set.Ici (0 : ℝ)) :=
    isClosed_Ici
  have heventually : ∀ᶠ N in atTop, u N ∈ Set.Ici (0 : ℝ) :=
    Filter.Eventually.of_forall
      (fun N : ℕ => hnonneg N)
  exact hclosed.mem_of_tendsto hu heventually

/-- A real limit of an everywhere nonnegative sequence is nonnegative. -/
theorem nonnegative_of_tendsto_nonnegative
    {u : ℕ → ℝ} {x : ℝ}
    (hu : Tendsto u atTop (nhds x))
    (hnonneg : ∀ N : ℕ, 0 ≤ u N) :
    0 ≤ x := by
  have hclosed : IsClosed (Set.Ici (0 : ℝ)) :=
    isClosed_Ici
  have heventually : ∀ᶠ N in atTop, u N ∈ Set.Ici (0 : ℝ) :=
    Filter.Eventually.of_forall
      (fun N : ℕ => hnonneg N)
  exact hclosed.mem_of_tendsto hu heventually

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
