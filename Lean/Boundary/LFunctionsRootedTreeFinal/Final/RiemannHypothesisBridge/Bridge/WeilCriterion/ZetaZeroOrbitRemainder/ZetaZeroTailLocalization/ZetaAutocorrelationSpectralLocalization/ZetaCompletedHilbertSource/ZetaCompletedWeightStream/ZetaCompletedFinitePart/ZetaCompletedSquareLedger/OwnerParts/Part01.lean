import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaCompletedWeightStream.ZetaCompletedFinitePart.ZetaCompletedSquareLedger.ZetaAutocorrelationHilbert.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.ZetaPrimePowerWindow.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.ConvolutionChannels
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaPacketComparison.ZetaCompletionCorrection.Owner

/-!
# Boundary completed-square ledger

This file owns the completed-square bookkeeping for the autocorrelation route.
It separates the raw prime off-diagonal channel from the diagonal debt and the
post-completion square terms.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

open Filter
open ZetaPrimePowerIndex

/-- Scalar distribution for one completed-square coordinate. -/
theorem zetaPrimeSquareLedger_scalar_distrib
    (w A B R : ℝ) :
    -(2 * w * R) + w * (A + B) =
      w * (A + B - 2 * R) := by
  have hmul : 2 * w * R = w * (2 * R) := by
    calc
      2 * w * R = (2 * w) * R := by
        rfl
      _ = (w * 2) * R := by
        exact congrArg (fun x : ℝ => x * R) (mul_comm 2 w)
      _ = w * (2 * R) := by
        exact mul_assoc w 2 R
  have hneg : -(2 * w * R) = -(w * (2 * R)) :=
    congrArg (fun x : ℝ => -x) hmul
  calc
    -(2 * w * R) + w * (A + B) =
        w * (A + B) + -(2 * w * R) := by
      exact add_comm (-(2 * w * R)) (w * (A + B))
    _ = w * (A + B) + -(w * (2 * R)) := by
      exact congrArg (fun x : ℝ => w * (A + B) + x) hneg
    _ = w * (A + B) + w * (-(2 * R)) := by
      exact congrArg (fun x : ℝ => w * (A + B) + x)
        (mul_neg w (2 * R)).symm
    _ = w * ((A + B) + -(2 * R)) := by
      exact (mul_add w (A + B) (-(2 * R))).symm
    _ = w * (A + B - 2 * R) := by
      exact congrArg (fun x : ℝ => w * x)
        (sub_eq_add_neg (A + B) (2 * R)).symm

/-- Adding the auxiliary residual back to its debt recovers the original channel. -/
theorem zetaBoundaryDebt_add_sub_cancel
    (A D : ℝ) :
    A = D + (A - D) := by
  have hright : D + (A - D) = A := by
    calc
      D + (A - D) = D + (A + -D) := by
        exact congrArg (fun x : ℝ => D + x) (sub_eq_add_neg A D)
      _ = (D + A) + -D := by
        exact (add_assoc D A (-D)).symm
      _ = (A + D) + -D := by
        exact congrArg (fun x : ℝ => x + -D) (add_comm D A)
      _ = A + (D + -D) := by
        exact add_assoc A D (-D)
      _ = A + 0 := by
        exact congrArg (fun x : ℝ => A + x) (add_neg_cancel D)
      _ = A := by
        exact add_zero A
  exact hright.symm

/-- The completed-square ledger rebrackets prime, debt, and auxiliary terms. -/
theorem zetaPrimeOffDiagonal_archimedeanDebt_rebracket
    (P D E : ℝ) :
    P + (D + E) = (P + D) + E := by
  exact (add_assoc P D E).symm

/-- The physical prime off-diagonal coordinate produced by the autocorrelation kernel. -/
def zetaPrimeOffDiagonalCoordinate
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℝ :=
  - (2 * ι.weight *
      Complex.re (zetaSeedInner (zetaTranslate ι.center f) f))

/-- Non-genuine prime-power indices contribute zero to the off-diagonal coordinate. -/
theorem zetaPrimeOffDiagonalCoordinate_eq_zero_of_not_isGenuine
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction)
    (hι : ¬ ZetaPrimePowerIndex.IsGenuine ι) :
    zetaPrimeOffDiagonalCoordinate ι f = 0 := by
  have hweight : ι.weight = 0 :=
    ZetaPrimePowerIndex.weight_eq_zero_of_not_isGenuine ι hι
  unfold zetaPrimeOffDiagonalCoordinate
  calc
    -(2 * ι.weight *
        Complex.re (zetaSeedInner (zetaTranslate ι.center f) f)) =
        -(2 * 0 *
          Complex.re (zetaSeedInner (zetaTranslate ι.center f) f)) := by
      exact congrArg
        (fun x : ℝ =>
          -(2 * x * Complex.re (zetaSeedInner (zetaTranslate ι.center f) f)))
        hweight
    _ = 0 := by
      calc
        -(2 * 0 *
            Complex.re (zetaSeedInner (zetaTranslate ι.center f) f)) =
            -(0 *
              Complex.re (zetaSeedInner (zetaTranslate ι.center f) f)) := by
          exact congrArg
            (fun x : ℝ =>
              -(x * Complex.re (zetaSeedInner (zetaTranslate ι.center f) f)))
            (mul_zero 2)
        _ = -0 := by
          exact congrArg Neg.neg
            (zero_mul (Complex.re (zetaSeedInner (zetaTranslate ι.center f) f)))
        _ = 0 := by
          exact neg_zero

/-- Compact support of the autocorrelation kernel gives an upper support bound. -/
theorem exists_convolutionAutocorrelationKernelSupportUpperBound
    (f : ZetaAdmissibleFunction) :
    ∃ B : ℝ, ∀ a ∈ tsupport (convolutionAutocorrelationKernel f), a ≤ B := by
  obtain ⟨B, hB⟩ :=
    IsCompact.bddAbove (convolutionAutocorrelationKernel_hasCompactSupport f).isCompact
  exact ⟨B, hB⟩

/-- The autocorrelation kernel vanishes strictly to the right of its compact-support bound. -/
theorem convolutionAutocorrelationKernel_eq_zero_of_supportUpperBound_lt
    (f : ZetaAdmissibleFunction) {B a : ℝ}
    (hB : ∀ x ∈ tsupport (convolutionAutocorrelationKernel f), x ≤ B)
    (ha : B < a) :
    convolutionAutocorrelationKernel f a = 0 := by
  have hnot_mem : a ∉ tsupport (convolutionAutocorrelationKernel f) := by
    intro hmem
    have hle : a ≤ B := hB a hmem
    exact (not_lt_of_ge hle) ha
  exact image_eq_zero_of_nmem_tsupport hnot_mem

/-- Prime off-diagonal coordinates vanish after the autocorrelation support bound. -/
theorem zetaPrimeOffDiagonalCoordinate_eq_zero_of_supportUpperBound_lt_center
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) {B : ℝ}
    (hB : ∀ a ∈ tsupport (convolutionAutocorrelationKernel f), a ≤ B)
    (hι : B < ZetaPrimePowerIndex.center ι) :
    zetaPrimeOffDiagonalCoordinate ι f = 0 := by
  have hkernel :
      convolutionAutocorrelationKernel f (ZetaPrimePowerIndex.center ι) = 0 :=
    convolutionAutocorrelationKernel_eq_zero_of_supportUpperBound_lt
      f hB hι
  have hinner :
      zetaSeedInner (zetaTranslate (ZetaPrimePowerIndex.center ι) f) f = 0 := by
    exact Eq.trans
      (convolutionAutocorrelationKernel_eq_translateInner
        f (ZetaPrimePowerIndex.center ι)).symm
      hkernel
  have hre :
      Complex.re (zetaSeedInner (zetaTranslate (ZetaPrimePowerIndex.center ι) f) f) = 0 :=
    congrArg Complex.re hinner
  unfold zetaPrimeOffDiagonalCoordinate
  calc
    -(2 * ι.weight *
        Complex.re (zetaSeedInner (zetaTranslate ι.center f) f)) =
        -(2 * ι.weight * 0) := by
      exact congrArg
        (fun x : ℝ => -(2 * ι.weight * x))
        hre
    _ = -0 := by
      exact congrArg Neg.neg (mul_zero (2 * ι.weight))
    _ = 0 := by
      exact neg_zero

/-- The diagonal debt attached to one prime-power coordinate. -/
def zetaPrimeDiagonalDebtCoordinate
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℝ :=
  ι.weight *
    (zetaSeedNormSq f + zetaSeedNormSq (zetaTranslate ι.center f))

/-- The completed square attached to one prime-power coordinate. -/
def zetaPrimeTranslationDefectEnergyCoordinate
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℝ :=
  ι.weight * zetaTranslationDefectNormSq ι.center f

/-- The raw physical prime off-diagonal channel over a finite prime-power window. -/
def zetaPrimeOffDiagonalChannel
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  ∑ ι in ZetaPrimePowerIndex.window N, zetaPrimeOffDiagonalCoordinate ι f

/-- The completed prime off-diagonal channel is the infinite prime-power sum of the
renormalized off-diagonal coordinates. -/
noncomputable def zetaCompletedPrimeOffDiagonalChannel
    (f : ZetaAdmissibleFunction) : ℝ :=
  ∑' ι : ZetaPrimePowerIndex, zetaPrimeOffDiagonalCoordinate ι f

/-- The total diagonal debt over a finite prime-power window. -/
def zetaPrimeDiagonalDebt
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  ∑ ι in ZetaPrimePowerIndex.window N, zetaPrimeDiagonalDebtCoordinate ι f

/-- The prime translation-defect square energy over a finite prime-power window. -/
def zetaPrimeTranslationDefectEnergy
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  ∑ ι in ZetaPrimePowerIndex.window N,
    zetaPrimeTranslationDefectEnergyCoordinate ι f

/-- The prime defect operator at a prime-power index, applied to an admissible seed.

This is the concrete owner version of `Δ_{p,k} φ = φ - T_{k log p} φ`.  It is represented
as a defect function rather than as an abstract operator because the current RH lane owns the
translation calculus on `ZetaAdmissibleFunction`. -/
def zetaPrimeDefectOperator
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    ℝ → ℂ :=
  zetaTranslationDefectValue ι.center f

/-- The one-coordinate prime defect-kernel quadratic form. -/
def zetaPrimeDefectKernelQuadraticCoordinate
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℝ :=
  zetaPrimeTranslationDefectEnergyCoordinate ι f

/-- The finite-window prime defect-kernel quadratic form.  This is the positive prime object;
the raw prime boundary channel is only its cross term after expansion. -/
def zetaPrimeDefectKernelQuadraticForm
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  zetaPrimeTranslationDefectEnergy N f

/-- The finite-window symmetrized prime boundary cross term. -/
def zetaPrimeSymmetrizedBoundaryCrossTerm
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  zetaPrimeOffDiagonalChannel N f

/-- The finite-window prime diagonal debt term appearing in the defect-square expansion. -/
def zetaPrimeDefectDiagonalDebt
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  zetaPrimeDiagonalDebt N f

/-- The defect-kernel coordinate is the translation-defect square coordinate. -/
theorem zetaPrimeDefectKernelQuadraticCoordinate_eq_translationDefectEnergyCoordinate
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    zetaPrimeDefectKernelQuadraticCoordinate ι f =
      zetaPrimeTranslationDefectEnergyCoordinate ι f := by
  rfl

/-- The finite prime defect-kernel quadratic form is the translation-defect energy. -/
theorem zetaPrimeDefectKernelQuadraticForm_eq_translationDefectEnergy
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    zetaPrimeDefectKernelQuadraticForm N f =
      zetaPrimeTranslationDefectEnergy N f := by
  rfl

/-- The one-coordinate completed-square identity. -/
theorem zetaPrimeOffDiagonal_add_diagonalDebt_coordinate
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    zetaPrimeOffDiagonalCoordinate ι f +
        zetaPrimeDiagonalDebtCoordinate ι f =
      zetaPrimeTranslationDefectEnergyCoordinate ι f := by
  have hdef :=
    zetaTranslationDefectNormSq_eq_diagonal_sub_offDiagonal ι.center f
  unfold zetaPrimeOffDiagonalCoordinate
  unfold zetaPrimeDiagonalDebtCoordinate
  unfold zetaPrimeTranslationDefectEnergyCoordinate
  calc
    -(2 * ι.weight *
          Complex.re (zetaSeedInner (zetaTranslate ι.center f) f)) +
        ι.weight *
          (zetaSeedNormSq f + zetaSeedNormSq (zetaTranslate ι.center f)) =
        ι.weight *
          (zetaSeedNormSq f + zetaSeedNormSq (zetaTranslate ι.center f) -
            2 * Complex.re (zetaSeedInner (zetaTranslate ι.center f) f)) := by
      exact zetaPrimeSquareLedger_scalar_distrib
        ι.weight
        (zetaSeedNormSq f)
        (zetaSeedNormSq (zetaTranslate ι.center f))
        (Complex.re (zetaSeedInner (zetaTranslate ι.center f) f))
    _ = ι.weight * zetaTranslationDefectNormSq ι.center f := by
      exact congrArg (fun x : ℝ => ι.weight * x) hdef.symm

/-- Prime off-diagonal plus diagonal debt is the finite sum of translation-defect squares. -/
theorem zetaPrimeOffDiagonal_add_diagonalDebt_eq_translationDefectEnergy
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    zetaPrimeOffDiagonalChannel N f + zetaPrimeDiagonalDebt N f =
      zetaPrimeTranslationDefectEnergy N f := by
  unfold zetaPrimeOffDiagonalChannel
  unfold zetaPrimeDiagonalDebt
  unfold zetaPrimeTranslationDefectEnergy
  calc
    (∑ ι in ZetaPrimePowerIndex.window N, zetaPrimeOffDiagonalCoordinate ι f) +
        ∑ ι in ZetaPrimePowerIndex.window N, zetaPrimeDiagonalDebtCoordinate ι f =
        ∑ ι in ZetaPrimePowerIndex.window N,
          (zetaPrimeOffDiagonalCoordinate ι f +
            zetaPrimeDiagonalDebtCoordinate ι f) := by
      exact (Finset.sum_add_distrib).symm
    _ =
        ∑ ι in ZetaPrimePowerIndex.window N,
          zetaPrimeTranslationDefectEnergyCoordinate ι f := by
      exact Finset.sum_congr rfl
        (fun ι hι =>
          (fun hmem : ι ∈ ZetaPrimePowerIndex.window N =>
            zetaPrimeOffDiagonal_add_diagonalDebt_coordinate ι f) hι)

/-- A single prime translation-defect energy coordinate is nonnegative. -/
theorem zetaPrimeTranslationDefectEnergyCoordinate_nonnegative
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    0 ≤ zetaPrimeTranslationDefectEnergyCoordinate ι f := by
  unfold zetaPrimeTranslationDefectEnergyCoordinate
  exact mul_nonneg
    (ZetaPrimePowerIndex.weight_nonnegative ι)
    (zetaTranslationDefectNormSq_nonnegative ι.center f)

/-- Prime translation-defect energy is nonnegative. -/
theorem zetaPrimeTranslationDefectEnergy_nonnegative
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    0 ≤ zetaPrimeTranslationDefectEnergy N f := by
  unfold zetaPrimeTranslationDefectEnergy
  exact Finset.sum_nonneg
    (fun ι hι => zetaPrimeTranslationDefectEnergyCoordinate_nonnegative ι f)

/-- Prime defect-kernel positivity. This is the owner positivity theorem for the prime
finite-window object. -/
theorem zetaPrimeDefectKernelQuadraticForm_nonnegative
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    0 ≤ zetaPrimeDefectKernelQuadraticForm N f := by
  exact zetaPrimeTranslationDefectEnergy_nonnegative N f

/-- The finite prime positive-kernel/GNS boundary form. This is the object whose positivity is
immediate from the defect-square construction. -/
def zetaPrimeDefectKernelGNSBoundaryForm
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  zetaPrimeDefectKernelQuadraticForm N f

/-- Finite prime positive-kernel/GNS positivity. -/
theorem zetaPrimeDefectKernelGNSBoundaryForm_nonnegative
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    0 ≤ zetaPrimeDefectKernelGNSBoundaryForm N f := by
  exact zetaPrimeDefectKernelQuadraticForm_nonnegative N f

/-- The prime defect-kernel expansion: positive defect square equals diagonal debt plus the
symmetrized prime boundary cross term. -/
theorem zetaPrimeDefectKernelQuadraticForm_eq_diagonalDebt_add_crossTerm
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    zetaPrimeDefectKernelQuadraticForm N f =
      zetaPrimeDefectDiagonalDebt N f +
        zetaPrimeSymmetrizedBoundaryCrossTerm N f := by
  have hledger :
      zetaPrimeOffDiagonalChannel N f + zetaPrimeDiagonalDebt N f =
        zetaPrimeTranslationDefectEnergy N f :=
    zetaPrimeOffDiagonal_add_diagonalDebt_eq_translationDefectEnergy N f
  unfold zetaPrimeDefectKernelQuadraticForm
  unfold zetaPrimeDefectDiagonalDebt
  unfold zetaPrimeSymmetrizedBoundaryCrossTerm
  calc
    zetaPrimeTranslationDefectEnergy N f =
        zetaPrimeOffDiagonalChannel N f + zetaPrimeDiagonalDebt N f := by
      exact hledger.symm
    _ = zetaPrimeDiagonalDebt N f + zetaPrimeOffDiagonalChannel N f := by
      exact add_comm (zetaPrimeOffDiagonalChannel N f) (zetaPrimeDiagonalDebt N f)

/-- The finite prime GNS boundary form expands into diagonal debt plus the symmetrized prime
boundary cross term. -/
theorem zetaPrimeDefectKernelGNSBoundaryForm_eq_diagonalDebt_add_crossTerm
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    zetaPrimeDefectKernelGNSBoundaryForm N f =
      zetaPrimeDefectDiagonalDebt N f +
        zetaPrimeSymmetrizedBoundaryCrossTerm N f := by
  exact zetaPrimeDefectKernelQuadraticForm_eq_diagonalDebt_add_crossTerm N f

/-- The finite set that can support nonzero prime off-diagonal coordinates for an explicit
autocorrelation support bound. -/
def zetaPrimeOffDiagonalSupportFinsetOfBound
    (f : ZetaAdmissibleFunction) (B : ℝ) : Finset ZetaPrimePowerIndex :=
  (ZetaPrimePowerIndex.finite_setOf_isGenuine_and_center_le
      B).toFinset

/-- Membership in the prime off-diagonal support finset is exactly genuine bounded center. -/
theorem mem_zetaPrimeOffDiagonalSupportFinsetOfBound_iff
    (f : ZetaAdmissibleFunction) (B : ℝ) (ι : ZetaPrimePowerIndex) :
    ι ∈ zetaPrimeOffDiagonalSupportFinsetOfBound f B ↔
      ZetaPrimePowerIndex.IsGenuine ι ∧
        ZetaPrimePowerIndex.center ι ≤ B := by
  unfold zetaPrimeOffDiagonalSupportFinsetOfBound
  exact
    Set.Finite.mem_toFinset
      (ZetaPrimePowerIndex.finite_setOf_isGenuine_and_center_le
        B)

/-- Prime off-diagonal coordinates vanish away from their finite support finset. -/
theorem zetaPrimeOffDiagonalCoordinate_eq_zero_of_not_mem_supportFinsetOfBound
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) {B : ℝ}
    (hB : ∀ a ∈ tsupport (convolutionAutocorrelationKernel f), a ≤ B)
    (hι : ι ∉ zetaPrimeOffDiagonalSupportFinsetOfBound f B) :
    zetaPrimeOffDiagonalCoordinate ι f = 0 := by
  by_cases hgenuine : ZetaPrimePowerIndex.IsGenuine ι
  · by_cases hcenter : ZetaPrimePowerIndex.center ι ≤ B
    · have hmem :
          ι ∈ zetaPrimeOffDiagonalSupportFinsetOfBound f B :=
        (mem_zetaPrimeOffDiagonalSupportFinsetOfBound_iff f B ι).mpr
          ⟨hgenuine, hcenter⟩
      exact False.elim (hι hmem)
    · have hlt : B < ZetaPrimePowerIndex.center ι :=
        lt_of_not_ge hcenter
      exact zetaPrimeOffDiagonalCoordinate_eq_zero_of_supportUpperBound_lt_center
        ι f hB hlt
  · exact zetaPrimeOffDiagonalCoordinate_eq_zero_of_not_isGenuine ι f hgenuine

/-- The prime off-diagonal coordinates are summable against the completed prime-power weights.
This is the owner admissibility/decay estimate for the renormalized prime finite-part channel. -/
theorem summable_zetaPrimeOffDiagonalCoordinate
    (f : ZetaAdmissibleFunction) :
    Summable (fun ι : ZetaPrimePowerIndex =>
      zetaPrimeOffDiagonalCoordinate ι f) := by
  rcases exists_convolutionAutocorrelationKernelSupportUpperBound f with
    ⟨B, hB⟩
  exact summable_of_ne_finset_zero
    (s := zetaPrimeOffDiagonalSupportFinsetOfBound f B)
    (fun ι hι =>
      zetaPrimeOffDiagonalCoordinate_eq_zero_of_not_mem_supportFinsetOfBound ι f hB hι)

/-- Generic exhaustion theorem for summable functions over genuine prime-power windows.

The hypotheses isolate the non-window-specific analytic input (`Summable a`) from the
prime-power indexing input: all non-genuine coordinates vanish and every genuine coordinate is
eventually in the rectangular windows. -/
theorem tendsto_sum_primePowerWindow_tsum_of_summable
    (a : ZetaPrimePowerIndex → ℝ)
    (hsum : Summable a)
    (hzero : ∀ ι : ZetaPrimePowerIndex, ¬ ZetaPrimePowerIndex.IsGenuine ι → a ι = 0) :
    Tendsto
      (fun N : ℕ => ∑ ι in ZetaPrimePowerIndex.window N, a ι)
      atTop
      (nhds (∑' ι : ZetaPrimePowerIndex, a ι)) := by
  exact ZetaPrimePowerIndex.tendsto_sum_window_tsum_of_summable a hsum hzero

/-- The rectangular prime-power windows exhaust the completed prime off-diagonal channel. -/
theorem zetaPrimeOffDiagonalChannel_tendsto_completed
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ => zetaPrimeOffDiagonalChannel N f)
      atTop
      (nhds (zetaCompletedPrimeOffDiagonalChannel f)) := by
  unfold zetaPrimeOffDiagonalChannel
  unfold zetaCompletedPrimeOffDiagonalChannel
  exact tendsto_sum_primePowerWindow_tsum_of_summable
    (fun ι : ZetaPrimePowerIndex => zetaPrimeOffDiagonalCoordinate ι f)
    (summable_zetaPrimeOffDiagonalCoordinate f)
    (fun ι hι => zetaPrimeOffDiagonalCoordinate_eq_zero_of_not_isGenuine ι f hι)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
