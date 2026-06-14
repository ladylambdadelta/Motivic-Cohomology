import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaCompletedWeightStream.ZetaCompletedFinitePart.ZetaCompletedSquareLedger.ZetaAutocorrelationHilbert.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.ZetaPrimePowerWindow.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.Owner
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
      refine Finset.sum_congr rfl ?_
      intro ι hι
      exact zetaPrimeOffDiagonal_add_diagonalDebt_coordinate ι f

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

/-- The non-prime completed channel: archimedean contribution plus centered correction,
evaluated on the convolution autocorrelation probe. -/
def zetaArchimedeanCorrectionAutocorrelationChannel
    (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re
      (zetaCompletedExplicitFormulaArchimedeanContribution
        (ZetaAdmissibleFunction.convolutionAutocorrelation f)) +
    Complex.re
      (zetaCompletedExplicitFormulaCorrectionContribution
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))

/-- The archimedean autocorrelation square energy at the self-dual basepoint. -/
def zetaArchimedeanAutocorrelationSquareEnergy
    (f : ZetaAdmissibleFunction) : ℝ :=
  2 * Complex.normSq (zetaCompletedExplicitFormulaPhi f 0)

/-- The correction autocorrelation square energy is the normalized correction coordinate square. -/
def zetaCorrectionAutocorrelationSquareEnergy
    (_f : ZetaAdmissibleFunction) : ℝ :=
  zetaCompletionCorrectionPacketCoordinate *
    zetaCompletionCorrectionPacketCoordinate

/-- The honest non-prime completed square energy: archimedean square plus correction square. -/
def zetaArchimedeanCorrectionAutocorrelationSquareEnergy
    (f : ZetaAdmissibleFunction) : ℝ :=
  zetaArchimedeanAutocorrelationSquareEnergy f +
    zetaCorrectionAutocorrelationSquareEnergy f

/-- Multiplying a complex conjugate square by the real scalar two has real part twice the
complex norm square. -/
theorem complex_two_mul_conjSquare_re
    (z : ℂ) :
    Complex.re ((2 : ℂ) * (z * star z)) =
      2 * Complex.normSq z := by
  have hsq : z * star z = (Complex.normSq z : ℂ) :=
    Complex.mul_conj z
  have hreal :
      (2 : ℂ) * (Complex.normSq z : ℂ) =
        ((2 * Complex.normSq z : ℝ) : ℂ) := by
    exact (Complex.ofReal_mul 2 (Complex.normSq z)).symm
  calc
    Complex.re ((2 : ℂ) * (z * star z)) =
        Complex.re ((2 : ℂ) * (Complex.normSq z : ℂ)) := by
      exact congrArg (fun x : ℂ => Complex.re ((2 : ℂ) * x)) hsq
    _ = Complex.re ((2 * Complex.normSq z : ℝ) : ℂ) := by
      exact congrArg Complex.re hreal
    _ = 2 * Complex.normSq z := by
      exact Complex.ofReal_re (2 * Complex.normSq z)

/-- The autocorrelation transform at the archimedean basepoint is a Hermitian square. -/
theorem zetaCompletedExplicitFormulaPhi_convolutionAutocorrelation_zero
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaPhi
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) 0 =
      zetaCompletedExplicitFormulaPhi f 0 *
        star (zetaCompletedExplicitFormulaPhi f 0) := by
  have hpair :=
    zetaCompletedExplicitFormulaPhi_convolutionAutocorrelation_real_pair f 0
  have hzero :
      zetaCompletedExplicitFormulaPhi f (-(0 : ℂ)) =
        zetaCompletedExplicitFormulaPhi f 0 := by
    exact congrArg (zetaCompletedExplicitFormulaPhi f) (neg_zero : -(0 : ℂ) = 0)
  calc
    zetaCompletedExplicitFormulaPhi
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) 0 =
        zetaCompletedExplicitFormulaPhi f 0 *
          star (zetaCompletedExplicitFormulaPhi f (-(0 : ℂ))) := hpair
    _ =
        zetaCompletedExplicitFormulaPhi f 0 *
          star (zetaCompletedExplicitFormulaPhi f 0) := by
      exact congrArg
        (fun x : ℂ => zetaCompletedExplicitFormulaPhi f 0 * star x)
        hzero

/-- The archimedean autocorrelation channel is the archimedean Hermitian square energy. -/
theorem zetaArchimedeanAutocorrelationChannel_eq_squareEnergy
    (f : ZetaAdmissibleFunction) :
    Complex.re
        (zetaCompletedExplicitFormulaArchimedeanContribution
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) =
      zetaArchimedeanAutocorrelationSquareEnergy f := by
  unfold zetaCompletedExplicitFormulaArchimedeanContribution
  unfold zetaArchimedeanAutocorrelationSquareEnergy
  have hzero :=
    zetaCompletedExplicitFormulaPhi_convolutionAutocorrelation_zero f
  calc
    Complex.re
        ((2 : ℂ) *
          zetaCompletedExplicitFormulaPhi
            (ZetaAdmissibleFunction.convolutionAutocorrelation f) 0) =
        Complex.re
          ((2 : ℂ) *
            (zetaCompletedExplicitFormulaPhi f 0 *
              star (zetaCompletedExplicitFormulaPhi f 0))) := by
      exact congrArg (fun x : ℂ => Complex.re ((2 : ℂ) * x)) hzero
    _ = 2 * Complex.normSq (zetaCompletedExplicitFormulaPhi f 0) := by
      exact complex_two_mul_conjSquare_re (zetaCompletedExplicitFormulaPhi f 0)

/-- The correction autocorrelation channel is the correction square energy. -/
theorem zetaCorrectionAutocorrelationChannel_eq_squareEnergy
    (f : ZetaAdmissibleFunction) :
    Complex.re
        (zetaCompletedExplicitFormulaCorrectionContribution
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) =
      zetaCorrectionAutocorrelationSquareEnergy f := by
  unfold zetaCorrectionAutocorrelationSquareEnergy
  have hcorr :
      zetaCompletedExplicitFormulaCorrectionContribution
          (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
        zetaCompletionCorrection 0 := by
    exact zetaCompletionCorrection_zero.symm
  calc
    Complex.re
        (zetaCompletedExplicitFormulaCorrectionContribution
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) =
        Complex.re (zetaCompletionCorrection 0) := by
      exact congrArg Complex.re hcorr
    _ =
        zetaCompletionCorrectionPacketCoordinate *
          zetaCompletionCorrectionPacketCoordinate := by
      exact zetaCompletionCorrectionPacketCoordinate_sq.symm

/-- Archimedean plus correction is exactly the honest non-prime completed square energy. -/
theorem zetaArchimedeanCorrectionAutocorrelationChannel_eq_squareEnergy
    (f : ZetaAdmissibleFunction) :
    zetaArchimedeanCorrectionAutocorrelationChannel f =
      zetaArchimedeanCorrectionAutocorrelationSquareEnergy f := by
  have harch := zetaArchimedeanAutocorrelationChannel_eq_squareEnergy f
  have hcorr := zetaCorrectionAutocorrelationChannel_eq_squareEnergy f
  unfold zetaArchimedeanCorrectionAutocorrelationChannel
  unfold zetaArchimedeanCorrectionAutocorrelationSquareEnergy
  exact congrArg₂ HAdd.hAdd harch hcorr

/-- The archimedean autocorrelation square energy is nonnegative. -/
theorem zetaArchimedeanAutocorrelationSquareEnergy_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaArchimedeanAutocorrelationSquareEnergy f := by
  unfold zetaArchimedeanAutocorrelationSquareEnergy
  exact mul_nonneg
    (by exact zero_le_two)
    (Complex.normSq_nonneg (zetaCompletedExplicitFormulaPhi f 0))

/-- The correction autocorrelation square energy is nonnegative. -/
theorem zetaCorrectionAutocorrelationSquareEnergy_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCorrectionAutocorrelationSquareEnergy f := by
  unfold zetaCorrectionAutocorrelationSquareEnergy
  exact mul_self_nonneg zetaCompletionCorrectionPacketCoordinate

/-- The honest non-prime completed square energy is nonnegative. -/
theorem zetaArchimedeanCorrectionAutocorrelationSquareEnergy_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaArchimedeanCorrectionAutocorrelationSquareEnergy f := by
  unfold zetaArchimedeanCorrectionAutocorrelationSquareEnergy
  exact add_nonneg
    (zetaArchimedeanAutocorrelationSquareEnergy_nonnegative f)
    (zetaCorrectionAutocorrelationSquareEnergy_nonnegative f)

/-- The raw finite completed autocorrelation boundary channel in physical variables. -/
def zetaCompletedPhysicalAutocorrelationBoundaryChannel
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  zetaPrimeOffDiagonalChannel N f +
    zetaArchimedeanCorrectionAutocorrelationChannel f

/-- The completed square energy attached to the finite physical boundary channel after adding
the matching prime diagonal debt. -/
def zetaCompletedPhysicalAutocorrelationSquareEnergy
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  zetaPrimeTranslationDefectEnergy N f +
    zetaArchimedeanCorrectionAutocorrelationSquareEnergy f

/-- The completed physical boundary channel becomes a sum of squares after adding the matching
prime diagonal debt. -/
theorem zetaCompletedPhysicalAutocorrelationBoundaryChannel_add_diagonalDebt_eq_squareEnergy
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    zetaCompletedPhysicalAutocorrelationBoundaryChannel N f +
        zetaPrimeDiagonalDebt N f =
      zetaCompletedPhysicalAutocorrelationSquareEnergy N f := by
  have hprime :=
    zetaPrimeOffDiagonal_add_diagonalDebt_eq_translationDefectEnergy N f
  have harch :=
    zetaArchimedeanCorrectionAutocorrelationChannel_eq_squareEnergy f
  unfold zetaCompletedPhysicalAutocorrelationBoundaryChannel
  unfold zetaCompletedPhysicalAutocorrelationSquareEnergy
  calc
    (zetaPrimeOffDiagonalChannel N f +
        zetaArchimedeanCorrectionAutocorrelationChannel f) +
        zetaPrimeDiagonalDebt N f =
        (zetaPrimeOffDiagonalChannel N f + zetaPrimeDiagonalDebt N f) +
          zetaArchimedeanCorrectionAutocorrelationChannel f := by
      have hassoc₁ :
          (zetaPrimeOffDiagonalChannel N f +
              zetaArchimedeanCorrectionAutocorrelationChannel f) +
              zetaPrimeDiagonalDebt N f =
            zetaPrimeOffDiagonalChannel N f +
              (zetaArchimedeanCorrectionAutocorrelationChannel f +
                zetaPrimeDiagonalDebt N f) := by
        exact add_assoc
          (zetaPrimeOffDiagonalChannel N f)
          (zetaArchimedeanCorrectionAutocorrelationChannel f)
          (zetaPrimeDiagonalDebt N f)
      have hcomm :
          zetaArchimedeanCorrectionAutocorrelationChannel f +
              zetaPrimeDiagonalDebt N f =
            zetaPrimeDiagonalDebt N f +
              zetaArchimedeanCorrectionAutocorrelationChannel f := by
        exact add_comm
          (zetaArchimedeanCorrectionAutocorrelationChannel f)
          (zetaPrimeDiagonalDebt N f)
      have hassoc₂ :
          zetaPrimeOffDiagonalChannel N f +
              (zetaPrimeDiagonalDebt N f +
                zetaArchimedeanCorrectionAutocorrelationChannel f) =
            (zetaPrimeOffDiagonalChannel N f + zetaPrimeDiagonalDebt N f) +
              zetaArchimedeanCorrectionAutocorrelationChannel f := by
        exact (add_assoc
          (zetaPrimeOffDiagonalChannel N f)
          (zetaPrimeDiagonalDebt N f)
          (zetaArchimedeanCorrectionAutocorrelationChannel f)).symm
      exact hassoc₁.trans
        ((congrArg
          (fun x : ℝ => zetaPrimeOffDiagonalChannel N f + x)
          hcomm).trans hassoc₂)
    _ =
        zetaPrimeTranslationDefectEnergy N f +
          zetaArchimedeanCorrectionAutocorrelationChannel f := by
      exact congrArg
        (fun x : ℝ => x + zetaArchimedeanCorrectionAutocorrelationChannel f)
        hprime
    _ =
        zetaPrimeTranslationDefectEnergy N f +
          zetaArchimedeanCorrectionAutocorrelationSquareEnergy f := by
      exact congrArg
        (fun x : ℝ => zetaPrimeTranslationDefectEnergy N f + x)
        harch

/-- The debt-corrected completed finite physical autocorrelation boundary channel is
nonnegative. -/
theorem zetaCompletedPhysicalAutocorrelationBoundaryChannel_add_diagonalDebt_nonnegative
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCompletedPhysicalAutocorrelationBoundaryChannel N f +
        zetaPrimeDiagonalDebt N f := by
  have hsquare :=
    zetaCompletedPhysicalAutocorrelationBoundaryChannel_add_diagonalDebt_eq_squareEnergy N f
  have hprime := zetaPrimeTranslationDefectEnergy_nonnegative N f
  have haux := zetaArchimedeanCorrectionAutocorrelationSquareEnergy_nonnegative f
  have hsum :
      0 ≤ zetaCompletedPhysicalAutocorrelationSquareEnergy N f := by
    unfold zetaCompletedPhysicalAutocorrelationSquareEnergy
    exact add_nonneg hprime haux
  exact Eq.subst (motive := fun x : ℝ => 0 ≤ x) hsquare.symm hsum

/-- The finite completed physical boundary channel attached to the `N`th prime-power window. -/
def completedBoundaryWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  zetaCompletedPhysicalAutocorrelationBoundaryChannel N f

/-- The physical prime off-diagonal boundary window evaluates the convolution autocorrelation
kernel at prime-power centers.  This is distinct from the Laplace-transform spectral window. -/
def primeKernelOffDiagonalBoundaryWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  ∑ ι in ZetaPrimePowerIndex.window N,
    - (2 * ι.weight * Complex.re (convolutionAutocorrelationKernel f ι.center))

/-- The kernel-level prime off-diagonal window is the physical prime off-diagonal channel. -/
theorem primeKernelOffDiagonalBoundaryWindow_eq_physicalPrimeOffDiagonal
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    primeKernelOffDiagonalBoundaryWindow N f =
      zetaPrimeOffDiagonalChannel N f := by
  unfold primeKernelOffDiagonalBoundaryWindow
  unfold zetaPrimeOffDiagonalChannel
  refine Finset.sum_congr rfl ?_
  intro ι hι
  unfold zetaPrimeOffDiagonalCoordinate
  have hkernel :
      convolutionAutocorrelationKernel f ι.center =
        zetaSeedInner (zetaTranslate ι.center f) f :=
    convolutionAutocorrelationKernel_eq_translateInner f ι.center
  exact congrArg
    (fun x : ℝ => - (2 * ι.weight * x))
    (congrArg Complex.re hkernel)

/-- The completed physical boundary window is the kernel off-diagonal window plus the
archimedean/correction square channel. -/
theorem completedBoundaryWindow_eq_primeKernelOffDiagonal_add_archimedeanCorrection
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    completedBoundaryWindow N f =
      primeKernelOffDiagonalBoundaryWindow N f +
        zetaArchimedeanCorrectionAutocorrelationChannel f := by
  have hprime :=
    primeKernelOffDiagonalBoundaryWindow_eq_physicalPrimeOffDiagonal N f
  unfold completedBoundaryWindow
  unfold zetaCompletedPhysicalAutocorrelationBoundaryChannel
  calc
    zetaPrimeOffDiagonalChannel N f +
        zetaArchimedeanCorrectionAutocorrelationChannel f =
        zetaPrimeOffDiagonalChannel N f +
          zetaArchimedeanCorrectionAutocorrelationChannel f := by
      rfl
    _ =
        primeKernelOffDiagonalBoundaryWindow N f +
          zetaArchimedeanCorrectionAutocorrelationChannel f := by
      exact congrArg
        (fun x : ℝ => x + zetaArchimedeanCorrectionAutocorrelationChannel f)
        hprime.symm

/-- The completed physical boundary window unfolds to the prime off-diagonal window plus the
archimedean/correction channel. -/
theorem completedBoundaryWindow_eq_primeOffDiagonal_add_archimedeanCorrection
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    completedBoundaryWindow N f =
      zetaPrimeOffDiagonalChannel N f +
        zetaArchimedeanCorrectionAutocorrelationChannel f := by
  rfl

/-- The smaller prime-power window embeds into the larger one compatibly with the completed
physical boundary presentation. -/
theorem completedBoundaryWindow_mono_compat
    {N M : ℕ} (hNM : N ≤ M) (f : ZetaAdmissibleFunction) :
    zetaPrimeOffDiagonalChannel N f =
      ∑ ι in (ZetaPrimePowerIndex.window M).filter
          (fun ι => ι ∈ ZetaPrimePowerIndex.window N),
        zetaPrimeOffDiagonalCoordinate ι f := by
  unfold zetaPrimeOffDiagonalChannel
  have hwindow :
      (ZetaPrimePowerIndex.window M).filter
          (fun ι => ι ∈ ZetaPrimePowerIndex.window N) =
        ZetaPrimePowerIndex.window N := by
    ext ι
    constructor
    · intro hι
      exact (Finset.mem_filter.mp hι).2
    · intro hι
      exact Finset.mem_filter.mpr
        ⟨ZetaPrimePowerIndex.window_mono hNM hι, hι⟩
  exact congrArg
    (fun s : Finset ZetaPrimePowerIndex =>
      ∑ ι in s, zetaPrimeOffDiagonalCoordinate ι f)
    hwindow.symm

/-- The debt-corrected finite completed boundary window.  This is the finite approximant in the
completed normalization; the raw finite physical window alone is not the approximating object. -/
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
