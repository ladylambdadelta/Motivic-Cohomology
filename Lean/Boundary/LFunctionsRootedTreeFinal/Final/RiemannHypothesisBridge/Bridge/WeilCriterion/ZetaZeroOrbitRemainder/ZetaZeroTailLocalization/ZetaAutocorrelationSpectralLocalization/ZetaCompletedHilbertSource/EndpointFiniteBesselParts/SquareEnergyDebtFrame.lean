import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointFiniteBesselParts.PositiveTraceMatrix
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointFiniteBesselParts.PrimeOffDiagonalWindow
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.TraceReconstruction

/-!
# Endpoint finite square-energy debt frame

This file owns the finite square-energy frame that realizes the endpoint debt
inside the finite positive trace matrix.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- If `D + E ≤ Q`, then the two successive Schur subtractions leave a
nonnegative real remainder. -/
theorem endpointFinite_sub_sub_nonnegative_of_add_le
    (Q D E : ℝ) (hbound : D + E ≤ Q) :
    0 ≤ Q - D - E :=
  let hsingle :
      0 ≤ Q - (D + E) :=
    sub_nonneg.mpr hbound
  let hsubLeft :
        Q - (D + E) = Q + -(D + E) :=
      sub_eq_add_neg Q (D + E)
  let hneg :
        Q + -(D + E) = Q + (-D + -E) :=
      congrArg (fun value : ℝ => Q + value) (neg_add D E)
  let hassoc :
        Q + (-D + -E) = (Q + -D) + -E :=
      (add_assoc Q (-D) (-E)).symm
  let hfirstSub :
        (Q + -D) + -E = Q - D + -E :=
      congrArg (fun value : ℝ => value + -E)
        (sub_eq_add_neg Q D).symm
  let hsecondSub :
        Q - D + -E = Q - D - E :=
      (sub_eq_add_neg (Q - D) E).symm
  let hnormal :
      Q - (D + E) = Q - D - E :=
    hsubLeft.trans
      (hneg.trans
        (hassoc.trans
          (hfirstSub.trans hsecondSub)))
  Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    hnormal
    hsingle

/-- The finite square-energy domination needed by endpoint Schur compression. -/
def CompletedEndpointFiniteSquareEnergyEndpointDebtDomination
    (N : ℕ) (f : ZetaAdmissibleFunction) : Prop :=
  zetaPrimeDiagonalDebt N f +
      (completedWeilEndpointTraceFiber f).gram ≤
    finitePositiveSquareEnergyWindow N f

/-- A finite square-energy frame splitting the positive square energy into
prime diagonal debt, endpoint debt, and a nonnegative complement. -/
structure CompletedEndpointFiniteSquareEnergyEndpointDebtFrame
    (N : ℕ) (f : ZetaAdmissibleFunction) where
  squareEnergy : ℝ
  primeDiagonalDebt : ℝ
  endpointDebt : ℝ
  complementEnergy : ℝ
  squareEnergy_eq :
    squareEnergy = finitePositiveSquareEnergyWindow N f
  primeDiagonalDebt_eq :
    primeDiagonalDebt = zetaPrimeDiagonalDebt N f
  endpointDebt_eq :
    endpointDebt = (completedWeilEndpointTraceFiber f).gram
  squareEnergy_split :
    squareEnergy =
      primeDiagonalDebt + endpointDebt + complementEnergy
  complementEnergy_nonnegative :
    0 ≤ complementEnergy

/-- The canonical finite complement left after removing the prime diagonal
debt and the visible endpoint trace Gram from the finite positive square
energy. -/
noncomputable def completedEndpointFiniteSquareEnergyEndpointDebtComplement
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  finitePositiveSquareEnergyWindow N f -
    (zetaPrimeDiagonalDebt N f +
      (completedWeilEndpointTraceFiber f).gram)

/-- The finite square-energy endpoint-debt complement unfolds to square energy
minus the combined prime-diagonal and endpoint debts. -/
theorem completedEndpointFiniteSquareEnergyEndpointDebtComplement_eq
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    completedEndpointFiniteSquareEnergyEndpointDebtComplement N f =
      finitePositiveSquareEnergyWindow N f -
        (zetaPrimeDiagonalDebt N f +
          (completedWeilEndpointTraceFiber f).gram) :=
  Eq.refl (completedEndpointFiniteSquareEnergyEndpointDebtComplement N f)

/-- Nonnegativity of the canonical finite square-energy complement is exactly
the finite domination needed by endpoint Schur compression. -/
theorem completedEndpointFiniteSquareEnergyEndpointDebtDomination_of_complement_nonnegative
    (N : ℕ) (f : ZetaAdmissibleFunction)
    (hcomplement :
      0 ≤ completedEndpointFiniteSquareEnergyEndpointDebtComplement N f) :
    CompletedEndpointFiniteSquareEnergyEndpointDebtDomination N f :=
  let hsub :
      0 ≤
        finitePositiveSquareEnergyWindow N f -
          (zetaPrimeDiagonalDebt N f +
            (completedWeilEndpointTraceFiber f).gram) :=
    Eq.subst
      (motive := fun value : ℝ => 0 ≤ value)
      (completedEndpointFiniteSquareEnergyEndpointDebtComplement_eq N f)
      hcomplement
  sub_nonneg.mp hsub

/-- Finite domination gives nonnegativity of the canonical finite square-energy
complement. -/
theorem completedEndpointFiniteSquareEnergyEndpointDebtComplement_nonnegative_of_domination
    (N : ℕ) (f : ZetaAdmissibleFunction)
    (hdomination :
      CompletedEndpointFiniteSquareEnergyEndpointDebtDomination N f) :
    0 ≤ completedEndpointFiniteSquareEnergyEndpointDebtComplement N f :=
  let hsub :
      0 ≤
        finitePositiveSquareEnergyWindow N f -
          (zetaPrimeDiagonalDebt N f +
            (completedWeilEndpointTraceFiber f).gram) :=
    sub_nonneg.mpr hdomination
  Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    (completedEndpointFiniteSquareEnergyEndpointDebtComplement_eq N f).symm
    hsub

/-- The finite renormalized boundary window is the positive square-energy
window after subtracting prime diagonal debt, in the finite trace-frame owner
layer. -/
theorem finitePositiveRenormalizedBoundaryWindow_eq_squareEnergy_sub_primeDiagonalDebt_traceFrame
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePositiveRenormalizedBoundaryWindow N f =
      finitePositiveSquareEnergyWindow N f - zetaPrimeDiagonalDebt N f :=
  let hcorrected :
      completedCorrectedBoundaryWindow N f =
        finitePositiveSquareEnergyWindow N f :=
    completedCorrectedBoundaryWindow_eq_finitePositiveSquareEnergyWindow
      N f
  let hadd :
      finitePositiveRenormalizedBoundaryWindow N f =
        finitePositiveSquareEnergyWindow N f +
          -zetaPrimeDiagonalDebt N f :=
    congrArg
      (fun value : ℝ => value + -zetaPrimeDiagonalDebt N f)
      hcorrected
  hadd.trans
    (sub_eq_add_neg
      (finitePositiveSquareEnergyWindow N f)
      (zetaPrimeDiagonalDebt N f)).symm

/-- If the endpoint Gram is dominated by the renormalized finite boundary
window, then the positive square-energy window dominates prime diagonal debt
plus the endpoint Gram. -/
theorem completedEndpointFiniteSquareEnergyEndpointDebtDomination_of_renormalizedEndpointBound
    (N : ℕ) (f : ZetaAdmissibleFunction)
    (hbound :
      (completedWeilEndpointTraceFiber f).gram ≤
        finitePositiveRenormalizedBoundaryWindow N f) :
    CompletedEndpointFiniteSquareEnergyEndpointDebtDomination N f :=
  let Q : ℝ := finitePositiveSquareEnergyWindow N f
  let D : ℝ := zetaPrimeDiagonalDebt N f
  let E : ℝ := (completedWeilEndpointTraceFiber f).gram
  let hrenormalized :
      finitePositiveRenormalizedBoundaryWindow N f = Q - D :=
    finitePositiveRenormalizedBoundaryWindow_eq_squareEnergy_sub_primeDiagonalDebt_traceFrame
      N f
  let hEsub : E ≤ Q - D :=
    Eq.subst
      (motive := fun value : ℝ =>
        (completedWeilEndpointTraceFiber f).gram ≤ value)
      hrenormalized
      hbound
  let haddLeft : D + E ≤ D + (Q - D) :=
    add_le_add_left hEsub D
  let hsplit : Q = D + (Q - D) :=
    endpointTraceDebt_add_sub_cancel Q D
  let htarget : D + E ≤ Q :=
    Eq.subst
      (motive := fun value : ℝ => D + E ≤ value)
      hsplit.symm
      haddLeft
  htarget

/-- The canonical nonnegative finite complement constructs the square-energy
endpoint-debt frame. -/
def completedEndpointFiniteSquareEnergyEndpointDebtFrame_of_complement_nonnegative
    (N : ℕ) (f : ZetaAdmissibleFunction)
    (hcomplement :
      0 ≤ completedEndpointFiniteSquareEnergyEndpointDebtComplement N f) :
    CompletedEndpointFiniteSquareEnergyEndpointDebtFrame N f :=
  { squareEnergy := finitePositiveSquareEnergyWindow N f
    primeDiagonalDebt := zetaPrimeDiagonalDebt N f
    endpointDebt := (completedWeilEndpointTraceFiber f).gram
    complementEnergy :=
      completedEndpointFiniteSquareEnergyEndpointDebtComplement N f
    squareEnergy_eq :=
      Eq.refl (finitePositiveSquareEnergyWindow N f)
    primeDiagonalDebt_eq :=
      Eq.refl (zetaPrimeDiagonalDebt N f)
    endpointDebt_eq :=
      Eq.refl ((completedWeilEndpointTraceFiber f).gram)
    squareEnergy_split :=
      endpointTraceDebt_add_sub_cancel
        (finitePositiveSquareEnergyWindow N f)
        (zetaPrimeDiagonalDebt N f +
          (completedWeilEndpointTraceFiber f).gram)
    complementEnergy_nonnegative := hcomplement }

/-- A finite square-energy endpoint-debt frame gives the scalar domination
needed by endpoint Schur compression. -/
theorem completedEndpointFiniteSquareEnergyEndpointDebtDomination_of_frame
    (N : ℕ) (f : ZetaAdmissibleFunction)
    (frame : CompletedEndpointFiniteSquareEnergyEndpointDebtFrame N f) :
    CompletedEndpointFiniteSquareEnergyEndpointDebtDomination N f :=
  let hwithComplement :
        frame.primeDiagonalDebt + frame.endpointDebt ≤
          frame.primeDiagonalDebt + frame.endpointDebt +
            frame.complementEnergy :=
      le_add_of_nonneg_right frame.complementEnergy_nonnegative
  let hframeLe :
      frame.primeDiagonalDebt + frame.endpointDebt ≤ frame.squareEnergy :=
    Eq.subst
      (motive := fun value : ℝ =>
        frame.primeDiagonalDebt + frame.endpointDebt ≤ value)
      frame.squareEnergy_split.symm
      hwithComplement
  let hleft :
      frame.primeDiagonalDebt + frame.endpointDebt =
        zetaPrimeDiagonalDebt N f +
          (completedWeilEndpointTraceFiber f).gram :=
    congrArg₂ HAdd.hAdd
      frame.primeDiagonalDebt_eq
      frame.endpointDebt_eq
  let hactualLeft :
      zetaPrimeDiagonalDebt N f +
          (completedWeilEndpointTraceFiber f).gram ≤
        frame.squareEnergy :=
    Eq.subst
      (motive := fun value : ℝ => value ≤ frame.squareEnergy)
      hleft
      hframeLe
  Eq.subst
    (motive := fun value : ℝ =>
      zetaPrimeDiagonalDebt N f +
          (completedWeilEndpointTraceFiber f).gram ≤ value)
    frame.squareEnergy_eq
    hactualLeft

/-- Finite square-energy endpoint-debt domination gives nonnegativity of the
canonical finite trace-frame complement norm-square. -/
theorem completedEndpointFinitePositiveTraceFrameComplementNormSq_nonnegative_of_squareEnergyEndpointDebtDomination
    (N : ℕ) (f : ZetaAdmissibleFunction)
    (hdomination :
      CompletedEndpointFiniteSquareEnergyEndpointDebtDomination N f) :
    0 ≤ completedEndpointFinitePositiveTraceFrameComplementNormSq N f :=
  let Q : ℝ := finitePositiveSquareEnergyWindow N f
  let D : ℝ := zetaPrimeDiagonalDebt N f
  let E : ℝ := (completedWeilEndpointTraceFiber f).gram
  let hrenormalized :
      finitePositiveRenormalizedBoundaryWindow N f = Q - D :=
    finitePositiveRenormalizedBoundaryWindow_eq_squareEnergy_sub_primeDiagonalDebt_traceFrame
      N f
  let hraw :
        completedEndpointFinitePositiveTraceFrameComplementNormSq N f =
          finitePositiveRenormalizedBoundaryWindow N f - E :=
      Eq.refl (completedEndpointFinitePositiveTraceFrameComplementNormSq N f)
  let hcomplement :
      completedEndpointFinitePositiveTraceFrameComplementNormSq N f =
        Q - D - E :=
    hraw.trans
      (congrArg (fun value : ℝ => value - E) hrenormalized)
  let hbound : D + E ≤ Q := hdomination
  let hsub :
      0 ≤ Q - D - E :=
    endpointFinite_sub_sub_nonnegative_of_add_le Q D E hbound
  Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    hcomplement.symm
    hsub

/-- If the finite prime off-diagonal channel vanishes, then the prime
translation-defect square is the finite diagonal debt. -/
theorem zetaPrimeTranslationDefectEnergy_eq_diagonalDebt_of_offDiagonal_zero
    (N : ℕ) (f : ZetaAdmissibleFunction)
    (hoffDiagonal : zetaPrimeOffDiagonalChannel N f = 0) :
    zetaPrimeTranslationDefectEnergy N f = zetaPrimeDiagonalDebt N f :=
  let hledger :
      zetaPrimeOffDiagonalChannel N f + zetaPrimeDiagonalDebt N f =
        zetaPrimeTranslationDefectEnergy N f :=
    zetaPrimeOffDiagonal_add_diagonalDebt_eq_translationDefectEnergy N f
  let hzeroAdd :
      0 + zetaPrimeDiagonalDebt N f =
        zetaPrimeTranslationDefectEnergy N f :=
    Eq.subst
      (motive := fun value : ℝ =>
        value + zetaPrimeDiagonalDebt N f =
          zetaPrimeTranslationDefectEnergy N f)
      hoffDiagonal
      hledger
  let hdiagonal :
      zetaPrimeDiagonalDebt N f =
        zetaPrimeTranslationDefectEnergy N f :=
    (zero_add (zetaPrimeDiagonalDebt N f)).symm.trans hzeroAdd
  hdiagonal.symm

/-- Eventually the finite prime translation-defect square equals the finite
prime diagonal debt. -/
theorem zetaPrimeTranslationDefectEnergy_eventually_eq_diagonalDebt_source
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    ∀ᶠ N in atTop,
      zetaPrimeTranslationDefectEnergy N f = zetaPrimeDiagonalDebt N f :=
  (zetaPrimeOffDiagonalChannel_eventually_eq_zero_source
    f D).mono
    (fun N hN =>
      zetaPrimeTranslationDefectEnergy_eq_diagonalDebt_of_offDiagonal_zero
        N f hN)

/-- Eventually the finite prime diagonal debt is bounded by the finite prime
translation-defect square. -/
theorem zetaPrimeDiagonalDebt_eventually_le_translationDefectEnergy_source
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    ∀ᶠ N in atTop,
      zetaPrimeDiagonalDebt N f ≤ zetaPrimeTranslationDefectEnergy N f :=
  (zetaPrimeTranslationDefectEnergy_eventually_eq_diagonalDebt_source
    f D).mono
    (fun N hN => Eq.subst
      (motive := fun value : ℝ => zetaPrimeDiagonalDebt N f ≤ value)
      hN.symm
      (le_refl (zetaPrimeDiagonalDebt N f)))

/-- Source finite square-energy endpoint-debt domination, transported from the
finite positive trace-matrix endpoint-vector realization. -/
theorem completedEndpointFiniteSquareEnergyEndpointDebtDomination_eventually_traceExhaustion_source
    (f : ZetaAdmissibleFunction)
    (hrealization :
      ∀ᶠ N in atTop,
        CompletedEndpointFinitePositiveTraceMatrixEndpointVectorRealization
          N f) :
    ∀ᶠ N in atTop,
      CompletedEndpointFiniteSquareEnergyEndpointDebtDomination N f :=
  hrealization.mono
    (fun N hrealization =>
      let hdomination :
            CompletedEndpointFinitePositiveTraceMatrixEndpointBesselDomination
              N f :=
          completedEndpointFinitePositiveTraceMatrixEndpointBesselDomination_of_endpointVectorRealization
            N f hrealization
      completedEndpointFiniteSquareEnergyEndpointDebtDomination_of_renormalizedEndpointBound
        N f
        (completedEndpointFiniteBesselCompression_of_positiveTraceMatrixEndpointBesselDomination
          N f hdomination))

/-- Source finite square-energy endpoint-debt complement nonnegativity. -/
theorem completedEndpointFiniteSquareEnergyEndpointDebtComplement_eventually_nonnegative_source
    (f : ZetaAdmissibleFunction)
    (hrealization :
      ∀ᶠ N in atTop,
        CompletedEndpointFinitePositiveTraceMatrixEndpointVectorRealization
          N f) :
    ∀ᶠ N in atTop,
      0 ≤ completedEndpointFiniteSquareEnergyEndpointDebtComplement N f :=
  (completedEndpointFiniteSquareEnergyEndpointDebtDomination_eventually_traceExhaustion_source
    f hrealization).mono
    (fun N hN =>
      completedEndpointFiniteSquareEnergyEndpointDebtComplement_nonnegative_of_domination
        N f hN)

/-- Source finite square-energy endpoint-debt frame construction. -/
theorem completedEndpointFiniteSquareEnergyEndpointDebtFrame_eventually_source
    (f : ZetaAdmissibleFunction)
    (hrealization :
      ∀ᶠ N in atTop,
        CompletedEndpointFinitePositiveTraceMatrixEndpointVectorRealization
          N f) :
    ∀ᶠ N in atTop,
      Nonempty (CompletedEndpointFiniteSquareEnergyEndpointDebtFrame N f) :=
  (completedEndpointFiniteSquareEnergyEndpointDebtComplement_eventually_nonnegative_source
    f hrealization).mono
    (fun N hN =>
      Nonempty.intro
        (completedEndpointFiniteSquareEnergyEndpointDebtFrame_of_complement_nonnegative
          N f hN))

/-- Source finite square-energy endpoint-debt domination. -/
theorem completedEndpointFiniteSquareEnergyEndpointDebtDomination_eventually_source
    (f : ZetaAdmissibleFunction)
    (hrealization :
      ∀ᶠ N in atTop,
        CompletedEndpointFinitePositiveTraceMatrixEndpointVectorRealization
          N f) :
    ∀ᶠ N in atTop,
      CompletedEndpointFiniteSquareEnergyEndpointDebtDomination N f :=
  (completedEndpointFiniteSquareEnergyEndpointDebtFrame_eventually_source
    f hrealization).mono
    (fun N hN =>
      match hN with
      | ⟨frame⟩ =>
          completedEndpointFiniteSquareEnergyEndpointDebtDomination_of_frame
            N f frame)

/-- Source finite trace-frame complement norm-square nonnegativity. -/
theorem completedEndpointFinitePositiveTraceFrameComplementNormSq_eventually_nonnegative_source
    (f : ZetaAdmissibleFunction)
    (hrealization :
      ∀ᶠ N in atTop,
        CompletedEndpointFinitePositiveTraceMatrixEndpointVectorRealization
          N f) :
    ∀ᶠ N in atTop,
      0 ≤ completedEndpointFinitePositiveTraceFrameComplementNormSq N f :=
  (completedEndpointFiniteSquareEnergyEndpointDebtDomination_eventually_source
    f hrealization).mono
    (fun N hN =>
      completedEndpointFinitePositiveTraceFrameComplementNormSq_nonnegative_of_squareEnergyEndpointDebtDomination
        N f hN)

/-- Source finite positive trace-frame construction. -/
theorem completedEndpointFinitePositiveTraceFrame_eventually_source
    (f : ZetaAdmissibleFunction)
    (hrealization :
      ∀ᶠ N in atTop,
        CompletedEndpointFinitePositiveTraceMatrixEndpointVectorRealization
          N f) :
    ∀ᶠ N in atTop,
      Nonempty (CompletedEndpointFinitePositiveTraceFrame N f) :=
  (completedEndpointFinitePositiveTraceFrameComplementNormSq_eventually_nonnegative_source
    f hrealization).mono
    (fun N hN =>
      Nonempty.intro
        (completedEndpointFinitePositiveTraceFrame_of_complementNormSq_nonnegative
          N f hN))

/-- Source finite endpoint-vector Bessel domination in the positive trace
matrix. -/
theorem completedEndpointFinitePositiveTraceMatrixEndpointBesselDomination_eventually_source
    (f : ZetaAdmissibleFunction)
    (hrealization :
      ∀ᶠ N in atTop,
        CompletedEndpointFinitePositiveTraceMatrixEndpointVectorRealization
          N f) :
    ∀ᶠ N in atTop,
      CompletedEndpointFinitePositiveTraceMatrixEndpointBesselDomination
        N f :=
  (completedEndpointFinitePositiveTraceFrame_eventually_source
    f hrealization).mono
    (fun N hN =>
      match hN with
      | ⟨frame⟩ =>
          completedEndpointFinitePositiveTraceMatrixEndpointBesselDomination_of_endpointVectorRealization
            N f
            (completedEndpointFinitePositiveTraceMatrixEndpointVectorRealization_of_traceFrame
              N f frame))

/-- Source finite positive trace-matrix kernel split. -/
theorem completedEndpointFinitePositiveTraceMatrix_kernelSplit_eventually_source
    (f : ZetaAdmissibleFunction)
    (hrealization :
      ∀ᶠ N in atTop,
        CompletedEndpointFinitePositiveTraceMatrixEndpointVectorRealization
          N f) :
    ∀ᶠ N in atTop,
      CompletedEndpointFinitePositiveTraceMatrix.KernelSplit
        (completedEndpointFinitePositiveTraceMatrix N f) :=
  (completedEndpointFinitePositiveTraceMatrixEndpointBesselDomination_eventually_source
    f hrealization).mono
    (fun N hN =>
      completedEndpointFinitePositiveTraceMatrix_kernelSplit_of_hiddenKernel_nonnegative
        N f
        (completedEndpointFinitePositiveTraceMatrix_hiddenKernel_nonnegative_of_endpointBesselDomination
          N f hN))

/-- Source hidden-kernel nonnegativity for the concrete finite positive trace
matrices. -/
theorem completedEndpointFinitePositiveTraceMatrix_hiddenKernel_eventually_nonnegative_source
    (f : ZetaAdmissibleFunction)
    (hrealization :
      ∀ᶠ N in atTop,
        CompletedEndpointFinitePositiveTraceMatrixEndpointVectorRealization
          N f) :
    ∀ᶠ N in atTop,
      0 ≤
        (completedEndpointFinitePositiveTraceMatrix N f).hiddenKernelScalar :=
  (completedEndpointFinitePositiveTraceFrame_eventually_source
    f hrealization).mono
    (fun N hN =>
      match hN with
      | ⟨frame⟩ =>
          completedEndpointFinitePositiveTraceMatrix_hiddenKernel_nonnegative_of_traceFrame
            N f frame)

/-- Source finite positive trace-matrix Schur compression. -/
theorem completedEndpointFinitePositiveTraceMatrixSchurCompression_eventually_source
    (f : ZetaAdmissibleFunction)
    (hrealization :
      ∀ᶠ N in atTop,
        CompletedEndpointFinitePositiveTraceMatrixEndpointVectorRealization
          N f) :
    ∀ᶠ N in atTop,
      CompletedEndpointFinitePositiveTraceMatrixSchurCompression N f :=
  (completedEndpointFinitePositiveTraceMatrix_hiddenKernel_eventually_nonnegative_source
    f hrealization).mono
    (fun N hN =>
      completedEndpointFinitePositiveTraceMatrixSchurCompression_of_hiddenKernel_nonnegative
        N f hN)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
