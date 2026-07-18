import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.HorizontalDecay.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaResidueRegularity.ContourHeightWindow

/-!
# Explicit-formula finite rectangle residues

This owner layer contains finite-rectangle residue equalities, scheduled avoidance, and residue-window error transport.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The rectangle theorem applies to the factorized contour integrand once its analytic hypotheses
are provided. -/
theorem zetaCompletedExplicitFormulaRectangleBoundaryIdentity_factorized
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle)
    (f' : ℂ → (ℂ →L[ℝ] ℂ))
    (s : Set ℂ) (hs : s.Countable)
    (Hc : ContinuousOn (fun z : ℂ =>
      (- logDeriv (fun w : ℂ => completedRiemannZeta w * (Gammaℝ w)⁻¹) z) *
        zetaCompletedExplicitFormulaPhi f (z - 1 / 2))
      (Set.uIcc (r.c + (-r.T) * Complex.I).re (r.c + (r.T) * Complex.I).re ×ℂ
        Set.uIcc (r.c + (-r.T) * Complex.I).im (r.c + (r.T) * Complex.I).im))
    (Hd : ∀ x, x ∈ Set.Ioo (min (r.c + (-r.T) * Complex.I).re (r.c + (r.T) * Complex.I).re)
        (max (r.c + (-r.T) * Complex.I).re (r.c + (r.T) * Complex.I).re) ×ℂ
        Set.Ioo (min (r.c + (-r.T) * Complex.I).im (r.c + (r.T) * Complex.I).im)
          (max (r.c + (-r.T) * Complex.I).im (r.c + (r.T) * Complex.I).im) \ s →
        HasFDerivAt
          (fun z : ℂ =>
            (- logDeriv (fun w : ℂ => completedRiemannZeta w * (Gammaℝ w)⁻¹) z) *
              zetaCompletedExplicitFormulaPhi f (z - 1 / 2))
          (f' x) x)
    (Hi : IntegrableOn
      (fun z => Complex.I • ⇑(f' z) 1 - ⇑(f' z) Complex.I)
      (Set.uIcc (r.c + (-r.T) * Complex.I).re (r.c + (r.T) * Complex.I).re ×ℂ
        Set.uIcc (r.c + (-r.T) * Complex.I).im (r.c + (r.T) * Complex.I).im) volume) :
    (((∫ x in (r.c + (-r.T) * Complex.I).re..(r.c + (r.T) * Complex.I).re,
          (- logDeriv (fun w : ℂ => completedRiemannZeta w * (Gammaℝ w)⁻¹)
            (x + (r.c + (-r.T) * Complex.I).im * Complex.I)) *
            zetaCompletedExplicitFormulaPhi f
              (x + (r.c + (-r.T) * Complex.I).im * Complex.I - 1 / 2)) -
        ∫ x in (r.c + (-r.T) * Complex.I).re..(r.c + (r.T) * Complex.I).re,
          (- logDeriv (fun w : ℂ => completedRiemannZeta w * (Gammaℝ w)⁻¹)
            (x + (r.c + (r.T) * Complex.I).im * Complex.I)) *
            zetaCompletedExplicitFormulaPhi f
              (x + (r.c + (r.T) * Complex.I).im * Complex.I - 1 / 2)) +
      Complex.I • ∫ y in (r.c + (-r.T) * Complex.I).im..(r.c + (r.T) * Complex.I).im,
        (- logDeriv (fun w : ℂ => completedRiemannZeta w * (Gammaℝ w)⁻¹)
          ((r.c + (r.T) * Complex.I).re + y * Complex.I)) *
          zetaCompletedExplicitFormulaPhi f
            ((r.c + (r.T) * Complex.I).re + y * Complex.I - 1 / 2)) -
      Complex.I • ∫ y in (r.c + (-r.T) * Complex.I).im..(r.c + (r.T) * Complex.I).im,
        (- logDeriv (fun w : ℂ => completedRiemannZeta w * (Gammaℝ w)⁻¹)
          ((r.c + (-r.T) * Complex.I).re + y * Complex.I)) *
          zetaCompletedExplicitFormulaPhi f
            ((r.c + (-r.T) * Complex.I).re + y * Complex.I - 1 / 2)
      =
      ∫ x in (r.c + (-r.T) * Complex.I).re..(r.c + (r.T) * Complex.I).re,
        ∫ y in (r.c + (-r.T) * Complex.I).im..(r.c + (r.T) * Complex.I).im,
          Complex.I • ⇑(f' (x + y * Complex.I)) 1 - ⇑(f' (x + y * Complex.I)) Complex.I :=
  Complex.integral_boundary_rect_of_hasFDerivAt_real_off_countable
    (f := fun z : ℂ =>
      (- logDeriv (fun w : ℂ => completedRiemannZeta w * (Gammaℝ w)⁻¹) z) *
        zetaCompletedExplicitFormulaPhi f (z - 1 / 2))
    (f' := f') (z := r.c + (-r.T) * Complex.I) (w := r.c + (r.T) * Complex.I)
    (s := s) (hs := hs) (Hc := Hc) (Hd := Hd) (Hi := Hi)

/-- The boundary sum splits into prime, archimedean, and correction pieces. -/
theorem zetaCompletedExplicitFormulaBoundaryPieces_bridge
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundaryPieces f =
      (zetaCompletedExplicitFormulaPrimeContribution f,
        zetaCompletedExplicitFormulaArchimedeanContribution f,
        zetaCompletedExplicitFormulaCorrectionContribution f) :=
  rfl

/-- The analytic boundary sum is the sum of the three pieces. -/
theorem zetaCompletedExplicitFormulaBoundarySumAnalytic_bridge
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundarySumAnalytic f =
      zetaCompletedExplicitFormulaPrimeContribution f +
        zetaCompletedExplicitFormulaArchimedeanContribution f +
        zetaCompletedExplicitFormulaCorrectionContribution f :=
  rfl

/-- The residue-window error left after subtracting the finite completed-zero window from the
rectangle contour integral. -/
noncomputable def explicitFormulaFamilyResidueWindowError
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T) -
    explicitFormulaCompletedZeroContourHeightWindowResidueSum f T

/-- The finite-rectangle vertical residue-window error: the right-minus-left vertical
contour contribution after subtracting the finite completed-zero residue window. -/
noncomputable def explicitFormulaFamilyVerticalResidueWindowError
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) -
    zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) -
      explicitFormulaCompletedZeroContourHeightWindowResidueSum f T

/-- The vertical finite-window error written using the zero-side finite window rather than
the residue presentation. -/
noncomputable def explicitFormulaFamilyVerticalZeroSideWindowError
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) -
    zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) -
      explicitFormulaCompletedZeroContourHeightWindowZeroSideSum f T

/-- The full finite-rectangle residue-theorem error after replacing the residue window by
the zero-side finite window. -/
noncomputable def explicitFormulaFamilyContourZeroSideWindowError
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T) -
    explicitFormulaCompletedZeroContourHeightWindowZeroSideSum f T

/-- The scheduled finite-rectangle residue equality error: contour integral minus the finite
residue sum obtained from the residue theorem at the scheduled height. -/
noncomputable def explicitFormulaScheduledRectangleResidueSum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) : ℂ :=
  explicitFormulaCompletedZeroContourHeightWindowResidueSum f
    (h.height_schedule.height u)

/-- The scheduled finite-rectangle residue equality error: contour integral minus the finite
residue sum obtained from the residue theorem at the scheduled height. -/
noncomputable def explicitFormulaScheduledRectangleResidueEqualityError
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaContourIntegral f
      (F.rectangle (h.height_schedule.height u)) -
    explicitFormulaScheduledRectangleResidueSum f F h u

/-- The finite zero-window accounting error between the scheduled residue presentation and
the zero-side presentation. -/
noncomputable def explicitFormulaScheduledZeroWindowAccountingError
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) : ℂ :=
  explicitFormulaScheduledRectangleResidueSum f F h u -
    explicitFormulaCompletedZeroContourHeightWindowZeroSideSum f
      (h.height_schedule.height u)

/-- The horizontal residue-window error is the top-minus-bottom horizontal contour
contribution. -/
noncomputable def explicitFormulaFamilyHorizontalResidueWindowError
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
    zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T)

/-- The rectangle contour integral is its finite completed-zero residue window plus the
residue-window error. -/
theorem zetaCompletedExplicitFormulaContourIntegral_eq_heightWindowResidueSum_add_error
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T) =
      explicitFormulaCompletedZeroContourHeightWindowResidueSum f T +
        explicitFormulaFamilyResidueWindowError f F T := by
  let C : ℂ := zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T)
  let S : ℂ := explicitFormulaCompletedZeroContourHeightWindowResidueSum f T
  change C = S + (C - S)
  calc
    C = C + 0 := by
      exact (add_zero C).symm
    _ = C + (-S + S) := by
      exact congrArg (fun x : ℂ => C + x) (neg_add_cancel S).symm
    _ = (C + -S) + S := by
      exact (add_assoc C (-S) S).symm
    _ = S + (C + -S) := by
      exact add_comm (C + -S) S
    _ = S + (C - S) := by
      exact congrArg (fun x : ℂ => S + x) (sub_eq_add_neg C S).symm

/-- The full residue-window error is the sum of the vertical finite-residue error and the
horizontal top-minus-bottom error. -/
theorem explicitFormulaFamilyResidueWindowError_eq_vertical_add_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    explicitFormulaFamilyResidueWindowError f F T =
      explicitFormulaFamilyVerticalResidueWindowError f F T +
        explicitFormulaFamilyHorizontalResidueWindowError f F T := by
  let R : ℂ := zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T)
  let L : ℂ := zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T)
  let U : ℂ := zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T)
  let B : ℂ := zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T)
  let S : ℂ := explicitFormulaCompletedZeroContourHeightWindowResidueSum f T
  change (R - L + U - B) - S = (R - L - S) + (U - B)
  calc
    (R - L + U - B) - S = ((R - L) + U - B) - S := by
      rfl
    _ = (((R - L) + U) - B) - S := by
      rfl
    _ = (((R - L) + U) + -B) + -S := by
      exact sub_eq_add_neg (((R - L) + U) - B) S
    _ = ((R - L) + U + -B) + -S := by
      rfl
    _ = (R - L) + (U + -B) + -S := by
      exact congrArg (fun x : ℂ => x + -S) (add_assoc (R - L) U (-B))
    _ = (R - L) + (U - B) + -S := by
      exact congrArg (fun x : ℂ => (R - L) + x + -S) (sub_eq_add_neg U B).symm
    _ = (R - L) + ((U - B) + -S) := by
      exact add_assoc (R - L) (U - B) (-S)
    _ = (R - L) + (-S + (U - B)) := by
      exact congrArg (fun x : ℂ => (R - L) + x) (add_comm (U - B) (-S))
    _ = ((R - L) + -S) + (U - B) := by
      exact (add_assoc (R - L) (-S) (U - B)).symm
    _ = (R - L - S) + (U - B) := by
      exact congrArg (fun x : ℂ => x + (U - B)) (sub_eq_add_neg (R - L) S).symm

/-- The horizontal residue-window error is exactly the horizontal difference controlled by
the family horizontal-decay theorem. -/
theorem explicitFormulaFamilyHorizontalResidueWindowError_tendsto_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (T x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath (F.rectangle T) x ∈ E.carrier)
    (hBottomMem :
      ∀ (T x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x ∈ E.carrier)
    (N : ℕ) :
    Tendsto
      (fun T : ℝ => explicitFormulaFamilyHorizontalResidueWindowError f F T)
      atTop
      (𝓝 0) := by
  exact h.horizontalDecay E hTopMem hBottomMem N

/-- The horizontal residue-window error also vanishes along the cofinal avoiding schedule. -/
theorem explicitFormulaFamilyHorizontalResidueWindowError_tendsto_zero_scheduled
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (T x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath (F.rectangle T) x ∈ E.carrier)
    (hBottomMem :
      ∀ (T x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x ∈ E.carrier)
    (N : ℕ) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaFamilyHorizontalResidueWindowError f F
          (h.height_schedule.height u))
      atTop
      (𝓝 0) :=
  (explicitFormulaFamilyHorizontalResidueWindowError_tendsto_zero
      f F h E hTopMem hBottomMem N).comp h.height_schedule.cofinal

/-- The horizontal residue-window error vanishes along the cofinal avoiding schedule,
requiring zero-excised strip membership only at the scheduled heights. -/
theorem explicitFormulaFamilyHorizontalResidueWindowError_tendsto_zero_of_scheduledMembership
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier)
    (hBottomMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier)
    (N : ℕ) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaFamilyHorizontalResidueWindowError f F
          (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  exact
    zetaCompletedExplicitFormulaHorizontalDifference_tendsto_zero_scheduled
      F h E hTopMem hBottomMem N

/-- The horizontal residue-window error vanishes along the cofinal avoiding schedule using
the scheduled horizontal-edge carrier constructed by the analytic package. -/
theorem explicitFormulaFamilyHorizontalResidueWindowError_tendsto_zero_of_scheduledCarrier
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (N : ℕ) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaFamilyHorizontalResidueWindowError f F
          (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  exact
    zetaCompletedExplicitFormulaHorizontalDifference_tendsto_zero_of_scheduledCarrier
      F h N

/-- The completed-zero residue window and the zero-side window are the same finite sum
after both are expressed at the centered completed-zero coordinate. -/
theorem explicitFormulaCompletedZeroContourHeightWindowResidueSum_eq_zeroSideSum
    (f : ZetaAdmissibleFunction) (T : ℝ) :
    explicitFormulaCompletedZeroContourHeightWindowResidueSum f T =
      explicitFormulaCompletedZeroContourHeightWindowZeroSideSum f T := by
  unfold explicitFormulaCompletedZeroContourHeightWindowResidueSum
  unfold explicitFormulaCompletedZeroContourHeightWindowZeroSideSum
  exact Finset.sum_congr rfl
    (fun ρ _hρ => by
      calc
        explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ) =
            - (zetaZeroMultiplicity (ρ : ℂ) : ℂ) *
              zetaCompletedExplicitFormulaPhi f (ρ : ℂ) := by
          exact explicitFormulaZeroResidue_ofCompletedZero_unfold f ρ
        _ = - (zetaZeroMultiplicity (ρ : ℂ) : ℂ) *
              zetaSpectralEval f (ρ : ℂ) := by
          rfl
        _ = zetaZeroSideContribution (ρ : ℂ) f := by
          exact (zetaZeroSideContribution_def (ρ : ℂ) f).symm)

/-- The completed-zero residue windows converge to the zero-side `tsum`. -/
theorem explicitFormulaCompletedZeroContourHeightWindowResidueSum_tendsto_zeroSideTsum
    (f : ZetaAdmissibleFunction)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          zetaZeroSideContribution (ρ : ℂ) f)) :
    Tendsto
      (fun T : ℝ => explicitFormulaCompletedZeroContourHeightWindowResidueSum f T)
      atTop
      (𝓝
        (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          zetaZeroSideContribution (ρ : ℂ) f)) := by
  have hzero :
      Tendsto
        (fun T : ℝ => explicitFormulaCompletedZeroContourHeightWindowZeroSideSum f T)
        atTop
        (𝓝
          (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ},
            zetaZeroSideContribution (ρ : ℂ) f)) :=
    explicitFormulaCompletedZeroContourHeightWindowZeroSideSum_tendsto_tsum f hsum
  have hpointwise :
      (fun T : ℝ => explicitFormulaCompletedZeroContourHeightWindowResidueSum f T) =
        fun T : ℝ => explicitFormulaCompletedZeroContourHeightWindowZeroSideSum f T := by
    funext T
    exact explicitFormulaCompletedZeroContourHeightWindowResidueSum_eq_zeroSideSum f T
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ =>
      Tendsto φ atTop
        (𝓝
          (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ},
            zetaZeroSideContribution (ρ : ℂ) f)))
    hpointwise.symm
    hzero

/-- The residue-presentation and zero-side-presentation vertical finite-window errors agree. -/
theorem explicitFormulaFamilyVerticalResidueWindowError_eq_zeroSideWindowError
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    explicitFormulaFamilyVerticalResidueWindowError f F T =
      explicitFormulaFamilyVerticalZeroSideWindowError f F T := by
  let V : ℂ :=
    zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) -
      zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T)
  have hwindow :
      explicitFormulaCompletedZeroContourHeightWindowResidueSum f T =
        explicitFormulaCompletedZeroContourHeightWindowZeroSideSum f T :=
    explicitFormulaCompletedZeroContourHeightWindowResidueSum_eq_zeroSideSum f T
  change V - explicitFormulaCompletedZeroContourHeightWindowResidueSum f T =
    V - explicitFormulaCompletedZeroContourHeightWindowZeroSideSum f T
  exact congrArg (fun S : ℂ => V - S) hwindow

/-- If the zero-side presentation of the vertical finite-window error vanishes, then so does
the residue presentation. -/
theorem explicitFormulaFamilyVerticalResidueWindowError_tendsto_zero_of_zeroSideWindowError
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hzeroSide :
      Tendsto
        (fun T : ℝ => explicitFormulaFamilyVerticalZeroSideWindowError f F T)
        atTop
        (𝓝 0)) :
    Tendsto
      (fun T : ℝ => explicitFormulaFamilyVerticalResidueWindowError f F T)
      atTop
      (𝓝 0) := by
  have hpointwise :
      (fun T : ℝ => explicitFormulaFamilyVerticalResidueWindowError f F T) =
        (fun T : ℝ => explicitFormulaFamilyVerticalZeroSideWindowError f F T) := by
    funext T
    exact explicitFormulaFamilyVerticalResidueWindowError_eq_zeroSideWindowError f F T
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    hzeroSide

/-- Replacing the residue window by the zero-side window in the full contour error is only
the finite zero-window accounting identity. -/
theorem explicitFormulaFamilyContourZeroSideWindowError_eq_residueWindowError
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    explicitFormulaFamilyContourZeroSideWindowError f F T =
      explicitFormulaFamilyResidueWindowError f F T := by
  let C : ℂ := zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T)
  have hwindow :
      explicitFormulaCompletedZeroContourHeightWindowResidueSum f T =
        explicitFormulaCompletedZeroContourHeightWindowZeroSideSum f T :=
    explicitFormulaCompletedZeroContourHeightWindowResidueSum_eq_zeroSideSum f T
  change C - explicitFormulaCompletedZeroContourHeightWindowZeroSideSum f T =
    C - explicitFormulaCompletedZeroContourHeightWindowResidueSum f T
  exact congrArg (fun S : ℂ => C - S) hwindow.symm

/-- The scheduled zero-window accounting error vanishes pointwise: the finite rectangle
residue presentation is the zero-side finite window after the completed-zero residue
identification. -/
theorem explicitFormulaScheduledZeroWindowAccountingError_eq_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    explicitFormulaScheduledZeroWindowAccountingError f F h u = 0 := by
  have hwindow :
      explicitFormulaCompletedZeroContourHeightWindowResidueSum f
          (h.height_schedule.height u) =
        explicitFormulaCompletedZeroContourHeightWindowZeroSideSum f
          (h.height_schedule.height u) :=
    explicitFormulaCompletedZeroContourHeightWindowResidueSum_eq_zeroSideSum
      f (h.height_schedule.height u)
  exact sub_eq_zero.mpr hwindow

/-- The scheduled zero-window accounting error tends to zero. -/
theorem explicitFormulaScheduledZeroWindowAccountingError_tendsto_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ => explicitFormulaScheduledZeroWindowAccountingError f F h u)
      atTop
      (𝓝 0) := by
  have hpointwise :
      (fun u : ℝ => explicitFormulaScheduledZeroWindowAccountingError f F h u) =
        (fun _u : ℝ => (0 : ℂ)) := by
    funext u
    exact explicitFormulaScheduledZeroWindowAccountingError_eq_zero f F h u
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    tendsto_const_nhds

/-- The scheduled contour zero-side error splits into the finite scheduled rectangle residue
equality error plus the finite zero-window accounting error. -/
theorem explicitFormulaFamilyContourZeroSideWindowError_scheduled_eq_residueEquality_add_accounting
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    explicitFormulaFamilyContourZeroSideWindowError f F
        (h.height_schedule.height u) =
      explicitFormulaScheduledRectangleResidueEqualityError f F h u +
        explicitFormulaScheduledZeroWindowAccountingError f F h u := by
  let C : ℂ :=
    zetaCompletedExplicitFormulaContourIntegral f
      (F.rectangle (h.height_schedule.height u))
  let R : ℂ := explicitFormulaScheduledRectangleResidueSum f F h u
  let Z : ℂ :=
    explicitFormulaCompletedZeroContourHeightWindowZeroSideSum f
      (h.height_schedule.height u)
  change C - Z = (C - R) + (R - Z)
  calc
    C - Z = C + -Z := by
      exact sub_eq_add_neg C Z
    _ = C + (0 + -Z) := by
      exact congrArg (fun x : ℂ => C + x) (zero_add (-Z)).symm
    _ = C + ((-R + R) + -Z) := by
      exact congrArg (fun x : ℂ => C + (x + -Z)) (neg_add_cancel R).symm
    _ = C + (-R + (R + -Z)) := by
      exact congrArg (fun x : ℂ => C + x) (add_assoc (-R) R (-Z))
    _ = (C + -R) + (R + -Z) := by
      exact (add_assoc C (-R) (R + -Z)).symm
    _ = (C - R) + (R + -Z) := by
      exact congrArg (fun x : ℂ => x + (R + -Z)) (sub_eq_add_neg C R).symm
    _ = (C - R) + (R - Z) := by
      exact congrArg (fun x : ℂ => (C - R) + x) (sub_eq_add_neg R Z).symm

/-- The vertical zero-side window error is the full finite-rectangle residue-theorem error
with the horizontal side contribution subtracted. -/
theorem explicitFormulaFamilyVerticalZeroSideWindowError_eq_contourZeroSide_sub_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    explicitFormulaFamilyVerticalZeroSideWindowError f F T =
      explicitFormulaFamilyContourZeroSideWindowError f F T -
        explicitFormulaFamilyHorizontalResidueWindowError f F T := by
  let R : ℂ := zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T)
  let L : ℂ := zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T)
  let U : ℂ := zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T)
  let B : ℂ := zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T)
  let S : ℂ := explicitFormulaCompletedZeroContourHeightWindowZeroSideSum f T
  change R - L - S = ((R - L + U - B) - S) - (U - B)
  exact (calc
    ((R - L + U - B) - S) - (U - B)
        = (((R - L) + U - B) - S) - (U - B) := by
      rfl
    _ = ((((R - L) + U) - B) - S) - (U - B) := by
      rfl
    _ = ((((R - L) + U) + -B) + -S) + -(U - B) := by
      exact sub_eq_add_neg ((((R - L) + U) - B) - S) (U - B)
    _ = (((R - L) + U + -B) + -S) + -(U - B) := by
      rfl
    _ = (((R - L) + (U + -B)) + -S) + -(U - B) := by
      exact congrArg (fun x : ℂ => (x + -S) + -(U - B))
        (add_assoc (R - L) U (-B))
    _ = (((R - L) + (U - B)) + -S) + -(U - B) := by
      exact congrArg (fun x : ℂ => (((R - L) + x) + -S) + -(U - B))
        (sub_eq_add_neg U B).symm
    _ = ((R - L) + ((U - B) + -S)) + -(U - B) := by
      exact congrArg (fun x : ℂ => x + -(U - B))
        (add_assoc (R - L) (U - B) (-S))
    _ = ((R - L) + (-S + (U - B))) + -(U - B) := by
      exact congrArg (fun x : ℂ => ((R - L) + x) + -(U - B))
        (add_comm (U - B) (-S))
    _ = (((R - L) + -S) + (U - B)) + -(U - B) := by
      exact congrArg (fun x : ℂ => x + -(U - B))
        (add_assoc (R - L) (-S) (U - B)).symm
    _ = ((R - L) + -S) + ((U - B) + -(U - B)) := by
      exact add_assoc ((R - L) + -S) (U - B) (-(U - B))
    _ = ((R - L) + -S) + 0 := by
      exact congrArg (fun x : ℂ => ((R - L) + -S) + x) (add_neg_cancel (U - B))
    _ = (R - L) + -S := by
      exact add_zero ((R - L) + -S)
    _ = R - L - S := by
      exact (sub_eq_add_neg (R - L) S).symm
  ).symm

/-- Owner complex zero-limit theorem for the finite completed-zero residue windows.

This is the zero-side summability/Jensen input specialized to the residue windows:
the finite height-window residue sums converge to the completed complex zero-side residue
sum.  Passing to the Krein scalar is a real-part operation, not a complex equality with a
coerced real number. -/
theorem explicitFormulaCompletedZeroContourHeightWindowResidueSum_tendsto_zeroSideComplex_ownerZeroLimit
    (f : ZetaAdmissibleFunction)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          zetaZeroSideContribution (ρ : ℂ) f)) :
    Tendsto
      (fun T : ℝ => explicitFormulaCompletedZeroContourHeightWindowResidueSum f T)
      atTop
      (𝓝 (zetaCompletedZeroSideComplex f)) := by
  have hzeroSideTsum :
      Tendsto
        (fun T : ℝ => explicitFormulaCompletedZeroContourHeightWindowResidueSum f T)
        atTop
        (𝓝
          (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ},
            zetaZeroSideContribution (ρ : ℂ) f)) :=
    explicitFormulaCompletedZeroContourHeightWindowResidueSum_tendsto_zeroSideTsum f hsum
  have hzeroSideTsum_eq_complex :
      (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          zetaZeroSideContribution (ρ : ℂ) f) =
        zetaCompletedZeroSideComplex f := by
    rfl
  exact Eq.subst
    (motive := fun z : ℂ =>
      Tendsto
        (fun T : ℝ => explicitFormulaCompletedZeroContourHeightWindowResidueSum f T)
        atTop
        (𝓝 z))
    hzeroSideTsum_eq_complex
    hzeroSideTsum

/-- The real parts of the completed-zero residue windows converge to the zero-side Krein
scalar. -/
theorem explicitFormulaCompletedZeroContourHeightWindowResidueSum_re_tendsto_zeroKreinGram_ownerZeroLimit
    (f : ZetaAdmissibleFunction)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          zetaZeroSideContribution (ρ : ℂ) f)) :
    Tendsto
      (fun T : ℝ => Complex.re (explicitFormulaCompletedZeroContourHeightWindowResidueSum f T))
      atTop
      (𝓝 (zetaCompletedZeroKreinGram f)) := by
  have hcomplex :
      Tendsto
          (fun T : ℝ => explicitFormulaCompletedZeroContourHeightWindowResidueSum f T)
        atTop
        (𝓝 (zetaCompletedZeroSideComplex f)) :=
    explicitFormulaCompletedZeroContourHeightWindowResidueSum_tendsto_zeroSideComplex_ownerZeroLimit f hsum
  have hre :
      Tendsto
        (fun T : ℝ => Complex.re (explicitFormulaCompletedZeroContourHeightWindowResidueSum f T))
        atTop
        (𝓝 (Complex.re (zetaCompletedZeroSideComplex f))) :=
    (Complex.continuous_re.tendsto (zetaCompletedZeroSideComplex f)).comp hcomplex
  have htarget :
      Complex.re (zetaCompletedZeroSideComplex f) =
        zetaCompletedZeroKreinGram f := by
    rfl
  exact Eq.subst
    (motive := fun x : ℝ =>
      Tendsto
        (fun T : ℝ => Complex.re (explicitFormulaCompletedZeroContourHeightWindowResidueSum f T))
        atTop
        (𝓝 x))
    htarget
    hre

/-- If the contour integrals themselves converge to the completed complex zero side, then
the finite-height residue-window error vanishes. -/
theorem explicitFormulaFamilyResidueWindowError_tendsto_zero_of_contourIntegral_tendsto_zeroSideComplex
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          zetaZeroSideContribution (ρ : ℂ) f))
    (hcontour :
      Tendsto
        (fun T : ℝ =>
          zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T))
        atTop
        (𝓝 (zetaCompletedZeroSideComplex f))) :
    Tendsto
      (fun T : ℝ => explicitFormulaFamilyResidueWindowError f F T)
      atTop
      (𝓝 0) := by
  have hwindow :
      Tendsto
          (fun T : ℝ => explicitFormulaCompletedZeroContourHeightWindowResidueSum f T)
        atTop
        (𝓝 (zetaCompletedZeroSideComplex f)) :=
    explicitFormulaCompletedZeroContourHeightWindowResidueSum_tendsto_zeroSideComplex_ownerZeroLimit f hsum
  have hsub :
      Tendsto
        (fun T : ℝ =>
          zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T) -
            explicitFormulaCompletedZeroContourHeightWindowResidueSum f T)
        atTop
        (𝓝 (zetaCompletedZeroSideComplex f - zetaCompletedZeroSideComplex f)) :=
    hcontour.sub hwindow
  have htarget :
      zetaCompletedZeroSideComplex f - zetaCompletedZeroSideComplex f = 0 := by
    exact sub_self _
  have hpointwise :
      (fun T : ℝ => explicitFormulaFamilyResidueWindowError f F T) =
        (fun T : ℝ =>
          zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T) -
            explicitFormulaCompletedZeroContourHeightWindowResidueSum f T) := by
    funext T
    rfl
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun T : ℝ =>
            zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T) -
              explicitFormulaCompletedZeroContourHeightWindowResidueSum f T)
          atTop
          (𝓝 z))
      htarget
      hsub)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
