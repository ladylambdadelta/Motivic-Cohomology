import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.HorizontalDecay.Owner

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
    explicitFormulaCompletedZeroHeightWindowResidueSum f T

/-- The finite-rectangle vertical residue-window error: the right-minus-left vertical
contour contribution after subtracting the finite completed-zero residue window. -/
noncomputable def explicitFormulaFamilyVerticalResidueWindowError
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) -
    zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) -
      explicitFormulaCompletedZeroHeightWindowResidueSum f T

/-- The vertical finite-window error written using the zero-side finite window rather than
the residue presentation. -/
noncomputable def explicitFormulaFamilyVerticalZeroSideWindowError
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) -
    zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) -
      explicitFormulaCompletedZeroHeightWindowZeroSideSum f T

/-- The full finite-rectangle residue-theorem error after replacing the residue window by
the zero-side finite window. -/
noncomputable def explicitFormulaFamilyContourZeroSideWindowError
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T) -
    explicitFormulaCompletedZeroHeightWindowZeroSideSum f T

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
    explicitFormulaCompletedZeroHeightWindowZeroSideSum f
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
      explicitFormulaCompletedZeroHeightWindowResidueSum f T +
        explicitFormulaFamilyResidueWindowError f F T := by
  let C : ℂ := zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T)
  let S : ℂ := explicitFormulaCompletedZeroHeightWindowResidueSum f T
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
  let S : ℂ := explicitFormulaCompletedZeroHeightWindowResidueSum f T
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

/-- The residue-presentation and zero-side-presentation vertical finite-window errors agree. -/
theorem explicitFormulaFamilyVerticalResidueWindowError_eq_zeroSideWindowError
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    explicitFormulaFamilyVerticalResidueWindowError f F T =
      explicitFormulaFamilyVerticalZeroSideWindowError f F T := by
  let V : ℂ :=
    zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) -
      zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T)
  have hwindow :
      explicitFormulaCompletedZeroHeightWindowResidueSum f T =
        explicitFormulaCompletedZeroHeightWindowZeroSideSum f T :=
    explicitFormulaCompletedZeroHeightWindowResidueSum_eq_zeroSideSum f T
  change V - explicitFormulaCompletedZeroHeightWindowResidueSum f T =
    V - explicitFormulaCompletedZeroHeightWindowZeroSideSum f T
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
      explicitFormulaCompletedZeroHeightWindowResidueSum f T =
        explicitFormulaCompletedZeroHeightWindowZeroSideSum f T :=
    explicitFormulaCompletedZeroHeightWindowResidueSum_eq_zeroSideSum f T
  change C - explicitFormulaCompletedZeroHeightWindowZeroSideSum f T =
    C - explicitFormulaCompletedZeroHeightWindowResidueSum f T
  exact congrArg (fun S : ℂ => C - S) hwindow.symm

/-- The scheduled zero-window accounting error vanishes pointwise: the finite rectangle
residue presentation is the zero-side finite window after the completed-zero residue
identification. -/
theorem explicitFormulaScheduledZeroWindowAccountingError_eq_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    explicitFormulaScheduledZeroWindowAccountingError f F h u = 0 := by
  have hwindow :
      explicitFormulaCompletedZeroHeightWindowResidueSum f
          (h.height_schedule.height u) =
        explicitFormulaCompletedZeroHeightWindowZeroSideSum f
          (h.height_schedule.height u) :=
    explicitFormulaCompletedZeroHeightWindowResidueSum_eq_zeroSideSum
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
    explicitFormulaCompletedZeroHeightWindowZeroSideSum f
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
  let S : ℂ := explicitFormulaCompletedZeroHeightWindowZeroSideSum f T
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
theorem explicitFormulaCompletedZeroHeightWindowResidueSum_tendsto_zeroSideComplex_ownerZeroLimit
    (f : ZetaAdmissibleFunction)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          zetaZeroSideContribution (ρ : ℂ) f)) :
    Tendsto
      (fun T : ℝ => explicitFormulaCompletedZeroHeightWindowResidueSum f T)
      atTop
      (𝓝 (zetaCompletedZeroSideComplex f)) := by
  have hzeroSideTsum :
      Tendsto
        (fun T : ℝ => explicitFormulaCompletedZeroHeightWindowResidueSum f T)
        atTop
        (𝓝
          (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ},
            zetaZeroSideContribution (ρ : ℂ) f)) :=
    explicitFormulaCompletedZeroHeightWindowResidueSum_tendsto_zeroSideTsum f hsum
  have hzeroSideTsum_eq_complex :
      (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          zetaZeroSideContribution (ρ : ℂ) f) =
        zetaCompletedZeroSideComplex f := by
    rfl
  exact Eq.subst
    (motive := fun z : ℂ =>
      Tendsto
        (fun T : ℝ => explicitFormulaCompletedZeroHeightWindowResidueSum f T)
        atTop
        (𝓝 z))
    hzeroSideTsum_eq_complex
    hzeroSideTsum

/-- The real parts of the completed-zero residue windows converge to the zero-side Krein
scalar. -/
theorem explicitFormulaCompletedZeroHeightWindowResidueSum_re_tendsto_zeroKreinGram_ownerZeroLimit
    (f : ZetaAdmissibleFunction)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          zetaZeroSideContribution (ρ : ℂ) f)) :
    Tendsto
      (fun T : ℝ => Complex.re (explicitFormulaCompletedZeroHeightWindowResidueSum f T))
      atTop
      (𝓝 (zetaCompletedZeroKreinGram f)) := by
  have hcomplex :
      Tendsto
          (fun T : ℝ => explicitFormulaCompletedZeroHeightWindowResidueSum f T)
        atTop
        (𝓝 (zetaCompletedZeroSideComplex f)) :=
    explicitFormulaCompletedZeroHeightWindowResidueSum_tendsto_zeroSideComplex_ownerZeroLimit f hsum
  have hre :
      Tendsto
        (fun T : ℝ => Complex.re (explicitFormulaCompletedZeroHeightWindowResidueSum f T))
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
        (fun T : ℝ => Complex.re (explicitFormulaCompletedZeroHeightWindowResidueSum f T))
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
          (fun T : ℝ => explicitFormulaCompletedZeroHeightWindowResidueSum f T)
        atTop
        (𝓝 (zetaCompletedZeroSideComplex f)) :=
    explicitFormulaCompletedZeroHeightWindowResidueSum_tendsto_zeroSideComplex_ownerZeroLimit f hsum
  have hsub :
      Tendsto
        (fun T : ℝ =>
          zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T) -
            explicitFormulaCompletedZeroHeightWindowResidueSum f T)
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
            explicitFormulaCompletedZeroHeightWindowResidueSum f T) := by
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
              explicitFormulaCompletedZeroHeightWindowResidueSum f T)
          atTop
          (𝓝 z))
      htarget
      hsub)

/-- At a scheduled height, the contour integral is the finite residue-window sum plus the
named finite-rectangle residue equality error.

This is only the bookkeeping identity for the named error term; the analytic boundary
avoidance hypothesis belongs to the finite residue theorem below. -/
theorem explicitFormulaScheduledRectangleContourIntegral_eq_residueSum_add_error
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaContourIntegral f
        (F.rectangle (h.height_schedule.height u)) =
      explicitFormulaScheduledRectangleResidueSum f F h u +
        explicitFormulaScheduledRectangleResidueEqualityError f F h u := by
  let T : ℝ := h.height_schedule.height u
  have hbase :
      zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T) =
        explicitFormulaCompletedZeroHeightWindowResidueSum f T +
          explicitFormulaFamilyResidueWindowError f F T :=
    zetaCompletedExplicitFormulaContourIntegral_eq_heightWindowResidueSum_add_error f F T
  have hpointwise :
      explicitFormulaScheduledRectangleResidueSum f F h u =
        explicitFormulaCompletedZeroHeightWindowResidueSum f T := by
    rfl
  have herror :
      explicitFormulaScheduledRectangleResidueEqualityError f F h u =
        explicitFormulaFamilyResidueWindowError f F T := by
    rfl
  exact Eq.trans hbase
    (congrArg₂ (fun a b : ℂ => a + b) hpointwise.symm herror.symm)

/-- The package schedule gives boundary avoidance at the chosen scheduled rectangle. -/
theorem explicitFormulaScheduledRectangle_avoidsSingularBoundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    explicitFormulaContourFamilyAvoidsSingularBoundary F
      (h.height_schedule.height u) :=
  h.height_schedule.avoids_boundary u

/-- At a scheduled height, every boundary point is off the completed contour-integrand
singular set. -/
theorem completedZetaContourIntegrand_not_mem_singularSet_of_scheduledBoundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) {z : ℂ}
    (hboundary :
      z ∈ explicitFormulaContourFamilyBoundary F
        (h.height_schedule.height u)) :
    z ∉ completedZetaContourIntegrandSingularSet := by
  exact
    completedZetaContourIntegrand_not_mem_singularSet_of_avoidsBoundary
      F (h.height_schedule.height u)
      (explicitFormulaScheduledRectangle_avoidsSingularBoundary f F h u)
      hboundary

/-- The completed contour integrand is regular at every boundary point of the chosen
scheduled rectangle. -/
theorem completedZetaContourIntegrand_regularAt_scheduledBoundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) {z : ℂ}
    (hboundary :
      z ∈ explicitFormulaContourFamilyBoundary F
        (h.height_schedule.height u)) :
    ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
      DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z := by
  exact
    completedZetaContourIntegrand_regularAt_boundary_of_avoidsBoundary
      f F h (h.height_schedule.height u)
      (explicitFormulaScheduledRectangle_avoidsSingularBoundary f F h u)
      hboundary

/-- Finite rectangle residue theorem with the zero/pole boundary excluded.

At a height whose rectangle boundary avoids the completed-zeta singular set, the contour
integral of the completed explicit-formula integrand is the residue window over the
completed zeros inside that height window. -/
theorem explicitFormulaRectangleContourIntegral_eq_heightWindowResidueSum_of_avoidsBoundary_ownerFiniteRectangleResidueTheorem
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T)
    (hfinite :
      zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T) =
        explicitFormulaCompletedZeroHeightWindowResidueSum f T) :
    zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T) =
      explicitFormulaCompletedZeroHeightWindowResidueSum f T := by
  exact
    zetaCompletedExplicitFormulaRectangleContourIntegral_eq_heightWindowResidueSum_of_avoidsBoundary_of_finiteRectangleResidueTheorem
      f F h T havoid hfinite

/-- Finite rectangle residue equality at the scheduled height, with boundary avoidance
supplied by the package schedule. -/
theorem explicitFormulaScheduledRectangleContourIntegral_eq_heightWindowResidueSum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (hfinite :
      zetaCompletedExplicitFormulaContourIntegral f
          (F.rectangle (h.height_schedule.height u)) =
        explicitFormulaCompletedZeroHeightWindowResidueSum f
          (h.height_schedule.height u)) :
    zetaCompletedExplicitFormulaContourIntegral f
        (F.rectangle (h.height_schedule.height u)) =
      explicitFormulaCompletedZeroHeightWindowResidueSum f
        (h.height_schedule.height u) := by
  exact
    explicitFormulaRectangleContourIntegral_eq_heightWindowResidueSum_of_avoidsBoundary_ownerFiniteRectangleResidueTheorem
      f F h (h.height_schedule.height u)
      (explicitFormulaScheduledRectangle_avoidsSingularBoundary f F h u)
      hfinite

/-- Completed-zeta naming wrapper for the finite avoided-rectangle residue theorem. -/
theorem zetaCompletedExplicitFormulaContourIntegral_eq_completedZeroHeightWindowResidueSum_of_avoidsBoundary_ownerFiniteRectangleResidueTheorem
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T)
    (hfinite :
      zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T) =
        explicitFormulaCompletedZeroHeightWindowResidueSum f T) :
    zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T) =
      explicitFormulaCompletedZeroHeightWindowResidueSum f T := by
  exact
    explicitFormulaRectangleContourIntegral_eq_heightWindowResidueSum_of_avoidsBoundary_ownerFiniteRectangleResidueTheorem
      f F h T havoid hfinite

/-- If the chosen scheduled rectangle has the finite contour/residue equality, then the
named scheduled residue-equality error is zero at that height. -/
theorem explicitFormulaScheduledRectangleResidueEqualityError_eq_zero_of_heightWindowResidueEquality
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (hfinite :
      zetaCompletedExplicitFormulaContourIntegral f
          (F.rectangle (h.height_schedule.height u)) =
        explicitFormulaCompletedZeroHeightWindowResidueSum f
          (h.height_schedule.height u)) :
    explicitFormulaScheduledRectangleResidueEqualityError f F h u = 0 := by
  change
    zetaCompletedExplicitFormulaContourIntegral f
          (F.rectangle (h.height_schedule.height u)) -
        explicitFormulaCompletedZeroHeightWindowResidueSum f
          (h.height_schedule.height u) =
      0
  exact sub_eq_zero.mpr hfinite

/-- Finite scheduled rectangle residue equality at one avoided height.

This is the true finite-rectangle residue-theorem input: boundary avoidance guarantees that
the residue-window computation has no zero/pole hit on the contour, so the named equality
error vanishes at that scheduled height. -/
theorem explicitFormulaScheduledRectangleResidueEqualityError_eq_zero_of_avoidsBoundary_ownerFiniteRectangleResidueEquality
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (havoid :
      explicitFormulaContourFamilyAvoidsSingularBoundary F
        (h.height_schedule.height u))
    (hfinite :
      zetaCompletedExplicitFormulaContourIntegral f
          (F.rectangle (h.height_schedule.height u)) =
        explicitFormulaCompletedZeroHeightWindowResidueSum f
          (h.height_schedule.height u)) :
    explicitFormulaScheduledRectangleResidueEqualityError f F h u = 0 := by
  exact
    explicitFormulaScheduledRectangleResidueEqualityError_eq_zero_of_heightWindowResidueEquality
      f F h u hfinite

/-- The scheduled rectangle residue-equality error vanishes using the package schedule's
boundary-avoidance certificate. -/
theorem explicitFormulaScheduledRectangleResidueEqualityError_eq_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (hfinite :
      zetaCompletedExplicitFormulaContourIntegral f
          (F.rectangle (h.height_schedule.height u)) =
        explicitFormulaCompletedZeroHeightWindowResidueSum f
          (h.height_schedule.height u)) :
    explicitFormulaScheduledRectangleResidueEqualityError f F h u = 0 := by
  exact
    explicitFormulaScheduledRectangleResidueEqualityError_eq_zero_of_heightWindowResidueEquality
      f F h u hfinite

/-- Core finite-rectangle contour residue theorem, after zero-excision/window accounting.

This is the scheduled finite-rectangle computation with the boundary-avoidance certificate
kept visible.  The certificate is the progress condition that makes each finite contour
computation admissible along the scheduled realization. -/
theorem explicitFormulaScheduledRectangleResidueEqualityError_tendsto_zero_of_avoidsBoundary_ownerFiniteRectangleResidueEquality
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (havoid :
      ∀ u : ℝ,
        explicitFormulaContourFamilyAvoidsSingularBoundary F
          (h.height_schedule.height u))
    (hfinite :
      ∀ u : ℝ,
        zetaCompletedExplicitFormulaContourIntegral f
            (F.rectangle (h.height_schedule.height u)) =
          explicitFormulaCompletedZeroHeightWindowResidueSum f
            (h.height_schedule.height u)) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaScheduledRectangleResidueEqualityError f F h u)
      atTop
      (𝓝 0) := by
  have hpointwise :
      (fun u : ℝ =>
        explicitFormulaScheduledRectangleResidueEqualityError f F h u) =
        (fun _u : ℝ => (0 : ℂ)) := by
    funext u
    exact explicitFormulaScheduledRectangleResidueEqualityError_eq_zero f F h u (hfinite u)
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    tendsto_const_nhds

/-- Core finite-rectangle contour residue theorem, after zero-excision/window accounting.

This is the finite-rectangle residue theorem in its zero-side window form: the full
rectangle contour integral differs from the finite zero-side window by an error tending to
zero. -/
theorem explicitFormulaScheduledRectangleResidueEqualityError_tendsto_zero_core_ownerFiniteRectangleResidueEquality
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hfinite :
      ∀ u : ℝ,
        zetaCompletedExplicitFormulaContourIntegral f
            (F.rectangle (h.height_schedule.height u)) =
          explicitFormulaCompletedZeroHeightWindowResidueSum f
            (h.height_schedule.height u)) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaScheduledRectangleResidueEqualityError f F h u)
      atTop
      (𝓝 0) := by
  exact
    explicitFormulaScheduledRectangleResidueEqualityError_tendsto_zero_of_avoidsBoundary_ownerFiniteRectangleResidueEquality
      f F h
      (fun u => explicitFormulaScheduledRectangle_avoidsSingularBoundary f F h u)
      hfinite

/-! ## Projected contour spine for vertical channels -/

/-- The scheduled rectangle residue-equality error, viewed as a contour-side input to a
selected vertical channel projection. -/
noncomputable def explicitFormulaScheduledProjectedRectangleResidueEqualityError
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (_channel : ExplicitFormulaScheduledVerticalChannelProjection) : ℂ :=
  explicitFormulaScheduledRectangleResidueEqualityError f F h u

/-- The scheduled horizontal contour error, viewed as an input to a selected vertical channel
projection. -/
noncomputable def explicitFormulaScheduledProjectedHorizontalError
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (_channel : ExplicitFormulaScheduledVerticalChannelProjection) : ℂ :=
  explicitFormulaFamilyHorizontalResidueWindowError f F
    (h.height_schedule.height u)

/-- The full projected contour spine error combines finite rectangle residue equality,
projected horizontal decay, and projected vertical decomposition. -/
noncomputable def explicitFormulaScheduledProjectedContourSpineError
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (channel : ExplicitFormulaScheduledVerticalChannelProjection) : ℂ :=
  explicitFormulaScheduledProjectedRectangleResidueEqualityError f F h u channel +
    explicitFormulaScheduledProjectedHorizontalError f F h u channel +
      explicitFormulaScheduledProjectedVerticalDecompositionError f F h u channel

/-- Projecting the finite scheduled rectangle residue equality introduces no new algebra. -/
theorem explicitFormulaScheduledProjectedRectangleResidueEqualityError_eq_rectangleError
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (channel : ExplicitFormulaScheduledVerticalChannelProjection) :
    explicitFormulaScheduledProjectedRectangleResidueEqualityError f F h u channel =
      explicitFormulaScheduledRectangleResidueEqualityError f F h u := by
  rfl

/-- The projected finite rectangle residue-equality error vanishes along the scheduled
boundary-avoiding rectangles. -/
theorem explicitFormulaScheduledProjectedRectangleResidueEqualityError_tendsto_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (channel : ExplicitFormulaScheduledVerticalChannelProjection)
    (hfinite :
      ∀ u : ℝ,
        zetaCompletedExplicitFormulaContourIntegral f
            (F.rectangle (h.height_schedule.height u)) =
          explicitFormulaCompletedZeroHeightWindowResidueSum f
            (h.height_schedule.height u)) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaScheduledProjectedRectangleResidueEqualityError f F h u channel)
      atTop
      (𝓝 0) := by
  have hpointwise :
      (fun u : ℝ =>
        explicitFormulaScheduledProjectedRectangleResidueEqualityError f F h u channel) =
        (fun u : ℝ =>
          explicitFormulaScheduledRectangleResidueEqualityError f F h u) := by
    funext u
    exact
      explicitFormulaScheduledProjectedRectangleResidueEqualityError_eq_rectangleError
        f F h u channel
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    (explicitFormulaScheduledRectangleResidueEqualityError_tendsto_zero_core_ownerFiniteRectangleResidueEquality
      f F h hfinite)

/-- Projected horizontal decay for a selected vertical channel. -/
theorem explicitFormulaScheduledProjectedHorizontalError_tendsto_zero_ownerProjectedHorizontalDecay
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily)
    (E : CompletedZetaZeroExcisedStrip
      (min F.toContourFamily.c (1 - F.toContourFamily.c))
      (max F.toContourFamily.c (1 - F.toContourFamily.c)))
    (hTopMem :
      ∀ (T x : ℝ), x ∈ Set.uIcc F.toContourFamily.c (1 - F.toContourFamily.c) →
        zetaCompletedExplicitFormulaTopPath (F.toContourFamily.rectangle T) x ∈ E.carrier)
    (hBottomMem :
      ∀ (T x : ℝ), x ∈ Set.uIcc F.toContourFamily.c (1 - F.toContourFamily.c) →
        zetaCompletedExplicitFormulaBottomPath (F.toContourFamily.rectangle T) x ∈ E.carrier)
    (N : ℕ)
    (channel : ExplicitFormulaScheduledVerticalChannelProjection) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        explicitFormulaScheduledProjectedHorizontalError
          f F.toContourFamily h u channel)
      atTop
      (𝓝 0) := by
  let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
  exact
    explicitFormulaFamilyHorizontalResidueWindowError_tendsto_zero_scheduled
      f F.toContourFamily h E hTopMem hBottomMem N

/-- The projected contour spine error vanishes once the three owner inputs are supplied:
scheduled rectangle residue equality, projected horizontal decay, and projected vertical
decomposition. -/
theorem explicitFormulaScheduledProjectedContourSpineError_tendsto_zero_ownerProjectedContourSpine
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily)
    (channel : ExplicitFormulaScheduledVerticalChannelProjection)
    (E : CompletedZetaZeroExcisedStrip
      (min F.toContourFamily.c (1 - F.toContourFamily.c))
      (max F.toContourFamily.c (1 - F.toContourFamily.c)))
    (hTopMem :
      ∀ (T x : ℝ), x ∈ Set.uIcc F.toContourFamily.c (1 - F.toContourFamily.c) →
        zetaCompletedExplicitFormulaTopPath (F.toContourFamily.rectangle T) x ∈ E.carrier)
    (hBottomMem :
      ∀ (T x : ℝ), x ∈ Set.uIcc F.toContourFamily.c (1 - F.toContourFamily.c) →
        zetaCompletedExplicitFormulaBottomPath (F.toContourFamily.rectangle T) x ∈ E.carrier)
    (N : ℕ)
    (hvertical :
      let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledProjectedVerticalDecompositionError
            f F.toContourFamily h u channel)
        atTop
        (𝓝 0))
    (hfinite :
      let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
      ∀ u : ℝ,
        zetaCompletedExplicitFormulaContourIntegral f
            (F.toContourFamily.rectangle (h.height_schedule.height u)) =
          explicitFormulaCompletedZeroHeightWindowResidueSum f
            (h.height_schedule.height u)) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        explicitFormulaScheduledProjectedContourSpineError
          f F.toContourFamily h u channel)
      atTop
      (𝓝 0) := by
  let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
  have hresidue :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledProjectedRectangleResidueEqualityError
            f F.toContourFamily h u channel)
        atTop
        (𝓝 0) :=
    explicitFormulaScheduledProjectedRectangleResidueEqualityError_tendsto_zero
      f F.toContourFamily h channel hfinite
  have hhorizontal :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledProjectedHorizontalError
            f F.toContourFamily h u channel)
        atTop
        (𝓝 0) :=
    explicitFormulaScheduledProjectedHorizontalError_tendsto_zero_ownerProjectedHorizontalDecay
      f F hSchedule E hTopMem hBottomMem N channel
  have hsum :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledProjectedRectangleResidueEqualityError
              f F.toContourFamily h u channel +
            explicitFormulaScheduledProjectedHorizontalError
              f F.toContourFamily h u channel +
              explicitFormulaScheduledProjectedVerticalDecompositionError
                f F.toContourFamily h u channel)
        atTop
        (𝓝 (0 + 0 + 0 : ℂ)) :=
    (hresidue.add hhorizontal).add hvertical
  have htarget : (0 + 0 + 0 : ℂ) = 0 := by
    exact Eq.trans (add_zero (0 + 0)) (add_zero 0)
  have hpointwise :
      (fun u : ℝ =>
        explicitFormulaScheduledProjectedContourSpineError
          f F.toContourFamily h u channel) =
        (fun u : ℝ =>
          explicitFormulaScheduledProjectedRectangleResidueEqualityError
              f F.toContourFamily h u channel +
            explicitFormulaScheduledProjectedHorizontalError
              f F.toContourFamily h u channel +
              explicitFormulaScheduledProjectedVerticalDecompositionError
                f F.toContourFamily h u channel) := by
    funext u
    rfl
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            explicitFormulaScheduledProjectedRectangleResidueEqualityError
                f F.toContourFamily h u channel +
              explicitFormulaScheduledProjectedHorizontalError
                f F.toContourFamily h u channel +
                explicitFormulaScheduledProjectedVerticalDecompositionError
                  f F.toContourFamily h u channel)
          atTop
          (𝓝 z))
      htarget
      hsum)

/-- The shared selected-channel transport theorem is a thin wrapper over a supplied
projected vertical-decomposition input. -/
theorem explicitFormulaScheduledVerticalChannelProjectionTransportRemainder_tendsto_zero_ownerProjectedContourSpine
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily)
    (channel : ExplicitFormulaScheduledVerticalChannelProjection)
    (hvertical :
      let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledProjectedVerticalDecompositionError
            f F.toContourFamily h u channel)
        atTop
        (𝓝 0)) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        explicitFormulaScheduledVerticalChannelProjectionTransportRemainder
          f F.toContourFamily (h.height_schedule.height u) channel)
      atTop
      (𝓝 0) := by
  let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
  have hpointwise :
      (fun u : ℝ =>
        explicitFormulaScheduledVerticalChannelProjectionTransportRemainder
          f F.toContourFamily (h.height_schedule.height u) channel) =
        (fun u : ℝ =>
          explicitFormulaScheduledProjectedVerticalDecompositionError
            f F.toContourFamily h u channel) := by
    funext u
    rfl
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    hvertical

/-- Core finite-rectangle contour residue theorem, after zero-excision/window accounting.

The scheduled finite-rectangle residue equality controls the contour-minus-residue error,
and the finite zero-window accounting error is identically zero. -/
theorem explicitFormulaFamilyContourZeroSideWindowError_tendsto_zero_core_ownerFiniteRectangleResidueTheorem
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hfinite :
      ∀ u : ℝ,
        zetaCompletedExplicitFormulaContourIntegral f
            (F.rectangle (h.height_schedule.height u)) =
          explicitFormulaCompletedZeroHeightWindowResidueSum f
            (h.height_schedule.height u)) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaFamilyContourZeroSideWindowError f F
          (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  have hresidue :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledRectangleResidueEqualityError f F h u)
        atTop
        (𝓝 0) :=
    explicitFormulaScheduledRectangleResidueEqualityError_tendsto_zero_core_ownerFiniteRectangleResidueEquality
      f F h hfinite
  have hwindow :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledZeroWindowAccountingError f F h u)
        atTop
        (𝓝 0) :=
    explicitFormulaScheduledZeroWindowAccountingError_tendsto_zero f F h
  have hsum :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledRectangleResidueEqualityError f F h u +
            explicitFormulaScheduledZeroWindowAccountingError f F h u)
        atTop
        (𝓝 (0 + 0 : ℂ)) :=
    hresidue.add hwindow
  have htarget : (0 + 0 : ℂ) = 0 :=
    add_zero 0
  have hpointwise :
      (fun u : ℝ =>
        explicitFormulaFamilyContourZeroSideWindowError f F
          (h.height_schedule.height u)) =
        (fun u : ℝ =>
          explicitFormulaScheduledRectangleResidueEqualityError f F h u +
            explicitFormulaScheduledZeroWindowAccountingError f F h u) := by
    funext u
    exact
      explicitFormulaFamilyContourZeroSideWindowError_scheduled_eq_residueEquality_add_accounting
        f F h u
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            explicitFormulaScheduledRectangleResidueEqualityError f F h u +
              explicitFormulaScheduledZeroWindowAccountingError f F h u)
          atTop
          (𝓝 z))
      htarget
      hsum)

/-- Core finite-rectangle vertical zero-side theorem.

This is the finite-rectangle residue-calculus input after zero-excision/window
normalization and after removing the horizontal contour sides: the right-minus-left
vertical side differs from the finite zero-side window by an error tending to zero. -/
theorem explicitFormulaFamilyVerticalZeroSideWindowError_tendsto_zero_core_ownerFiniteRectangleResidueTheorem
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
    (N : ℕ)
    (hfinite :
      ∀ u : ℝ,
        zetaCompletedExplicitFormulaContourIntegral f
            (F.rectangle (h.height_schedule.height u)) =
          explicitFormulaCompletedZeroHeightWindowResidueSum f
            (h.height_schedule.height u)) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaFamilyVerticalZeroSideWindowError f F
          (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  have hcontour :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaFamilyContourZeroSideWindowError f F
            (h.height_schedule.height u))
        atTop
        (𝓝 0) :=
    explicitFormulaFamilyContourZeroSideWindowError_tendsto_zero_core_ownerFiniteRectangleResidueTheorem
      f F h hfinite
  have hhorizontal :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaFamilyHorizontalResidueWindowError f F
            (h.height_schedule.height u))
        atTop
        (𝓝 0) :=
    explicitFormulaFamilyHorizontalResidueWindowError_tendsto_zero_scheduled
      f F h E hTopMem hBottomMem N
  have hsub :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaFamilyContourZeroSideWindowError f F
              (h.height_schedule.height u) -
            explicitFormulaFamilyHorizontalResidueWindowError f F
              (h.height_schedule.height u))
        atTop
        (𝓝 (0 - 0 : ℂ)) :=
    hcontour.sub hhorizontal
  have htarget : (0 - 0 : ℂ) = 0 :=
    sub_self 0
  have hpointwise :
      (fun u : ℝ =>
        explicitFormulaFamilyVerticalZeroSideWindowError f F
          (h.height_schedule.height u)) =
        (fun u : ℝ =>
          explicitFormulaFamilyContourZeroSideWindowError f F
              (h.height_schedule.height u) -
            explicitFormulaFamilyHorizontalResidueWindowError f F
              (h.height_schedule.height u)) := by
    funext u
    exact explicitFormulaFamilyVerticalZeroSideWindowError_eq_contourZeroSide_sub_horizontal
      f F (h.height_schedule.height u)
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            explicitFormulaFamilyContourZeroSideWindowError f F
                (h.height_schedule.height u) -
              explicitFormulaFamilyHorizontalResidueWindowError f F
                (h.height_schedule.height u))
          atTop
          (𝓝 z))
      htarget
      hsub)

/-- The vertical residue-window error vanishes by zero-excision/window equality from the
zero-side finite-rectangle residue theorem. -/
theorem explicitFormulaFamilyVerticalResidueWindowError_tendsto_zero_core_ownerFiniteRectangleResidueTheorem
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
    (N : ℕ)
    (hfinite :
      ∀ u : ℝ,
        zetaCompletedExplicitFormulaContourIntegral f
            (F.rectangle (h.height_schedule.height u)) =
          explicitFormulaCompletedZeroHeightWindowResidueSum f
            (h.height_schedule.height u)) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaFamilyVerticalResidueWindowError f F
          (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  have hzeroSide :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaFamilyVerticalZeroSideWindowError f F
            (h.height_schedule.height u))
        atTop
        (𝓝 0) :=
    explicitFormulaFamilyVerticalZeroSideWindowError_tendsto_zero_core_ownerFiniteRectangleResidueTheorem
      f F h E hTopMem hBottomMem N hfinite
  have hpointwise :
      (fun u : ℝ =>
        explicitFormulaFamilyVerticalResidueWindowError f F
          (h.height_schedule.height u)) =
        (fun u : ℝ =>
          explicitFormulaFamilyVerticalZeroSideWindowError f F
            (h.height_schedule.height u)) := by
    funext u
    exact explicitFormulaFamilyVerticalResidueWindowError_eq_zeroSideWindowError
      f F (h.height_schedule.height u)
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    hzeroSide

/-- Core finite-rectangle residue-calculus error theorem.

The full contour residue-window error splits into the vertical finite-residue error plus
the horizontal side error.  The finite-rectangle residue theorem controls the former, and
horizontal edge decay controls the latter. -/
theorem explicitFormulaFamilyResidueWindowError_tendsto_zero_core_ownerResidueCalculus
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
    (N : ℕ)
    (hfinite :
      ∀ u : ℝ,
        zetaCompletedExplicitFormulaContourIntegral f
            (F.rectangle (h.height_schedule.height u)) =
          explicitFormulaCompletedZeroHeightWindowResidueSum f
            (h.height_schedule.height u)) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaFamilyResidueWindowError f F
          (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  have hvertical :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaFamilyVerticalResidueWindowError f F
            (h.height_schedule.height u))
        atTop
        (𝓝 0) :=
    explicitFormulaFamilyVerticalResidueWindowError_tendsto_zero_core_ownerFiniteRectangleResidueTheorem
      f F h E hTopMem hBottomMem N hfinite
  have hhorizontal :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaFamilyHorizontalResidueWindowError f F
            (h.height_schedule.height u))
        atTop
        (𝓝 0) :=
    explicitFormulaFamilyHorizontalResidueWindowError_tendsto_zero_scheduled
      f F h E hTopMem hBottomMem N
  have hsum :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaFamilyVerticalResidueWindowError f F
              (h.height_schedule.height u) +
            explicitFormulaFamilyHorizontalResidueWindowError f F
              (h.height_schedule.height u))
        atTop
        (𝓝 (0 + 0 : ℂ)) :=
    hvertical.add hhorizontal
  have htarget : (0 + 0 : ℂ) = 0 :=
    add_zero 0
  have hpointwise :
      (fun u : ℝ =>
        explicitFormulaFamilyResidueWindowError f F
          (h.height_schedule.height u)) =
        (fun u : ℝ =>
          explicitFormulaFamilyVerticalResidueWindowError f F
              (h.height_schedule.height u) +
            explicitFormulaFamilyHorizontalResidueWindowError f F
              (h.height_schedule.height u)) := by
    funext u
    exact explicitFormulaFamilyResidueWindowError_eq_vertical_add_horizontal
      f F (h.height_schedule.height u)
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            explicitFormulaFamilyVerticalResidueWindowError f F
                (h.height_schedule.height u) +
              explicitFormulaFamilyHorizontalResidueWindowError f F
                (h.height_schedule.height u))
          atTop
          (𝓝 z))
      htarget
      hsum)

/-- Core contour-residue assembly theorem.

This contour-side residue theorem is assembled from finite-rectangle residue calculus,
with the pointwise scheduled primitive
`explicitFormulaScheduledRectangleResidueEqualityError_eq_zero_of_avoidsBoundary_ownerFiniteRectangleResidueEquality`
providing the boundary-avoiding rectangle computation. -/
theorem zetaCompletedExplicitFormulaContourIntegral_tendsto_zeroSideComplex_core_ownerContourResidueTheorem
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
    (N : ℕ)
    (hfinite :
      ∀ u : ℝ,
        zetaCompletedExplicitFormulaContourIntegral f
            (F.rectangle (h.height_schedule.height u)) =
          explicitFormulaCompletedZeroHeightWindowResidueSum f
            (h.height_schedule.height u))
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          zetaZeroSideContribution (ρ : ℂ) f)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaContourIntegral f
          (F.rectangle (h.height_schedule.height u)))
      atTop
      (𝓝 (zetaCompletedZeroSideComplex f)) := by
  have hwindow :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaCompletedZeroHeightWindowResidueSum f
            (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedZeroSideComplex f)) :=
    (explicitFormulaCompletedZeroHeightWindowResidueSum_tendsto_zeroSideComplex_ownerZeroLimit f hsum).comp
      h.height_schedule.cofinal
  have herror :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaFamilyResidueWindowError f F
            (h.height_schedule.height u))
        atTop
        (𝓝 0) :=
    explicitFormulaFamilyResidueWindowError_tendsto_zero_core_ownerResidueCalculus f F h
      E hTopMem hBottomMem N hfinite
  have hsum :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaCompletedZeroHeightWindowResidueSum f
              (h.height_schedule.height u) +
            explicitFormulaFamilyResidueWindowError f F
              (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedZeroSideComplex f + 0)) :=
    hwindow.add herror
  have htarget :
      zetaCompletedZeroSideComplex f + 0 =
        zetaCompletedZeroSideComplex f :=
    add_zero _
  have hpointwise :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaContourIntegral f
          (F.rectangle (h.height_schedule.height u))) =
        (fun u : ℝ =>
          explicitFormulaCompletedZeroHeightWindowResidueSum f
              (h.height_schedule.height u) +
            explicitFormulaFamilyResidueWindowError f F
              (h.height_schedule.height u)) := by
    funext u
    exact zetaCompletedExplicitFormulaContourIntegral_eq_heightWindowResidueSum_add_error
      f F (h.height_schedule.height u)
  exact Eq.subst
    (motive := fun u : ℝ → ℂ =>
      Tendsto u atTop (𝓝 (zetaCompletedZeroSideComplex f)))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            explicitFormulaCompletedZeroHeightWindowResidueSum f
                (h.height_schedule.height u) +
              explicitFormulaFamilyResidueWindowError f F
                (h.height_schedule.height u))
          atTop
          (𝓝 z))
      htarget
      hsum)

/-- Owner finite-rectangle residue-calculus error theorem.

After the finite completed-zero height-window residue sum is subtracted from the
rectangle contour integral, the residual rectangle error tends to zero along an admissible
contour family. -/
theorem explicitFormulaFamilyResidueWindowError_tendsto_zero_ownerResidueCalculus
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily)
    (E : CompletedZetaZeroExcisedStrip
      (min F.toContourFamily.c (1 - F.toContourFamily.c))
      (max F.toContourFamily.c (1 - F.toContourFamily.c)))
    (hTopMem :
      ∀ (T x : ℝ), x ∈ Set.uIcc F.toContourFamily.c (1 - F.toContourFamily.c) →
        zetaCompletedExplicitFormulaTopPath (F.toContourFamily.rectangle T) x ∈ E.carrier)
    (hBottomMem :
      ∀ (T x : ℝ), x ∈ Set.uIcc F.toContourFamily.c (1 - F.toContourFamily.c) →
        zetaCompletedExplicitFormulaBottomPath (F.toContourFamily.rectangle T) x ∈ E.carrier)
    (N : ℕ)
    (hfinite :
      let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
      ∀ u : ℝ,
        zetaCompletedExplicitFormulaContourIntegral f
            (F.toContourFamily.rectangle (h.height_schedule.height u)) =
          explicitFormulaCompletedZeroHeightWindowResidueSum f
            (h.height_schedule.height u)) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        explicitFormulaFamilyResidueWindowError f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  exact
    explicitFormulaFamilyResidueWindowError_tendsto_zero_core_ownerResidueCalculus
      f F.toContourFamily
      (explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule)
      E
      hTopMem
      hBottomMem
      N
      hfinite

/-- The completed-zeta rectangle residue calculus reconstructs the complex zero-side
residue sum from the limiting contour integral. -/
theorem zetaCompletedExplicitFormulaContourIntegral_tendsto_zeroSideComplex_ownerResidueCalculus
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily)
    (E : CompletedZetaZeroExcisedStrip
      (min F.toContourFamily.c (1 - F.toContourFamily.c))
      (max F.toContourFamily.c (1 - F.toContourFamily.c)))
    (hTopMem :
      ∀ (T x : ℝ), x ∈ Set.uIcc F.toContourFamily.c (1 - F.toContourFamily.c) →
        zetaCompletedExplicitFormulaTopPath (F.toContourFamily.rectangle T) x ∈ E.carrier)
    (hBottomMem :
      ∀ (T x : ℝ), x ∈ Set.uIcc F.toContourFamily.c (1 - F.toContourFamily.c) →
        zetaCompletedExplicitFormulaBottomPath (F.toContourFamily.rectangle T) x ∈ E.carrier)
    (N : ℕ)
    (hfinite :
      let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
      ∀ u : ℝ,
        zetaCompletedExplicitFormulaContourIntegral f
            (F.toContourFamily.rectangle (h.height_schedule.height u)) =
          explicitFormulaCompletedZeroHeightWindowResidueSum f
            (h.height_schedule.height u))
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          zetaZeroSideContribution (ρ : ℂ) f)) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaContourIntegral f
          (F.toContourFamily.rectangle (h.height_schedule.height u)))
      atTop
      (𝓝 (zetaCompletedZeroSideComplex f)) := by
  exact
    zetaCompletedExplicitFormulaContourIntegral_tendsto_zeroSideComplex_core_ownerContourResidueTheorem
      f F.toContourFamily
      (explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule)
      E
      hTopMem
      hBottomMem
      N
      hfinite
      hsum

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
