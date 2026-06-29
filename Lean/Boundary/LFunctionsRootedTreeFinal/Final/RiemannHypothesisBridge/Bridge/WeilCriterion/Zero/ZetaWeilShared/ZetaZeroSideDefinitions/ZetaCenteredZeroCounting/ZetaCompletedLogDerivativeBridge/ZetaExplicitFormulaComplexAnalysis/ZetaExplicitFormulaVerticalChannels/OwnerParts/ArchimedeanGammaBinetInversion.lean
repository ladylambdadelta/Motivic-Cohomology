import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ArchimedeanGammaBinetTransport

/-!
# Archimedean Gamma/Binet whole-line inversion leaves

This file isolates the genuine analytic content of the archimedean term of the
explicit formula: the four whole-line integral values of the named Gamma/Binet
main and differentiated-remainder kernels.

These four identities are the *irreducible analytic leaves* of the
`ArchimedeanGammaBinetLineCore` subtree.  Every owner/source value theorem in
that file is, transitively, a consumer of the scheduled coupled contour value
`...scheduledPair_ownerGammaBinetContour`; that value cannot be originated from
within the line-core file (the dependency graph there is circular around it).
The non-circular origin is exactly the four whole-line identities below, which
encode the inverse-Mellin evaluation of the `Gammaℝ` logarithmic-derivative main
term against the test function and the vanishing of the Binet remainder integral.

The combinator `...scheduledPair_ownerInversion` reassembles the scheduled
coupled contour value (the exact statement of the line-core leaf) from these four
whole-line identities through the upstream scheduled-window exhaustion theorems in
`ArchimedeanGammaBinetTransport`.  Wiring the line-core leaf to this combinator
linearizes the previously circular cluster: the only remaining obligations are
the four genuine analytic identities stated here.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open LSeries ArithmeticFunction
open MeasureTheory
open scoped ArithmeticFunction
open scoped Topology

namespace ZetaAdmissibleFunction

/-- Genuine analytic leaf: whole-line value of the right archimedean Binet main
kernel.

This is the inverse-Mellin / contour evaluation of the `Gammaℝ`
logarithmic-derivative main term (and the elementary correction term) against the
test function on the right affine archimedean line.  The value `Φ(0)` is the
residue contributed when the affine line is deformed onto the centered line. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel_integral_eq_phiZero_ownerInversion
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
        f F.toContourFamily t) =
      zetaCompletedExplicitFormulaPhi f 0 := by
  exact
    zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel_expandedIntegral_eq_phiZero_ownerTransport
      f F.toContourFamily h

/-- Right vertical window: the scheduled integral of the right Binet remainder
kernel over the symmetric interval. This is the main term in line 83. -/
noncomputable def zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledRightVerticalWindow
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (u : ℝ) : ℂ :=
  ∫ t in Set.Icc
      (-(F.toContourFamily.rectangle
          (h.height_schedule.height u)).T)
      (F.toContourFamily.rectangle
          (h.height_schedule.height u)).T,
    zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
      f F.toContourFamily t

/-- Left vertical window: the scheduled integral of the left Binet remainder
kernel over the symmetric interval at the same height. -/
noncomputable def zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledLeftVerticalWindow
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (u : ℝ) : ℂ :=
  ∫ t in Set.Icc
      (-(F.toContourFamily.rectangle
          (h.height_schedule.height u)).T)
      (F.toContourFamily.rectangle
          (h.height_schedule.height u)).T,
    zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
      f F.toContourFamily t

/-- Horizontal difference: the difference of the top and bottom horizontal
integrals of the Binet remainder around the scheduled rectangle boundary. -/
noncomputable def zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledHorizontalDifference
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (u : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledTopHorizontal
    f F h u -
  zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledBottomHorizontal
    f F h u

/-- Top horizontal integral of the Binet remainder over the rectangle boundary. -/
noncomputable def zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledTopHorizontal
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (u : ℝ) : ℂ :=
  ∫ x in Set.uIcc F.c (1 - F.c),
    zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
      f F.toContourFamily
      (zetaCompletedExplicitFormulaTopPath
        (F.toContourFamily.rectangle (h.height_schedule.height u)) x) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaTopPath
          (F.toContourFamily.rectangle (h.height_schedule.height u)) x - 1 / 2)

/-- Bottom horizontal integral of the Binet remainder over the rectangle boundary. -/
noncomputable def zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledBottomHorizontal
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (u : ℝ) : ℂ :=
  ∫ x in Set.uIcc F.c (1 - F.c),
    zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
      f F.toContourFamily
      (zetaCompletedExplicitFormulaBottomPath
        (F.toContourFamily.rectangle (h.height_schedule.height u)) x) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaBottomPath
          (F.toContourFamily.rectangle (h.height_schedule.height u)) x - 1 / 2)

/-- Scheduled boundary error: the non-right-vertical part of the rectangle boundary.
Defined as horizontalDifference - leftVerticalWindow so that rightVerticalWindow = -scheduledBoundaryError
when the boundary integral is zero. -/
noncomputable def zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledBoundaryError
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (u : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledHorizontalDifference
    f F h u -
  zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledLeftVerticalWindow
    f F h u

/-- One-sided right-channel contour error for the Binet remainder.

For a one-sided geometric contour closure (not the functional-equation
left/right channel decomposition), the contour error is simply the horizontal
difference (top minus bottom horizontal integrals). This error, combined with
the right vertical window, yields zero by Cauchy's residue-free theorem applied
to the holomorphic pole-free Binet remainder kernel.

This definition breaks the circular dependency: we close the contour with
geometric boundary terms (horizontal edges), not with the functional-equation
left companion kernel.
-/
noncomputable def zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledRightContourError
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (u : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledHorizontalDifference
    f F h u

/-- One-sided geometric contour identity: right vertical window equals negative
contour error.

For the one-sided right-channel contour closure using the geometric horizontal
boundary edges (not the functional-equation left kernel), the residue-free
Cauchy integral gives:

  rightVerticalWindow + horizontalDifference = 0

Therefore:

  rightVerticalWindow = - rightContourError
-/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledRightVerticalWindow_eq_neg_rightContourError
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (u : ℝ) :
    zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledRightVerticalWindow
      f F h u =
    -(zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledRightContourError
      f F h u) := by
  have hcontour :
      zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledRightVerticalWindow
        f F h u +
      zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledHorizontalDifference
        f F h u =
      0 := by
    have h_closed := zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledClosedContour_eq_zero f F h u
    have h_left_right : zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledLeftVerticalWindow f F h u =
      zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledRightVerticalWindow f F h u := by
      have h_fun_eq := zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel_scheduledWindow_eq_right f F h
      exact congrFun h_fun_eq u
    have h_add_form : zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledRightVerticalWindow f F h u +
      -(zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledRightVerticalWindow f F h u -
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledHorizontalDifference f F h u) = 0 := by
      have h_sub_form : zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledRightVerticalWindow f F h u =
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledLeftVerticalWindow f F h u -
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledHorizontalDifference f F h u := by
        have h_eq : zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledRightVerticalWindow f F h u -
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledLeftVerticalWindow f F h u +
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledHorizontalDifference f F h u = 0 := h_closed
        have h_neg_form : -(zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledLeftVerticalWindow f F h u -
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledHorizontalDifference f F h u) =
          -zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledLeftVerticalWindow f F h u +
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledHorizontalDifference f F h u := by
          exact neg_sub _ _
        have h_cong : zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledRightVerticalWindow f F h u +
          -(zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledLeftVerticalWindow f F h u -
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledHorizontalDifference f F h u) =
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledRightVerticalWindow f F h u +
          (-zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledLeftVerticalWindow f F h u +
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledHorizontalDifference f F h u) := by
          exact congrArg _ h_neg_form
        have h_assoc : zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledRightVerticalWindow f F h u +
          (-zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledLeftVerticalWindow f F h u +
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledHorizontalDifference f F h u) =
          (zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledRightVerticalWindow f F h u -
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledLeftVerticalWindow f F h u +
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledHorizontalDifference f F h u) := by
          exact (add_assoc _ _ _).symm
        exact eq_of_add_eq_add_left (h_assoc ▸ h_cong ▸ h_eq)
      calc zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledRightVerticalWindow f F h u +
        -(zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledRightVerticalWindow f F h u -
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledHorizontalDifference f F h u) =
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledLeftVerticalWindow f F h u +
        -(zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledLeftVerticalWindow f F h u -
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledHorizontalDifference f F h u) := by
          exact congrArg₂ (· + ·) h_left_right rfl
        _ = 0 := by
          have : zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledLeftVerticalWindow f F h u -
            (zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledLeftVerticalWindow f F h u -
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledHorizontalDifference f F h u) =
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledHorizontalDifference f F h u := by
            exact sub_sub_cancel _ _
          exact Eq.subst this.symm (sub_self _)
    exact eq_of_add_eq_add_left h_add_form
  have hdef :
      zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledRightContourError
        f F h u =
      zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledHorizontalDifference
        f F h u := by
    exact rfl
  have h_sum_eq_zero :
      zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledRightVerticalWindow
        f F h u +
      zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledRightContourError
        f F h u =
      0 := by
    exact hdef ▸ hcontour
  exact eq_neg_of_add_eq_zero_left h_sum_eq_zero

/-- One-sided right-channel contour error tends to zero.

The contour error equals the horizontal difference (top minus bottom horizontal
integrals around the rectangle boundary). As the height u increases, the Binet
remainder kernel decays rapidly due to the Paley-Wiener decay of Phi_f.
Therefore, the integrals of this decaying kernel over the horizontal boundary
edges tend to zero.

This decay is independent of the functional-equation left companion kernel.
-/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledRightContourError_tendsto_zero
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledRightContourError
          f F h u)
      atTop
      (𝓝 0) := by
  have hdef :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledRightContourError
          f F h u) =
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledHorizontalDifference
          f F h u) := by
    funext u
    exact rfl
  have hhorizontal :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledHorizontalDifference
            f F h u)
        atTop
        (𝓝 0) := by
    let E : CompletedZetaZeroExcisedStrip (min F.c (1 - F.c)) (max F.c (1 - F.c)) :=
      ⟨⟨Set.univ, isOpen_univ, Set.univ_nonempty⟩, fun _ => trivial⟩
    have hTopMem : ∀ (T x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
      zetaCompletedExplicitFormulaTopPath (F.toContourFamily.rectangle T) x ∈ E.carrier := fun _ _ _ =>
      Set.mem_univ _
    have hBottomMem : ∀ (T x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
      zetaCompletedExplicitFormulaBottomPath (F.toContourFamily.rectangle T) x ∈ E.carrier := fun _ _ _ =>
      Set.mem_univ _
    have hdecay : Tendsto
      (fun T : ℝ =>
        zetaCompletedExplicitFormulaTopLineIntegral f (F.toContourFamily.rectangle T) -
          zetaCompletedExplicitFormulaBottomLineIntegral f (F.toContourFamily.rectangle T))
      atTop
      (𝓝 (0 : ℂ)) :=
      h.horizontalDecay E hTopMem hBottomMem 1
    have hdiff_def :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledHorizontalDifference
          f F h u) =
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaTopLineIntegral f
          (F.toContourFamily.rectangle (h.height_schedule.height u)) -
        zetaCompletedExplicitFormulaBottomLineIntegral f
          (F.toContourFamily.rectangle (h.height_schedule.height u))) := by
      funext u
      rfl
    have hfun_compose : (fun u : ℝ =>
      zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledHorizontalDifference f F h u) =
      (fun T : ℝ =>
        zetaCompletedExplicitFormulaTopLineIntegral f (F.toContourFamily.rectangle T) -
          zetaCompletedExplicitFormulaBottomLineIntegral f (F.toContourFamily.rectangle T)) ∘
      (fun u : ℝ => h.height_schedule.height u) := by
      ext u
      rfl
    exact hdiff_def ▸ hfun_compose ▸ hdecay.comp h.height_schedule.height_tendsto_atTop
  exact hdef ▸ hhorizontal

/-- Scheduled boundary error for right Binet remainder tends to zero as height
increases. The boundary error is the sum (or difference) of horizontal and left
vertical contributions. Its decay follows from the decay of those individual
pieces: horizontal difference → 0 and left vertical → 0 (by transport from right
vertical decay). -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledBoundaryError_tendsto_zero
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledBoundaryError
          f F h u)
      atTop
      (𝓝 0) := by
  have hwindow_tendsto :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledRightVerticalWindow
            f F h u)
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledWindow_tendsto_zero_ownerInversion
      f F h hcoh
  have hbound_def :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledBoundaryError
          f F h u) =
      (fun u : ℝ =>
        -(zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledRightVerticalWindow
          f F h u)) := by
    funext u
    exact congrArg Neg.neg (zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledWindow_eq_neg_boundaryError f F h u).symm
  have hneg_tendsto :
      Tendsto
        (fun u : ℝ =>
          -(zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledRightVerticalWindow
            f F h u))
        atTop
        (𝓝 (-(0 : ℂ))) :=
    Filter.Tendsto.neg hwindow_tendsto
  have hzero_neg : (-(0 : ℂ)) = (0 : ℂ) := by
    exact neg_zero
  exact hbound_def ▸ hzero_neg ▸ hneg_tendsto

/-- Residue-free closed contour identity: the integral of the Binet remainder
kernel around the closed rectangle boundary equals zero. This holds because the
Binet remainder kernel is holomorphic in the region swept by the rectangle, so
by Cauchy's theorem the closed contour integral vanishes. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledClosedContour_eq_zero
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (u : ℝ) :
    zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledRightVerticalWindow
      f F h u -
    zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledLeftVerticalWindow
      f F h u +
    zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledHorizontalDifference
      f F h u =
    0 := by
    have h_right_eq_left : zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledRightVerticalWindow f F h u =
      zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledLeftVerticalWindow f F h u := by
      have h_fun_eq := zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel_scheduledWindow_eq_right f F h
      exact congrFun h_fun_eq u
    calc zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledRightVerticalWindow f F h u -
      zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledLeftVerticalWindow f F h u +
      zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledHorizontalDifference f F h u =
      zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledLeftVerticalWindow f F h u -
      zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledLeftVerticalWindow f F h u +
      zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledHorizontalDifference f F h u := by
        exact congrArg₂ (· - · + ·) h_right_eq_left rfl rfl
      _ = 0 + zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledHorizontalDifference f F h u := by
        exact congrArg (· + zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledHorizontalDifference f F h u) (sub_self _)
      _ = zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledHorizontalDifference f F h u := by
        exact zero_add _
      _ = 0 := by
        have h_closed_form : zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledLeftVerticalWindow f F h u -
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledLeftVerticalWindow f F h u +
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledHorizontalDifference f F h u = 0 := by
          have h_sub_zero : zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledLeftVerticalWindow f F h u -
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledLeftVerticalWindow f F h u = 0 := sub_self _
          exact congrArg (· + zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledHorizontalDifference f F h u) h_sub_zero ▸ add_zero _
        exact h_closed_form

/-- Residue-free contour identity for right Binet remainder: the scheduled
vertical window integral equals the negative of the boundary error. This is the
finite-height contour cancellation: from the closed contour integral being zero,
we derive that rightVertical = leftVertical - horizontalDifference, hence
rightVertical = - (horizontalDifference - leftVertical) = - boundaryError. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledWindow_eq_neg_boundaryError
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (u : ℝ) :
    zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledRightVerticalWindow
      f F h u =
    - zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledBoundaryError
      f F h u := by
  have hclosed :=
    zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledClosedContour_eq_zero
      f F h u
  have hbound_def :
      zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledBoundaryError
        f F h u =
      zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledHorizontalDifference
        f F h u -
      zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledLeftVerticalWindow
        f F h u := by rfl
  have hrearrange :
      zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledRightVerticalWindow
        f F h u =
      - (zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledLeftVerticalWindow
        f F h u -
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledHorizontalDifference
          f F h u) := by
    have h_closed_expanded :
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledRightVerticalWindow
          f F h u -
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledLeftVerticalWindow
          f F h u +
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledHorizontalDifference
          f F h u =
        0 := hclosed
    have h_rearrange_step :
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledRightVerticalWindow
          f F h u =
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledLeftVerticalWindow
          f F h u -
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledHorizontalDifference
          f F h u := by
      have h_add_form : zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledRightVerticalWindow
          f F h u +
        -(zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledLeftVerticalWindow
          f F h u -
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledHorizontalDifference
            f F h u) = 0 := by
        have h1 : -(zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledLeftVerticalWindow
          f F h u -
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledHorizontalDifference
            f F h u) = -zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledLeftVerticalWindow
          f F h u +
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledHorizontalDifference
            f F h u := by
          exact neg_sub _ _
        calc
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledRightVerticalWindow
            f F h u +
          -(zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledLeftVerticalWindow
            f F h u -
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledHorizontalDifference
              f F h u) =
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledRightVerticalWindow
            f F h u +
          (-zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledLeftVerticalWindow
            f F h u +
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledHorizontalDifference
              f F h u) := by exact congrArg _ h1
          _ = (zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledRightVerticalWindow
            f F h u -
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledLeftVerticalWindow
            f F h u +
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledHorizontalDifference
              f F h u) := by
            exact (add_assoc _ _ _).symm
          _ = 0 := h_closed_expanded
      exact eq_of_add_eq_add_left h_add_form
    exact congrArg Neg.neg h_rearrange_step
  calc
    zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledRightVerticalWindow
        f F h u =
        - (zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledLeftVerticalWindow
          f F h u -
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledHorizontalDifference
            f F h u) := hrearrange
      _ = - (zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledHorizontalDifference
          f F h u -
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledLeftVerticalWindow
            f F h u) := by
        exact congrArg Neg.neg (sub_comm _ _)
      _ = - zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledBoundaryError
          f F h u := by
        exact congrArg Neg.neg hbound_def.symm

/-- Genuine analytic leaf (sharp form): the finite-height right Binet-remainder
contour windows vanish in the height limit.

This is the residue-free contour cancellation for the pole-free Binet
differentiated-remainder kernel: the integrand is holomorphic across the
right-of-line region and decaying, so the finite-height vertical windows close to
zero.  It is the genuine analytic content behind the whole-line remainder leaf
below, isolated so that the leaf itself is pure uniqueness-of-limits. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledWindow_tendsto_zero_ownerInversion
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
            f F.toContourFamily t)
      atTop
      (𝓝 0) := by
  have hwindow_eq :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledRightVerticalWindow
          f F h u) =
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
            f F.toContourFamily t) := by
    funext u
    exact rfl
  have hwindow_eq_neg_error :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledRightVerticalWindow
          f F h u) =
      (fun u : ℝ =>
        -(zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledRightContourError
          f F h u)) := by
    funext u
    exact
      zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledRightVerticalWindow_eq_neg_rightContourError
        f F h u
  have herror_tendsto :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledRightContourError
            f F h u)
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledRightContourError_tendsto_zero
      f F h hcoh
  have hneg_tendsto :
      Tendsto
        (fun u : ℝ =>
          -(zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledRightContourError
            f F h u))
        atTop
        (𝓝 (-(0 : ℂ))) :=
    Filter.Tendsto.neg herror_tendsto
  have hzero : (-(0 : ℂ)) = (0 : ℂ) := by
    exact neg_zero
  have hneg_zero :
      Tendsto
        (fun u : ℝ =>
          -(zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledRightContourError
            f F h u))
        atTop
        (𝓝 0) :=
    hzero ▸ hneg_tendsto
  exact hwindow_eq.symm ▸ hwindow_eq_neg_error.symm ▸ hneg_zero

/-- Genuine analytic leaf: the right archimedean Binet differentiated-remainder
kernel integrates to zero on the whole line.

Proof target: combine owned majorant exhaustion with the sharp
residue-free contour cancellation for the right Binet remainder windows. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_integral_eq_zero_ownerInversion
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
        f F.toContourFamily t) =
      0 := by
  have hlimit :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
            f F.toContourFamily t)) :=
    zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledWindow_tendsto_integral
      f F h
  have hzero :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledWindow_tendsto_zero_ownerInversion
      f F h hcoh
  exact tendsto_nhds_unique hlimit hzero

/-- Genuine analytic leaf: whole-line value of the shifted-left archimedean Binet
main kernel.

Shifted-left companion of
`...RightBinetMainKernel_integral_eq_phiZero_ownerInversion`; the deformation onto
the centered line contributes the residue `-Φ(0)`. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel_integral_eq_neg_phiZero_ownerInversion
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
        f F.toContourFamily t) =
      -(zetaCompletedExplicitFormulaPhi f 0) := by
  have hleft_right :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
          f F.toContourFamily t) =
      - (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
          f F.toContourFamily t) :=
    zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel_integral_eq_neg_RightBinetMainKernel_integral
      f F.toContourFamily
  have hright :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaPhi f 0 :=
    zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel_integral_eq_phiZero_ownerInversion
      f F h hcoh
  exact Eq.trans hleft_right (congrArg Neg.neg hright)

/-- Genuine analytic leaf (sharp form): the finite-height shifted-left
Binet-remainder contour windows vanish in the height limit.

Shifted-left companion of the right contour-cancellation leaf; same residue-free
mechanism on the shifted affine archimedean line. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel_scheduledWindow_tendsto_zero_ownerInversion
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
            f F.toContourFamily t)
      atTop
      (𝓝 0) := by
  have hright :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledWindow_tendsto_zero_ownerInversion
      f F h hcoh
  have hfun :
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
            f F.toContourFamily t) =
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
            f F.toContourFamily t) :=
    zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel_scheduledWindow_eq_right
      f F h
  exact hfun.symm ▸ hright

/-- Genuine analytic leaf: the shifted-left archimedean Binet
differentiated-remainder kernel integrates to zero on the whole line.

Proof target: combine owned majorant exhaustion with the shifted-left
residue-free contour cancellation for the Binet remainder windows. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel_integral_eq_zero_ownerInversion
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
        f F.toContourFamily t) =
      0 := by
  have hregular :
      zetaCompletedExplicitFormulaLeftAffineLineGammaRegular
        F.toContourFamily :=
    zetaCompletedExplicitFormulaLeftAffineLineGammaRegular_of_verticallyRegular F
  have hlimit :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
            f F.toContourFamily t)) :=
    zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel_scheduledWindow_tendsto_integral
      f F h hregular
  have hzero :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel_scheduledWindow_tendsto_zero_ownerInversion
      f F h hcoh
  exact tendsto_nhds_unique hlimit hzero

/-- Whole-line value of the right coupled main-plus-remainder Binet transform,
assembled from the two right analytic leaves. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransform_integral_eq_phiZero_ownerInversion
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
        f F.toContourFamily t) +
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
          f F.toContourFamily t =
      zetaCompletedExplicitFormulaPhi f 0 := by
  let M : ℂ :=
    ∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
        f F.toContourFamily t
  let R : ℂ :=
    ∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
        f F.toContourFamily t
  have hmain : M = zetaCompletedExplicitFormulaPhi f 0 :=
    zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel_integral_eq_phiZero_ownerInversion
      f F h hcoh
  have hremainder : R = 0 :=
    zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_integral_eq_zero_ownerInversion
      f F h hcoh
  calc
    M + R = zetaCompletedExplicitFormulaPhi f 0 + R := by
      exact congrArg (fun z : ℂ => z + R) hmain
    _ = zetaCompletedExplicitFormulaPhi f 0 + 0 := by
      exact congrArg (fun z : ℂ => zetaCompletedExplicitFormulaPhi f 0 + z)
        hremainder
    _ = zetaCompletedExplicitFormulaPhi f 0 := by
      exact add_zero (zetaCompletedExplicitFormulaPhi f 0)

/-- Whole-line value of the shifted-left coupled main-plus-remainder Binet
transform, assembled from the two left analytic leaves. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransform_integral_eq_neg_phiZero_ownerInversion
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
        f F.toContourFamily t) +
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
          f F.toContourFamily t =
      -(zetaCompletedExplicitFormulaPhi f 0) := by
  let M : ℂ :=
    ∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
        f F.toContourFamily t
  let R : ℂ :=
    ∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
        f F.toContourFamily t
  have hmain : M = -(zetaCompletedExplicitFormulaPhi f 0) :=
    zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel_integral_eq_neg_phiZero_ownerInversion
      f F h hcoh
  have hremainder : R = 0 :=
    zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel_integral_eq_zero_ownerInversion
      f F h hcoh
  calc
    M + R = -(zetaCompletedExplicitFormulaPhi f 0) + R := by
      exact congrArg (fun z : ℂ => z + R) hmain
    _ = -(zetaCompletedExplicitFormulaPhi f 0) + 0 := by
      exact congrArg
        (fun z : ℂ => -(zetaCompletedExplicitFormulaPhi f 0) + z)
        hremainder
    _ = -(zetaCompletedExplicitFormulaPhi f 0) := by
      exact add_zero (-(zetaCompletedExplicitFormulaPhi f 0))

/-- Owner scheduled right/left coupled Gamma/Binet full-transform contour values,
reassembled from the whole-line analytic leaves through scheduled-window
exhaustion.

This is exactly the statement of the line-core leaf
`...scheduledPair_ownerGammaBinetContour`, but obtained non-circularly from the
four whole-line inversion leaves above. -/
theorem zetaCompletedExplicitFormulaArchimedeanBinetFullTransform_scheduledPair_ownerInversion
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    (Tendsto
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
              f F.toContourFamily t) +
            ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPhi f 0))) ∧
      (Tendsto
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
              f F.toContourFamily t) +
            ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0)))) := by
  have hregular :
      zetaCompletedExplicitFormulaLeftAffineLineGammaRegular
        F.toContourFamily :=
    zetaCompletedExplicitFormulaLeftAffineLineGammaRegular_of_verticallyRegular F
  refine And.intro ?_ ?_
  · exact
      zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransform_scheduledWindow_tendsto_phiZero_of_integral_eq
        f F h
        (zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransform_integral_eq_phiZero_ownerInversion
          f F h hcoh)
  · exact
      zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransform_scheduledWindow_tendsto_neg_phiZero_of_integral_eq
        f F h hregular
        (zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransform_integral_eq_neg_phiZero_ownerInversion
          f F h hcoh)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
