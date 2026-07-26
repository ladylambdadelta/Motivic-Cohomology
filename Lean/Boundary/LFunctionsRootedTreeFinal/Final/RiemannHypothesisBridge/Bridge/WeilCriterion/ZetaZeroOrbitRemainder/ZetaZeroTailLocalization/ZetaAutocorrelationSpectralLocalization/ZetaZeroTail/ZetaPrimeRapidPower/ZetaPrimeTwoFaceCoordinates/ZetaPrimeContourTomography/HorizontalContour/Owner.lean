import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.CoordinateLedger.ConcreteResidueShadow

/-!
# Prime contour tomography

This owner layer is split from the public tomography owner.  It preserves the
public theorem names while keeping the proof graph in smaller linear layers.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The sampled top horizontal contour integral along a supplied height schedule. -/
noncomputable def sampledHorizontalTopIntegralAt
    (heightSchedule :
      ExplicitFormulaCofinalHeightSchedule completedPrimeContourTransportFamily)
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaTopLineIntegral
      (convolutionAutocorrelation f)
      (completedPrimeContourTransportFamily.rectangle
        (heightSchedule.height (N : ℝ)))

/-- The sampled bottom horizontal contour integral along a supplied height schedule. -/
noncomputable def sampledHorizontalBottomIntegralAt
    (heightSchedule :
      ExplicitFormulaCofinalHeightSchedule completedPrimeContourTransportFamily)
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaBottomLineIntegral
      (convolutionAutocorrelation f)
      (completedPrimeContourTransportFamily.rectangle
        (heightSchedule.height (N : ℝ)))

/-- The sampled horizontal top-minus-bottom contour remainder along a supplied schedule. -/
noncomputable def sampledHorizontalDifferenceComplexAt
    (heightSchedule :
      ExplicitFormulaCofinalHeightSchedule completedPrimeContourTransportFamily)
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℂ :=
  sampledHorizontalTopIntegralAt heightSchedule N f -
    sampledHorizontalBottomIntegralAt heightSchedule N f

/-- The scheduled top horizontal integral is the top edge integral of the prime
transport rectangle. -/
theorem sampledHorizontalTopIntegralAt_eq_topLineIntegral
    (heightSchedule :
      ExplicitFormulaCofinalHeightSchedule completedPrimeContourTransportFamily)
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    sampledHorizontalTopIntegralAt heightSchedule N f =
      zetaCompletedExplicitFormulaTopLineIntegral
        (convolutionAutocorrelation f)
        (completedPrimeContourTransportFamily.rectangle
          (heightSchedule.height (N : ℝ))) :=
  rfl

/-- The scheduled bottom horizontal integral is the bottom edge integral of the prime
transport rectangle. -/
theorem sampledHorizontalBottomIntegralAt_eq_bottomLineIntegral
    (heightSchedule :
      ExplicitFormulaCofinalHeightSchedule completedPrimeContourTransportFamily)
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    sampledHorizontalBottomIntegralAt heightSchedule N f =
      zetaCompletedExplicitFormulaBottomLineIntegral
        (convolutionAutocorrelation f)
        (completedPrimeContourTransportFamily.rectangle
          (heightSchedule.height (N : ℝ))) :=
  rfl

/-- The scheduled horizontal difference is the scheduled top edge minus the scheduled
bottom edge. -/
theorem sampledHorizontalDifferenceComplexAt_eq_top_sub_bottom
    (heightSchedule :
      ExplicitFormulaCofinalHeightSchedule completedPrimeContourTransportFamily)
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    sampledHorizontalDifferenceComplexAt heightSchedule N f =
      sampledHorizontalTopIntegralAt heightSchedule N f -
        sampledHorizontalBottomIntegralAt heightSchedule N f :=
  rfl

/-- The concrete sampled top horizontal contour integral. -/
noncomputable def sampledHorizontalTopIntegral
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℂ :=
  sampledHorizontalTopIntegralAt
    completedPrimeContourTransportHeightSchedule_owner N f

/-- The concrete sampled bottom horizontal contour integral. -/
noncomputable def sampledHorizontalBottomIntegral
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℂ :=
  sampledHorizontalBottomIntegralAt
    completedPrimeContourTransportHeightSchedule_owner N f

/-- The concrete sampled horizontal top-minus-bottom contour remainder. -/
noncomputable def sampledHorizontalDifferenceComplex
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℂ :=
  sampledHorizontalDifferenceComplexAt
    completedPrimeContourTransportHeightSchedule_owner N f

/-- The sampled top horizontal integral is the top edge integral of the prime transport
rectangle. -/
theorem sampledHorizontalTopIntegral_eq_topLineIntegral
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    sampledHorizontalTopIntegral N f =
      zetaCompletedExplicitFormulaTopLineIntegral
        (convolutionAutocorrelation f)
        (completedPrimeContourTransportFamily.rectangle
          (completedPrimeContourTransportHeightSchedule_owner.height (N : ℝ))) := by
  rfl

/-- The sampled bottom horizontal integral is the bottom edge integral of the prime
transport rectangle. -/
theorem sampledHorizontalBottomIntegral_eq_bottomLineIntegral
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    sampledHorizontalBottomIntegral N f =
      zetaCompletedExplicitFormulaBottomLineIntegral
        (convolutionAutocorrelation f)
        (completedPrimeContourTransportFamily.rectangle
          (completedPrimeContourTransportHeightSchedule_owner.height (N : ℝ))) := by
  rfl

/-- The sampled horizontal difference is the sampled top edge minus the sampled bottom
edge. -/
theorem sampledHorizontalDifferenceComplex_eq_top_sub_bottom
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    sampledHorizontalDifferenceComplex N f =
      sampledHorizontalTopIntegral N f -
        sampledHorizontalBottomIntegral N f := by
  rfl

/-- The top horizontal contour integrand along the prime transport rectangle. -/
noncomputable def primeTransportTopContourIntegrand
    (N : ℕ) (f : ZetaAdmissibleFunction) (x : ℝ) : ℂ :=
  completedZetaNegLogDeriv
      (zetaCompletedExplicitFormulaTopPath
        (completedPrimeContourTransportFamily.rectangle
          (completedPrimeContourTransportHeightSchedule_owner.height (N : ℝ))) x) *
    zetaCompletedExplicitFormulaPhi
      (convolutionAutocorrelation f)
      (zetaCompletedExplicitFormulaTopPath
        (completedPrimeContourTransportFamily.rectangle
          (completedPrimeContourTransportHeightSchedule_owner.height (N : ℝ))) x - 1 / 2)

/-- The bottom horizontal contour integrand along the prime transport rectangle. -/
noncomputable def primeTransportBottomContourIntegrand
    (N : ℕ) (f : ZetaAdmissibleFunction) (x : ℝ) : ℂ :=
  completedZetaNegLogDeriv
      (zetaCompletedExplicitFormulaBottomPath
        (completedPrimeContourTransportFamily.rectangle
          (completedPrimeContourTransportHeightSchedule_owner.height (N : ℝ))) x) *
    zetaCompletedExplicitFormulaPhi
      (convolutionAutocorrelation f)
      (zetaCompletedExplicitFormulaBottomPath
        (completedPrimeContourTransportFamily.rectangle
          (completedPrimeContourTransportHeightSchedule_owner.height (N : ℝ))) x - 1 / 2)

/-- The top line integral is the interval integral of the named top contour integrand. -/
theorem primeTransportTopLineIntegral_eq_integral_topContourIntegrand
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaTopLineIntegral
        (convolutionAutocorrelation f)
        (completedPrimeContourTransportFamily.rectangle
          (completedPrimeContourTransportHeightSchedule_owner.height (N : ℝ))) =
      ∫ x in Set.uIcc completedPrimeContourTransportFamily.c
          (1 - completedPrimeContourTransportFamily.c),
        primeTransportTopContourIntegrand N f x := by
  rfl

/-- The bottom line integral is the interval integral of the named bottom contour
integrand. -/
theorem primeTransportBottomLineIntegral_eq_integral_bottomContourIntegrand
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBottomLineIntegral
        (convolutionAutocorrelation f)
        (completedPrimeContourTransportFamily.rectangle
          (completedPrimeContourTransportHeightSchedule_owner.height (N : ℝ))) =
      ∫ x in Set.uIcc completedPrimeContourTransportFamily.c
          (1 - completedPrimeContourTransportFamily.c),
        primeTransportBottomContourIntegrand N f x := by
  rfl

/-- The named top contour-integrand integral along the prime transport rectangle. -/
noncomputable def primeTransportTopContourIntegral
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℂ :=
  ∫ x in Set.uIcc completedPrimeContourTransportFamily.c
      (1 - completedPrimeContourTransportFamily.c),
    primeTransportTopContourIntegrand N f x

/-- The named bottom contour-integrand integral along the prime transport rectangle. -/
noncomputable def primeTransportBottomContourIntegral
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℂ :=
  ∫ x in Set.uIcc completedPrimeContourTransportFamily.c
      (1 - completedPrimeContourTransportFamily.c),
    primeTransportBottomContourIntegrand N f x

/-- The top contour integral unfolds to the interval integral of its named integrand. -/
theorem primeTransportTopContourIntegral_eq_integral
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    primeTransportTopContourIntegral N f =
      ∫ x in Set.uIcc completedPrimeContourTransportFamily.c
          (1 - completedPrimeContourTransportFamily.c),
        primeTransportTopContourIntegrand N f x := by
  rfl

/-- The bottom contour integral unfolds to the interval integral of its named integrand. -/
theorem primeTransportBottomContourIntegral_eq_integral
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    primeTransportBottomContourIntegral N f =
      ∫ x in Set.uIcc completedPrimeContourTransportFamily.c
          (1 - completedPrimeContourTransportFamily.c),
        primeTransportBottomContourIntegrand N f x := by
  rfl

/-- The top line integral is the named top contour integral. -/
theorem primeTransportTopLineIntegral_eq_topContourIntegral
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaTopLineIntegral
        (convolutionAutocorrelation f)
        (completedPrimeContourTransportFamily.rectangle
          (completedPrimeContourTransportHeightSchedule_owner.height (N : ℝ))) =
      primeTransportTopContourIntegral N f := by
  exact
    (primeTransportTopLineIntegral_eq_integral_topContourIntegrand N f).trans
      (primeTransportTopContourIntegral_eq_integral N f).symm

/-- The bottom line integral is the named bottom contour integral. -/
theorem primeTransportBottomLineIntegral_eq_bottomContourIntegral
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBottomLineIntegral
        (convolutionAutocorrelation f)
        (completedPrimeContourTransportFamily.rectangle
          (completedPrimeContourTransportHeightSchedule_owner.height (N : ℝ))) =
      primeTransportBottomContourIntegral N f := by
  exact
    (primeTransportBottomLineIntegral_eq_integral_bottomContourIntegrand N f).trans
      (primeTransportBottomContourIntegral_eq_integral N f).symm

/-- One symmetrized complex prime coordinate sampled from a boundary channel. -/
noncomputable def finitePrimeSymmetrizedComplexCoordinate
    (A : ℝ → ℂ) (ι : ZetaPrimePowerIndex) : ℂ :=
  -((ι.weight : ℂ) * (A ι.center + star (A ι.center)))

/-- A finite symmetrized complex prime window sampled from a boundary channel. -/
noncomputable def finitePrimeSymmetrizedComplexWindow
    (N : ℕ) (A : ℝ → ℂ) : ℂ :=
  ∑ ι in ZetaPrimePowerIndex.window N,
    finitePrimeSymmetrizedComplexCoordinate A ι

/-- The symmetrized complex coordinate unfolds to its sampled boundary expression. -/
theorem finitePrimeSymmetrizedComplexCoordinate_eq
    (A : ℝ → ℂ) (ι : ZetaPrimePowerIndex) :
    finitePrimeSymmetrizedComplexCoordinate A ι =
      -((ι.weight : ℂ) * (A ι.center + star (A ι.center))) := by
  rfl

/-- The symmetrized complex window unfolds to the finite sum of its coordinates. -/
theorem finitePrimeSymmetrizedComplexWindow_eq_sum
    (N : ℕ) (A : ℝ → ℂ) :
    finitePrimeSymmetrizedComplexWindow N A =
      ∑ ι in ZetaPrimePowerIndex.window N,
        finitePrimeSymmetrizedComplexCoordinate A ι := by
  rfl

/-- The finite complex contour-realized prime coordinate is the symmetrized spectral
boundary coordinate. -/
noncomputable def finitePrimeContourRealizedComplexCoordinate
    (ι : ZetaPrimePowerIndex) (g : ZetaAdmissibleFunction) : ℂ :=
  finitePrimeSymmetrizedComplexCoordinate
    (fun a : ℝ => zetaCompletedSpectralLaplaceTransform g a) ι

/-- The finite complex contour-realized prime window before taking its real shadow. -/
noncomputable def finitePrimeContourRealizedComplexWindow
    (N : ℕ) (g : ZetaAdmissibleFunction) : ℂ :=
  finitePrimeSymmetrizedComplexWindow N
    (fun a : ℝ => zetaCompletedSpectralLaplaceTransform g a)

/-- The contour-realized complex coordinate is the symmetrized spectral coordinate. -/
theorem finitePrimeContourRealizedComplexCoordinate_eq_symmetrizedSpectral
    (ι : ZetaPrimePowerIndex) (g : ZetaAdmissibleFunction) :
    finitePrimeContourRealizedComplexCoordinate ι g =
      finitePrimeSymmetrizedComplexCoordinate
        (fun a : ℝ => zetaCompletedSpectralLaplaceTransform g a) ι := by
  rfl

/-- The contour-realized complex window is the symmetrized spectral window. -/
theorem finitePrimeContourRealizedComplexWindow_eq_symmetrizedSpectral
    (N : ℕ) (g : ZetaAdmissibleFunction) :
    finitePrimeContourRealizedComplexWindow N g =
      finitePrimeSymmetrizedComplexWindow N
        (fun a : ℝ => zetaCompletedSpectralLaplaceTransform g a) := by
  rfl

/-- The contour-realized complex window is the finite sum of contour-realized complex
coordinates. -/
theorem finitePrimeContourRealizedComplexWindow_eq_coordinateSum
    (N : ℕ) (g : ZetaAdmissibleFunction) :
    finitePrimeContourRealizedComplexWindow N g =
      ∑ ι in ZetaPrimePowerIndex.window N,
        finitePrimeContourRealizedComplexCoordinate ι g := by
  rfl

/-- The symmetrized spectral window is the finite sum of contour-realized complex
coordinates. -/
theorem finitePrimeSymmetrizedSpectralWindow_eq_contourRealizedComplexCoordinateSum
    (N : ℕ) (g : ZetaAdmissibleFunction) :
    finitePrimeSymmetrizedComplexWindow N
        (fun a : ℝ => zetaCompletedSpectralLaplaceTransform g a) =
      ∑ ι in ZetaPrimePowerIndex.window N,
        finitePrimeContourRealizedComplexCoordinate ι g := by
  exact
    (finitePrimeContourRealizedComplexWindow_eq_symmetrizedSpectral N g).symm.trans
      (finitePrimeContourRealizedComplexWindow_eq_coordinateSum N g)

/-- The finite contour-realized complex coordinate unfolds to the spectral Laplace
coordinate expression. -/
theorem finitePrimeContourRealizedComplexCoordinate_eq
    (ι : ZetaPrimePowerIndex) (g : ZetaAdmissibleFunction) :
    finitePrimeContourRealizedComplexCoordinate ι g =
      -((ι.weight : ℂ) *
        (zetaCompletedSpectralLaplaceTransform g ι.center +
          star (zetaCompletedSpectralLaplaceTransform g ι.center))) := by
  rfl

/-- The real part of one finite contour-realized complex coordinate is the corresponding
contour-realized real coordinate. -/
theorem finitePrimeContourRealizedComplexCoordinate_re_eq_contourRealizedCoordinate
    (ι : ZetaPrimePowerIndex) (g : ZetaAdmissibleFunction) :
    Complex.re (finitePrimeContourRealizedComplexCoordinate ι g) =
      completedPrimeContourRealizedTimeDistributionCoordinate ι g := by
  rfl

/-- The real part of the finite complex contour-realized prime window is the finite sum of
contour-realized coordinates. -/
theorem finitePrimeContourRealizedComplexWindow_re_eq_coordinateSum
    (N : ℕ) (g : ZetaAdmissibleFunction) :
    Complex.re (finitePrimeContourRealizedComplexWindow N g) =
      ∑ ι in ZetaPrimePowerIndex.window N,
        completedPrimeContourRealizedTimeDistributionCoordinate ι g := by
  exact
    (Complex.re_sum
      (ZetaPrimePowerIndex.window N)
      (fun ι : ZetaPrimePowerIndex =>
        finitePrimeContourRealizedComplexCoordinate ι g)).trans
      (Finset.sum_congr
        rfl
        (fun ι _ =>
          finitePrimeContourRealizedComplexCoordinate_re_eq_contourRealizedCoordinate
            ι g))

/-- The real part of the displayed finite contour-realized complex coordinate sum is the
finite sum of contour-realized real coordinates. -/
theorem finitePrimeContourRealizedComplexCoordinateSum_re_eq_coordinateSum
    (N : ℕ) (g : ZetaAdmissibleFunction) :
    Complex.re
        (∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeContourRealizedComplexCoordinate ι g) =
      ∑ ι in ZetaPrimePowerIndex.window N,
        completedPrimeContourRealizedTimeDistributionCoordinate ι g := by
  exact finitePrimeContourRealizedComplexWindow_re_eq_coordinateSum N g

/-- The real part of the finite complex contour-realized prime window is the finite
contour-realized prime window. -/
theorem finitePrimeContourRealizedComplexWindow_re_eq_window
    (N : ℕ) (g : ZetaAdmissibleFunction) :
    Complex.re (finitePrimeContourRealizedComplexWindow N g) =
      finitePrimeContourRealizedTimeDistributionWindow N g := by
  exact
    (finitePrimeContourRealizedComplexWindow_re_eq_coordinateSum N g).trans
      (finitePrimeContourRealizedTimeDistributionWindow_eq_sum_coordinate N g).symm

/-- The finite complex time-side prime window before taking its real shadow. -/
noncomputable def finitePrimeTimeDistributionComplexCoordinate
    (ι : ZetaPrimePowerIndex) (g : ZetaAdmissibleFunction) : ℂ :=
  finitePrimeSymmetrizedComplexCoordinate
    (fun a : ℝ => zetaCompletedTimeBoundaryValue g a) ι

/-- The finite complex time-side prime window before taking its real shadow. -/
noncomputable def finitePrimeTimeDistributionComplexWindow
    (N : ℕ) (g : ZetaAdmissibleFunction) : ℂ :=
  finitePrimeSymmetrizedComplexWindow N
    (fun a : ℝ => zetaCompletedTimeBoundaryValue g a)

/-- The time-side complex coordinate is the symmetrized time-boundary coordinate. -/
theorem finitePrimeTimeDistributionComplexCoordinate_eq_symmetrizedTime
    (ι : ZetaPrimePowerIndex) (g : ZetaAdmissibleFunction) :
    finitePrimeTimeDistributionComplexCoordinate ι g =
      finitePrimeSymmetrizedComplexCoordinate
        (fun a : ℝ => zetaCompletedTimeBoundaryValue g a) ι := by
  rfl

/-- The time-side complex window is the symmetrized time-boundary window. -/
theorem finitePrimeTimeDistributionComplexWindow_eq_symmetrizedTime
    (N : ℕ) (g : ZetaAdmissibleFunction) :
    finitePrimeTimeDistributionComplexWindow N g =
      finitePrimeSymmetrizedComplexWindow N
        (fun a : ℝ => zetaCompletedTimeBoundaryValue g a) := by
  rfl

/-- The time-side complex window is the finite sum of time-side complex coordinates. -/
theorem finitePrimeTimeDistributionComplexWindow_eq_coordinateSum
    (N : ℕ) (g : ZetaAdmissibleFunction) :
    finitePrimeTimeDistributionComplexWindow N g =
      ∑ ι in ZetaPrimePowerIndex.window N,
        finitePrimeTimeDistributionComplexCoordinate ι g := by
  rfl

/-- The symmetrized time-boundary window is the finite sum of time-side complex
coordinates. -/
theorem finitePrimeSymmetrizedTimeWindow_eq_timeComplexCoordinateSum
    (N : ℕ) (g : ZetaAdmissibleFunction) :
    finitePrimeSymmetrizedComplexWindow N
        (fun a : ℝ => zetaCompletedTimeBoundaryValue g a) =
      ∑ ι in ZetaPrimePowerIndex.window N,
        finitePrimeTimeDistributionComplexCoordinate ι g := by
  exact
    (finitePrimeTimeDistributionComplexWindow_eq_symmetrizedTime N g).symm.trans
      (finitePrimeTimeDistributionComplexWindow_eq_coordinateSum N g)

/-- The finite time-side complex coordinate unfolds to the raw time-boundary expression. -/
theorem finitePrimeTimeDistributionComplexCoordinate_eq
    (ι : ZetaPrimePowerIndex) (g : ZetaAdmissibleFunction) :
    finitePrimeTimeDistributionComplexCoordinate ι g =
      -((ι.weight : ℂ) *
        (zetaCompletedTimeBoundaryValue g ι.center +
          star (zetaCompletedTimeBoundaryValue g ι.center))) := by
  rfl

/-- The real part of one finite time-side complex coordinate is the corresponding
time-side distribution coordinate. -/
theorem finitePrimeTimeDistributionComplexCoordinate_re_eq_timeCoordinate
    (ι : ZetaPrimePowerIndex) (g : ZetaAdmissibleFunction) :
    Complex.re (finitePrimeTimeDistributionComplexCoordinate ι g) =
      completedPrimeTimeDistributionCoordinate ι g := by
  exact complex_re_neg_ofReal_mul
    ι.weight
    (zetaCompletedTimeBoundaryValue g ι.center +
      star (zetaCompletedTimeBoundaryValue g ι.center))

/-- The real part of the finite complex time-side prime window is the finite time-side
coordinate sum. -/
theorem finitePrimeTimeDistributionComplexWindow_re_eq_coordinateSum
    (N : ℕ) (g : ZetaAdmissibleFunction) :
    Complex.re (finitePrimeTimeDistributionComplexWindow N g) =
      ∑ ι in ZetaPrimePowerIndex.window N,
        completedPrimeTimeDistributionCoordinate ι g := by
  exact
    (Complex.re_sum
      (ZetaPrimePowerIndex.window N)
      (fun ι : ZetaPrimePowerIndex =>
        finitePrimeTimeDistributionComplexCoordinate ι g)).trans
      (Finset.sum_congr
        rfl
        (fun ι _ =>
          finitePrimeTimeDistributionComplexCoordinate_re_eq_timeCoordinate
            ι g))

/-- The real part of the displayed finite time-side complex coordinate sum is the finite
sum of time-side real coordinates. -/
theorem finitePrimeTimeDistributionComplexCoordinateSum_re_eq_coordinateSum
    (N : ℕ) (g : ZetaAdmissibleFunction) :
    Complex.re
        (∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeTimeDistributionComplexCoordinate ι g) =
      ∑ ι in ZetaPrimePowerIndex.window N,
        completedPrimeTimeDistributionCoordinate ι g := by
  exact finitePrimeTimeDistributionComplexWindow_re_eq_coordinateSum N g

/-- The real part of the sampled horizontal difference is the difference of the real parts
of the sampled top and bottom edges. -/
theorem sampledHorizontalDifferenceComplex_re_eq_top_re_sub_bottom_re
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re (sampledHorizontalDifferenceComplex N f) =
      Complex.re (sampledHorizontalTopIntegral N f) -
        Complex.re (sampledHorizontalBottomIntegral N f) := by
  exact
    Eq.trans
      (congrArg Complex.re (sampledHorizontalDifferenceComplex_eq_top_sub_bottom N f))
      (Complex.sub_re (sampledHorizontalTopIntegral N f)
        (sampledHorizontalBottomIntegral N f))

/-- The real shadow of the sampled horizontal top-minus-bottom contour remainder along the
prime transport family. -/
noncomputable def sampledHorizontalDifference
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (sampledHorizontalDifferenceComplex N f)

/-- The sampled horizontal difference is the real part of the complex top-minus-bottom
horizontal contour difference. -/
theorem sampledHorizontalDifference_eq_complex_re
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    sampledHorizontalDifference N f =
      Complex.re (sampledHorizontalDifferenceComplex N f) := by
  rfl

/-- The sampled horizontal difference is the finite horizontal residue shadow. -/
theorem sampledHorizontalDifference_eq_finitePrimeHorizontalResidueShadow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    sampledHorizontalDifference N f =
      finitePrimeHorizontalResidueShadow N f := by
  calc
    sampledHorizontalDifference N f =
        Complex.re (sampledHorizontalDifferenceComplex N f) := by
      exact sampledHorizontalDifference_eq_complex_re N f
    _ =
        Complex.re
          (explicitFormulaFamilyHorizontalResidueWindowError
            (convolutionAutocorrelation f)
            completedPrimeContourTransportFamily
            (completedPrimeContourTransportHeightSchedule_owner.height (N : ℝ))) := by
      rfl
    _ = finitePrimeHorizontalResidueShadow N f := by
      exact (finitePrimeHorizontalResidueShadow_eq_horizontalResidueWindowError_re
        N f).symm


end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
