import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.OwnerParts.Part02

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open LSeries ArithmeticFunction
open scoped ArithmeticFunction
open scoped Topology
local notation "π" => Real.pi

namespace ZetaAdmissibleFunction

theorem completedPrimeContourRealizedTimeDistributionCoordinate_eq_timeDistributionCoordinate_of_complexCoordinate
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction)
    (hcoordinate :
      finitePrimeContourRealizedComplexCoordinate ι (convolutionAutocorrelation f) =
        finitePrimeTimeDistributionComplexCoordinate ι (convolutionAutocorrelation f)) :
    completedPrimeContourRealizedTimeDistributionCoordinate
        ι (convolutionAutocorrelation f) =
      completedPrimeTimeDistributionCoordinate
        ι (convolutionAutocorrelation f) := by
  calc
    completedPrimeContourRealizedTimeDistributionCoordinate
        ι (convolutionAutocorrelation f) =
        Complex.re
          (finitePrimeContourRealizedComplexCoordinate
            ι (convolutionAutocorrelation f)) := by
      exact
        (finitePrimeContourRealizedComplexCoordinate_re_eq_contourRealizedCoordinate
          ι (convolutionAutocorrelation f)).symm
    _ =
        Complex.re
          (finitePrimeTimeDistributionComplexCoordinate
            ι (convolutionAutocorrelation f)) := by
      exact congrArg Complex.re hcoordinate
    _ =
        completedPrimeTimeDistributionCoordinate
          ι (convolutionAutocorrelation f) := by
      exact finitePrimeTimeDistributionComplexCoordinate_re_eq_timeCoordinate
        ι (convolutionAutocorrelation f)

/-- A pointwise equality between the spectral contour sample and the time-boundary sample
identifies the corresponding symmetrized complex prime coordinates. -/
theorem completedPrimeContourRealizedComplexCoordinate_eq_timeComplexCoordinate_of_sample
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction)
    (hsample :
      zetaCompletedSpectralLaplaceTransform
          (convolutionAutocorrelation f) ι.center =
        zetaCompletedTimeBoundaryValue
          (convolutionAutocorrelation f) ι.center) :
    finitePrimeContourRealizedComplexCoordinate
        ι (convolutionAutocorrelation f) =
      finitePrimeTimeDistributionComplexCoordinate
        ι (convolutionAutocorrelation f) := by
  calc
    finitePrimeContourRealizedComplexCoordinate
        ι (convolutionAutocorrelation f) =
        -((ι.weight : ℂ) *
          (zetaCompletedSpectralLaplaceTransform
              (convolutionAutocorrelation f) ι.center +
            star
              (zetaCompletedSpectralLaplaceTransform
                (convolutionAutocorrelation f) ι.center))) := by
      exact finitePrimeContourRealizedComplexCoordinate_eq
        ι (convolutionAutocorrelation f)
    _ =
        -((ι.weight : ℂ) *
          (zetaCompletedTimeBoundaryValue
              (convolutionAutocorrelation f) ι.center +
            star
              (zetaCompletedTimeBoundaryValue
                (convolutionAutocorrelation f) ι.center))) := by
      exact congrArg
        (fun z : ℂ => -((ι.weight : ℂ) * (z + star z)))
        hsample
    _ =
        finitePrimeTimeDistributionComplexCoordinate
          ι (convolutionAutocorrelation f) := by
      exact
        (finitePrimeTimeDistributionComplexCoordinate_eq
          ι (convolutionAutocorrelation f)).symm

/-- A coordinatewise contour/time transport identity cancels the corresponding
contour-transport remainder coordinate. -/
theorem completedPrimeContourTransportCoordinateRemainderFamily_eq_zero_of_coordinate_transport
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction)
    (hcoordinate :
      completedPrimeContourRealizedTimeDistributionCoordinate
          ι (convolutionAutocorrelation f) =
        completedPrimeTimeDistributionCoordinate
          ι (convolutionAutocorrelation f)) :
    completedPrimeContourTransportCoordinateRemainderFamily f ι = 0 := by
  calc
    completedPrimeContourTransportCoordinateRemainderFamily f ι =
        completedPrimeContourTransportCoordinateRemainder ι f := by
      exact completedPrimeContourTransportCoordinateRemainderFamily_apply ι f
    _ =
        completedPrimeContourRealizedTimeDistributionCoordinate
            ι (convolutionAutocorrelation f) -
          completedPrimeTimeDistributionCoordinate
            ι (convolutionAutocorrelation f) := by
      exact completedPrimeContourTransportCoordinateRemainder_eq_contour_sub_time
        ι f
    _ =
        completedPrimeTimeDistributionCoordinate
            ι (convolutionAutocorrelation f) -
          completedPrimeTimeDistributionCoordinate
            ι (convolutionAutocorrelation f) := by
      exact congrArg
        (fun x : ℝ =>
          x -
            completedPrimeTimeDistributionCoordinate
              ι (convolutionAutocorrelation f))
        hcoordinate
    _ = 0 := by
      exact sub_self
        (completedPrimeTimeDistributionCoordinate
          ι (convolutionAutocorrelation f))

/-- A coordinatewise cancellation on the selected finite prime-power window cancels the
finite contour-transport coordinate-remainder window. -/
theorem finitePrimeContourTransportCoordinateRemainderWindow_eq_zero_of_coordinatewise
    (N : ℕ) (f : ZetaAdmissibleFunction)
    (hcoordinate :
      ∀ ι : ZetaPrimePowerIndex,
        ι ∈ ZetaPrimePowerIndex.window N →
          completedPrimeContourTransportCoordinateRemainderFamily f ι = 0) :
    finitePrimeContourTransportCoordinateRemainderWindow N f = 0 := by
  calc
    finitePrimeContourTransportCoordinateRemainderWindow N f =
        ∑ ι in ZetaPrimePowerIndex.window N,
          completedPrimeContourTransportCoordinateRemainderFamily f ι := by
      exact finitePrimeContourTransportCoordinateRemainderWindow_eq_windowSum N f
    _ = 0 := by
      exact Finset.sum_eq_zero hcoordinate

/-- A finite time/log window equality cancels the finite contour-transport remainder
window by the owner remainder accounting identity. -/
theorem finitePrimeContourTransportCoordinateRemainderWindow_eq_zero_of_window_eq
    (N : ℕ) (f : ZetaAdmissibleFunction)
    (hwindow :
      finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) =
        finitePrimeContourRealizedTimeDistributionWindow N
          (convolutionAutocorrelation f)) :
    finitePrimeContourTransportCoordinateRemainderWindow N f = 0 := by
  let T : ℝ := finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f)
  let C : ℝ :=
    finitePrimeContourRealizedTimeDistributionWindow N
      (convolutionAutocorrelation f)
  let R : ℝ := finitePrimeContourTransportCoordinateRemainderWindow N f
  have hsum : T + R = C := by
    unfold T
    unfold C
    unfold R
    exact finitePrimeTimeDistributionWindow_add_coordinateRemainderWindow N f
  have hC_eq_T : C = T := by
    unfold T
    unfold C
    exact hwindow.symm
  have hsum_eq_T : T + R = T := hsum.trans hC_eq_T
  have hleft :
    -T + (T + R) = R := by
    calc
      -T + (T + R) = (-T + T) + R := by
        exact (add_assoc (-T) T R).symm
      _ = 0 + R := by
        exact congrArg (fun x : ℝ => x + R) (neg_add_cancel T)
      _ = R := by
        exact zero_add R
  have hright :
      -T + T = 0 := by
    exact neg_add_cancel T
  have htransport :
      -T + (T + R) = -T + T := by
    exact congrArg (fun x : ℝ => -T + x) hsum_eq_T
  calc
    R = -T + (T + R) := by
      exact hleft.symm
    _ = -T + T := by
      exact htransport
    _ = 0 := by
      exact hright

/-- The finite contour-realized prime window of an autocorrelation is the finite spectral
prime off-diagonal window. -/
theorem finitePrimeContourRealizedTimeDistributionWindow_convolutionAutocorrelation_eq_spectral
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeContourRealizedTimeDistributionWindow N
        (convolutionAutocorrelation f) =
      finiteSpectralPrimeOffDiagonalWindow N f := by
  unfold finitePrimeContourRealizedTimeDistributionWindow
  unfold finiteSpectralPrimeOffDiagonalWindow
  exact congrArg Complex.re
    (Finset.sum_congr rfl
      (fun ι _hι =>
        congrArg
          (fun z : ℂ => -((ι.weight : ℂ) * (z + star z)))
            ((congrFun
              (zetaCompletedExplicitFormulaPhi_eq_spectralLaplaceTransform
                (convolutionAutocorrelation f))
              ι.center).symm)))

/-- The spectral off-diagonal coordinate is the contour-realized coordinate after the
completed spectral transform is identified with the explicit-formula transform. -/
theorem zetaSpectralPrimeOffDiagonalCoordinate_eq_contourRealizedCoordinate
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    zetaSpectralPrimeOffDiagonalCoordinate ι f =
      completedPrimeContourRealizedTimeDistributionCoordinate
        ι (convolutionAutocorrelation f) := by
  have hΦ :
      zetaCompletedExplicitFormulaPhi
          (convolutionAutocorrelation f) ι.center =
        zetaCompletedSpectralLaplaceTransform
          (convolutionAutocorrelation f) ι.center := by
    exact
      congrFun
        (zetaCompletedExplicitFormulaPhi_eq_spectralLaplaceTransform
          (convolutionAutocorrelation f))
        ι.center
  calc
    zetaSpectralPrimeOffDiagonalCoordinate ι f =
        Complex.re
          (-((ι.weight : ℂ) *
            (zetaCompletedExplicitFormulaPhi
                (convolutionAutocorrelation f) ι.center +
              star
                (zetaCompletedExplicitFormulaPhi
                  (convolutionAutocorrelation f) ι.center)))) := by
      rfl
    _ =
        Complex.re
          (-((ι.weight : ℂ) *
            (zetaCompletedSpectralLaplaceTransform
                (convolutionAutocorrelation f) ι.center +
              star
                (zetaCompletedSpectralLaplaceTransform
                  (convolutionAutocorrelation f) ι.center)))) := by
      exact congrArg
        (fun z : ℂ =>
          Complex.re (-((ι.weight : ℂ) * (z + star z))))
        hΦ
    _ =
        completedPrimeContourRealizedTimeDistributionCoordinate
          ι (convolutionAutocorrelation f) := by
      rfl

/-- The autocorrelation time-side prime coordinate unfolds to the signed real
symmetrized logarithmic-boundary coefficient. -/
theorem completedPrimeAutocorrelationTimeCoordinate_eq_weightedTimeBoundarySample
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    completedPrimeTimeDistributionCoordinate
        ι (convolutionAutocorrelation f) =
      -(ι.weight *
        Complex.re
          (zetaCompletedTimeBoundaryValue
              (convolutionAutocorrelation f) ι.center +
            star
              (zetaCompletedTimeBoundaryValue
                (convolutionAutocorrelation f) ι.center))) := by
  rfl

/-- The contour-realized prime coordinate unfolds to the real part of the signed spectral
sample coefficient. -/
theorem completedPrimeContourRealizedCoordinate_eq_weightedSpectralSample
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    completedPrimeContourRealizedTimeDistributionCoordinate
        ι (convolutionAutocorrelation f) =
      Complex.re
        (-((ι.weight : ℂ) *
          (zetaCompletedSpectralLaplaceTransform
              (convolutionAutocorrelation f) ι.center +
            star
              (zetaCompletedSpectralLaplaceTransform
                (convolutionAutocorrelation f) ι.center)))) := by
  rfl

/-- The real part of the owner Hermitian symmetrization is twice the real part of the
sample. -/
theorem complex_re_add_star_eq_two_re
    (z : ℂ) :
    Complex.re (z + star z) = 2 * Complex.re z := by
  have hadd :
      Complex.re (z + star z) = Complex.re z + Complex.re (star z) := by
    exact Complex.add_re z (star z)
  have hstar :
      Complex.re (star z) = Complex.re z := by
    rfl
  calc
    Complex.re (z + star z) =
        Complex.re z + Complex.re (star z) := hadd
    _ = Complex.re z + Complex.re z := by
      exact congrArg (fun x : ℝ => Complex.re z + x) hstar
    _ = 2 * Complex.re z := by
      exact (two_mul (Complex.re z)).symm

/-- The time-side symmetrized autocorrelation sample is twice the real translated
autocorrelation inner product. -/
theorem completedPrimeAutocorrelationSymmetrizedTimeSample_re_eq_two_translateInner
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    Complex.re
        (zetaCompletedTimeBoundaryValue
            (convolutionAutocorrelation f) ι.center +
          star
            (zetaCompletedTimeBoundaryValue
              (convolutionAutocorrelation f) ι.center)) =
      2 * Complex.re (zetaSeedInner (zetaTranslate ι.center f) f) := by
  have htime :
      zetaCompletedTimeBoundaryValue
          (convolutionAutocorrelation f) ι.center =
        convolutionAutocorrelationKernel f ι.center :=
    zetaCompletedTimeBoundaryValue_convolutionAutocorrelation_eq_kernel f ι.center
  have hsum :
      zetaCompletedTimeBoundaryValue
          (convolutionAutocorrelation f) ι.center +
        star
          (zetaCompletedTimeBoundaryValue
            (convolutionAutocorrelation f) ι.center) =
        convolutionAutocorrelationKernel f ι.center +
          star (convolutionAutocorrelationKernel f ι.center) := by
    exact congrArg₂ HAdd.hAdd htime (congrArg star htime)
  have hneg :
      convolutionAutocorrelationKernel f (-ι.center) =
        star (convolutionAutocorrelationKernel f ι.center) :=
    convolutionAutocorrelationKernel_neg_eq_conj f ι.center
  calc
    Complex.re
        (zetaCompletedTimeBoundaryValue
            (convolutionAutocorrelation f) ι.center +
          star
            (zetaCompletedTimeBoundaryValue
              (convolutionAutocorrelation f) ι.center)) =
        Complex.re
          (convolutionAutocorrelationKernel f ι.center +
            star (convolutionAutocorrelationKernel f ι.center)) := by
      exact congrArg Complex.re hsum
    _ =
        Complex.re
          (convolutionAutocorrelationKernel f ι.center +
            convolutionAutocorrelationKernel f (-ι.center)) := by
      exact congrArg
        (fun z : ℂ =>
          Complex.re (convolutionAutocorrelationKernel f ι.center + z))
        hneg.symm
    _ = 2 * Complex.re (zetaSeedInner (zetaTranslate ι.center f) f) := by
      exact convolutionAutocorrelationKernel_add_neg_eq_two_re_translateInner
        f ι.center

/-- The natural two-face boundary sample of a convolution-autocorrelation probe
reduces to the Hermitian time-boundary sum at the positive natural center.

This is the acyclic bridge from the Hilbert/autocorrelation symmetry theorem
to the vertical-channel natural-prime arithmetic owner.  It still does not
identify this two-face presentation with the vertical-channel `TimeSummand`;
that remaining comparison owns the explicit-formula constants. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample_convolutionAutocorrelation_of_ne_zero
    (seed : ZetaAdmissibleFunction) {n : ℕ} (hn : n ≠ 0) :
    zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample
        (convolutionAutocorrelation seed) n =
      ((Λ n / Real.sqrt n : ℝ) : ℂ) *
        ((2 * π : ℝ) •
          (zetaCompletedTimeBoundaryValue
              (convolutionAutocorrelation seed)
              (zetaCompletedExplicitFormulaPrimeNaturalCenter n) +
            star
              (zetaCompletedTimeBoundaryValue
                (convolutionAutocorrelation seed)
                (zetaCompletedExplicitFormulaPrimeNaturalCenter n)))) := by
  let a : ℝ := zetaCompletedExplicitFormulaPrimeNaturalCenter n
  have hpos :
      zetaCompletedTimeBoundaryValue (convolutionAutocorrelation seed) a =
        convolutionAutocorrelationKernel seed a :=
    zetaCompletedTimeBoundaryValue_convolutionAutocorrelation_eq_kernel seed a
  have hneg_time :
      zetaCompletedTimeBoundaryValue (convolutionAutocorrelation seed) (-a) =
        convolutionAutocorrelationKernel seed (-a) :=
    zetaCompletedTimeBoundaryValue_convolutionAutocorrelation_eq_kernel seed (-a)
  have hneg_kernel :
      convolutionAutocorrelationKernel seed (-a) =
        star (convolutionAutocorrelationKernel seed a) :=
    convolutionAutocorrelationKernel_neg_eq_conj seed a
  have hreflect :
      zetaCompletedTimeBoundaryValue
          (convolutionAutocorrelation seed)
          (-(zetaCompletedExplicitFormulaPrimeNaturalCenter n)) =
        star
          (zetaCompletedTimeBoundaryValue
            (convolutionAutocorrelation seed)
            (zetaCompletedExplicitFormulaPrimeNaturalCenter n)) := by
    calc
      zetaCompletedTimeBoundaryValue
          (convolutionAutocorrelation seed)
          (-(zetaCompletedExplicitFormulaPrimeNaturalCenter n)) =
          zetaCompletedTimeBoundaryValue
            (convolutionAutocorrelation seed) (-a) := by
        rfl
      _ = convolutionAutocorrelationKernel seed (-a) := hneg_time
      _ = star (convolutionAutocorrelationKernel seed a) := hneg_kernel
      _ =
          star
            (zetaCompletedTimeBoundaryValue
              (convolutionAutocorrelation seed)
              (zetaCompletedExplicitFormulaPrimeNaturalCenter n)) := by
        exact congrArg star hpos.symm
  exact
    zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample_of_ne_zero_of_reflectionDagger
      (convolutionAutocorrelation seed) hn hreflect

/-- The spectral symmetrized autocorrelation sample is twice the real part of the paired
seed spectral sample. -/
theorem completedPrimeAutocorrelationSymmetrizedSpectralSample_re_eq_two_pairedSample
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    Complex.re
        (zetaCompletedSpectralLaplaceTransform
            (convolutionAutocorrelation f) ι.center +
          star
            (zetaCompletedSpectralLaplaceTransform
              (convolutionAutocorrelation f) ι.center)) =
      2 *
        Complex.re
          (zetaCompletedSpectralLaplaceTransform f ι.center *
            star
              (zetaCompletedSpectralLaplaceTransform f (-(ι.center : ℂ)))) := by
  let P : ℂ :=
    zetaCompletedSpectralLaplaceTransform f ι.center *
      star (zetaCompletedSpectralLaplaceTransform f (-(ι.center : ℂ)))
  have hfactor :
      zetaCompletedSpectralLaplaceTransform
          (convolutionAutocorrelation f) ι.center = P := by
    unfold P
    calc
      zetaCompletedSpectralLaplaceTransform
          (convolutionAutocorrelation f) ι.center =
          zetaCompletedExplicitFormulaPhi
            (convolutionAutocorrelation f) ι.center := by
        exact
          (congrFun
            (zetaCompletedExplicitFormulaPhi_eq_spectralLaplaceTransform
              (convolutionAutocorrelation f))
            ι.center).symm
      _ =
          zetaCompletedExplicitFormulaPhi f ι.center *
            star
              (zetaCompletedExplicitFormulaPhi f (-(ι.center : ℂ))) := by
        exact zetaCompletedExplicitFormulaPhi_convolutionAutocorrelation_real_pair
          f ι.center
      _ =
          zetaCompletedSpectralLaplaceTransform f ι.center *
            star
              (zetaCompletedExplicitFormulaPhi f (-(ι.center : ℂ))) := by
        exact congrArg
          (fun z : ℂ =>
            z *
              star
                (zetaCompletedExplicitFormulaPhi f (-(ι.center : ℂ))))
          (congrFun
            (zetaCompletedExplicitFormulaPhi_eq_spectralLaplaceTransform f)
            ι.center)
      _ =
          zetaCompletedSpectralLaplaceTransform f ι.center *
            star
              (zetaCompletedSpectralLaplaceTransform f (-(ι.center : ℂ))) := by
        exact congrArg
          (fun z : ℂ =>
            zetaCompletedSpectralLaplaceTransform f ι.center * star z)
          (congrFun
            (zetaCompletedExplicitFormulaPhi_eq_spectralLaplaceTransform f)
            (-(ι.center : ℂ)))
  calc
    Complex.re
        (zetaCompletedSpectralLaplaceTransform
            (convolutionAutocorrelation f) ι.center +
          star
            (zetaCompletedSpectralLaplaceTransform
              (convolutionAutocorrelation f) ι.center)) =
        Complex.re (P + star P) := by
      exact congrArg Complex.re
        (congrArg₂ HAdd.hAdd hfactor (congrArg star hfactor))
    _ = 2 * Complex.re P := by
      exact complex_re_add_star_eq_two_re P
    _ =
        2 *
          Complex.re
            (zetaCompletedSpectralLaplaceTransform f ι.center *
            star
              (zetaCompletedSpectralLaplaceTransform f (-(ι.center : ℂ)))) := by
      rfl

/-- The translated seed inner product is the uncentered autocorrelation kernel. -/
theorem completedPrimeAutocorrelationTranslateInner_re_eq_kernel_re
    (a : ℝ) (f : ZetaAdmissibleFunction) :
    Complex.re (zetaSeedInner (zetaTranslate a f) f) =
      Complex.re (convolutionAutocorrelationKernel f a) := by
  have hkernel :
      convolutionAutocorrelationKernel f a =
        zetaSeedInner (zetaTranslate a f) f :=
    convolutionAutocorrelationKernel_eq_translateInner f a
  exact congrArg Complex.re hkernel.symm

/-- The paired `Φ` sample is the `Φ` sample of the autocorrelation probe. -/
theorem completedPrimePairedPhiSample_re_eq_autocorrelationPhi_re
    (a : ℝ) (f : ZetaAdmissibleFunction) :
    Complex.re
        (zetaCompletedExplicitFormulaPhi f (a : ℂ) *
          star
            (zetaCompletedExplicitFormulaPhi f (-(a : ℂ)))) =
      Complex.re
        (zetaCompletedExplicitFormulaPhi (convolutionAutocorrelation f) (a : ℂ)) := by
  have hphi :
      zetaCompletedExplicitFormulaPhi
          (convolutionAutocorrelation f) (a : ℂ) =
        zetaCompletedExplicitFormulaPhi f (a : ℂ) *
          star
            (zetaCompletedExplicitFormulaPhi f (-(a : ℂ))) :=
    zetaCompletedExplicitFormulaPhi_convolutionAutocorrelation_real_pair f a
  exact congrArg Complex.re hphi.symm

/-- The autocorrelation kernel is the time-boundary value of the convolution autocorrelation
probe, transported to real parts. -/
theorem completedPrimeAutocorrelationKernel_re_eq_timeBoundaryValue_re
    (a : ℝ) (f : ZetaAdmissibleFunction) :
    Complex.re (convolutionAutocorrelationKernel f a) =
      Complex.re
        (zetaCompletedTimeBoundaryValue (convolutionAutocorrelation f) a) := by
  have htime :
    zetaCompletedTimeBoundaryValue (convolutionAutocorrelation f) a =
        convolutionAutocorrelationKernel f a :=
    zetaCompletedTimeBoundaryValue_convolutionAutocorrelation_eq_kernel f a
  exact congrArg Complex.re htime.symm

/-!
The former HS:1903 pointwise Plancherel chain has been removed from this owner surface.
It asserted a false pointwise identification between the time-side autocorrelation kernel and
real-axis Laplace samples.  The finite physical and contour-realized prime windows are not
identified directly; the honest finite relation keeps the contour-transport remainder visible.
-/

/-- Finite prime transport is the additive remainder accounting identity between the time/log
window and the contour-realized spectral window. -/
theorem finitePrimeTimeDistributionWindow_add_coordinateRemainderWindow_ownerPrimeTransport
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) +
        finitePrimeContourTransportCoordinateRemainderWindow N f =
      finitePrimeContourRealizedTimeDistributionWindow N
        (convolutionAutocorrelation f) := by
  exact finitePrimeTimeDistributionWindow_add_coordinateRemainderWindow N f

/-- The selected finite coordinate-remainder window remains as the exact additive difference
between the time/log and contour-realized prime windows. -/
theorem finitePrimeContourTransportCoordinateRemainderWindow_ownerTransport
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) +
        finitePrimeContourTransportCoordinateRemainderWindow N f =
      finitePrimeContourRealizedTimeDistributionWindow N
        (convolutionAutocorrelation f) := by
  exact
    finitePrimeTimeDistributionWindow_add_coordinateRemainderWindow_ownerPrimeTransport
      N f

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
