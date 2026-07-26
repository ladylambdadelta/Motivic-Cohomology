import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.OwnerParts.Part01

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open LSeries ArithmeticFunction
open scoped ArithmeticFunction
open scoped Topology
local notation "π" => Real.pi

namespace ZetaAdmissibleFunction

/-- The scalar induced by the reduced time-side Hilbert pairing.  This is retained as a
comparison scalar; the completed ordered-heart scalar is owned by the positive GNS kernel. -/
def completedBoundaryTimePairingScalar
    (X : CompletedBoundaryHilbertSource) : ℝ :=
  completedBoundaryHilbertPairing X X

/-- The prime boundary channel vanishes on the zero admissible probe. -/
theorem primeBoundaryChannel_zero :
    primeBoundaryChannel (0 : ZetaAdmissibleFunction) = 0 := by
  unfold primeBoundaryChannel
  unfold zetaCompletedExplicitFormulaPrimeContribution
  unfold zetaCompletedExplicitFormulaPrimePowerContribution
  let term : ZetaPrimePowerIndex → ℂ :=
    fun ι : ZetaPrimePowerIndex =>
      -(((ZetaPrimePowerIndex.weight ι : ℝ) : ℂ) *
        ((Complex.re
            (zetaCompletedTimeBoundaryValue (0 : ZetaAdmissibleFunction)
                (ZetaPrimePowerIndex.center ι) +
              star
                (zetaCompletedTimeBoundaryValue (0 : ZetaAdmissibleFunction)
                  (ZetaPrimePowerIndex.center ι))) : ℝ) : ℂ))
  have hterm : term = fun _ι : ZetaPrimePowerIndex => 0 := by
    ext ι
    show term ι = 0
    unfold term
    have hpos :
        zetaCompletedTimeBoundaryValue (0 : ZetaAdmissibleFunction)
            (ZetaPrimePowerIndex.center ι) =
          0 :=
      zetaCompletedTimeBoundaryValue_zero (ZetaPrimePowerIndex.center ι)
    have hstar :
        star
            (zetaCompletedTimeBoundaryValue (0 : ZetaAdmissibleFunction)
              (ZetaPrimePowerIndex.center ι)) =
          0 := by
      exact (congrArg star hpos).trans (star_zero ℂ)
    have hsum :
        zetaCompletedTimeBoundaryValue (0 : ZetaAdmissibleFunction)
            (ZetaPrimePowerIndex.center ι) +
          star
            (zetaCompletedTimeBoundaryValue (0 : ZetaAdmissibleFunction)
              (ZetaPrimePowerIndex.center ι)) =
        0 := by
      calc
        zetaCompletedTimeBoundaryValue (0 : ZetaAdmissibleFunction)
            (ZetaPrimePowerIndex.center ι) +
          star
            (zetaCompletedTimeBoundaryValue (0 : ZetaAdmissibleFunction)
              (ZetaPrimePowerIndex.center ι)) =
            0 + 0 := by
          exact congrArg₂ HAdd.hAdd hpos hstar
        _ = 0 := by
          exact zero_add 0
    have hre :
        Complex.re
          (zetaCompletedTimeBoundaryValue (0 : ZetaAdmissibleFunction)
              (ZetaPrimePowerIndex.center ι) +
            star
              (zetaCompletedTimeBoundaryValue (0 : ZetaAdmissibleFunction)
                (ZetaPrimePowerIndex.center ι))) =
          0 := by
      exact (congrArg Complex.re hsum).trans Complex.zero_re
    calc
      -(((ZetaPrimePowerIndex.weight ι : ℝ) : ℂ) *
          ((Complex.re
              (zetaCompletedTimeBoundaryValue (0 : ZetaAdmissibleFunction)
                  (ZetaPrimePowerIndex.center ι) +
                star
                  (zetaCompletedTimeBoundaryValue (0 : ZetaAdmissibleFunction)
                    (ZetaPrimePowerIndex.center ι))) : ℝ) : ℂ)) =
          -(((ZetaPrimePowerIndex.weight ι : ℝ) : ℂ) * ((0 : ℝ) : ℂ)) := by
        exact congrArg
          (fun x : ℝ =>
            -(((ZetaPrimePowerIndex.weight ι : ℝ) : ℂ) * ((x : ℝ) : ℂ)))
          hre
      _ = -0 := by
        exact congrArg Neg.neg
          (mul_zero (((ZetaPrimePowerIndex.weight ι : ℝ) : ℂ)))
      _ = 0 := by
        exact neg_zero
  have htsum :
      (∑' ι : ZetaPrimePowerIndex, term ι) = 0 := by
    have hzeroTsum :
        (∑' ι : ZetaPrimePowerIndex, term ι) =
          (∑' _ι : ZetaPrimePowerIndex, (0 : ℂ)) := by
      exact congrArg
        (fun u : ZetaPrimePowerIndex → ℂ =>
          (∑' ι : ZetaPrimePowerIndex, u ι))
        hterm
    exact Eq.trans hzeroTsum tsum_zero
  change -(∑' ι : ZetaPrimePowerIndex, term ι) = 0
  have hneg :
      -(∑' ι : ZetaPrimePowerIndex, term ι) = -0 := by
    exact congrArg Neg.neg htsum
  exact Eq.trans hneg neg_zero

/-- The archimedean boundary channel vanishes on the zero admissible probe. -/
theorem archimedeanBoundaryChannel_zero :
    archimedeanBoundaryChannel (0 : ZetaAdmissibleFunction) = 0 := by
  unfold archimedeanBoundaryChannel
  unfold zetaCompletedExplicitFormulaArchimedeanContribution
  unfold zetaCompletedExplicitFormulaHermitianArchimedeanContribution
  have hintegrand :
      (fun t : ℝ =>
        zetaCompletedArchimedeanHermitianIntegrand
          (0 : ZetaAdmissibleFunction) t) =
        fun _t : ℝ => (0 : ℂ) := by
    funext t
    unfold zetaCompletedArchimedeanHermitianIntegrand
    have hphi :
        zetaCompletedExplicitFormulaPhi
            (0 : ZetaAdmissibleFunction) (t * Complex.I) = 0 :=
      zetaCompletedExplicitFormulaPhi_zero (t * Complex.I)
    exact Eq.trans
      (congrArg
        (fun z : ℂ => zetaCompletedArchimedeanHermitianKernel t * z)
        hphi)
      (mul_zero (zetaCompletedArchimedeanHermitianKernel t))
  have hintegral :
      (∫ t : ℝ,
        zetaCompletedArchimedeanHermitianIntegrand
          (0 : ZetaAdmissibleFunction) t) =
        ∫ _t : ℝ, (0 : ℂ) := by
    exact MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall
        (fun t : ℝ => congrFun hintegrand t))
  exact Eq.trans hintegral (MeasureTheory.integral_zero ℝ ℂ)

/-- The residual completion boundary channel vanishes on the zero admissible probe. -/
theorem completionBoundaryChannel_zero :
    completionBoundaryChannel (0 : ZetaAdmissibleFunction) = 0 := by
  rfl

/-- The reduced completed boundary channel vanishes on the zero admissible probe. -/
theorem completedBoundaryReducedChannel_zero :
    completedBoundaryReducedChannel (0 : ZetaAdmissibleFunction) = 0 := by
  unfold completedBoundaryReducedChannel
  calc
    primeBoundaryChannel (0 : ZetaAdmissibleFunction) +
        archimedeanBoundaryChannel (0 : ZetaAdmissibleFunction) +
        completionBoundaryChannel (0 : ZetaAdmissibleFunction) =
      0 + 0 + 0 := by
      exact congrArg₂ HAdd.hAdd
        (congrArg₂ HAdd.hAdd primeBoundaryChannel_zero archimedeanBoundaryChannel_zero)
        completionBoundaryChannel_zero
    _ = 0 + 0 := by
      exact add_zero (0 + 0)
    _ = 0 := by
      exact zero_add 0

/-- The reduced completed boundary channel of the zero convolution pair is zero. -/
theorem completedBoundaryReducedChannel_convolutionPair_zero_zero :
    completedBoundaryReducedChannel
        (convolutionPair (0 : ZetaAdmissibleFunction) 0) =
      0 := by
  exact (congrArg completedBoundaryReducedChannel convolutionPair_zero_zero).trans
    completedBoundaryReducedChannel_zero

/-- The reduced completed boundary channel of a convolution pair with zero left input is
zero. -/
theorem completedBoundaryReducedChannel_convolutionPair_zero_left
    (h : ZetaAdmissibleFunction) :
    completedBoundaryReducedChannel
        (convolutionPair (0 : ZetaAdmissibleFunction) h) =
      0 := by
  exact (congrArg completedBoundaryReducedChannel (convolutionPair_zero_left h)).trans
    completedBoundaryReducedChannel_zero

/-- The reduced completed boundary channel of a convolution pair with zero right input is
zero. -/
theorem completedBoundaryReducedChannel_convolutionPair_zero_right
    (f : ZetaAdmissibleFunction) :
    completedBoundaryReducedChannel
        (convolutionPair f (0 : ZetaAdmissibleFunction)) =
      0 := by
  exact (congrArg completedBoundaryReducedChannel (convolutionPair_zero_right f)).trans
    completedBoundaryReducedChannel_zero

/-- The zero Hilbert source has zero self-pairing. -/
theorem completedBoundaryHilbertPairing_zero_zero :
    completedBoundaryHilbertPairing
        (0 : CompletedBoundaryHilbertSource)
        (0 : CompletedBoundaryHilbertSource) =
      0 := by
  unfold completedBoundaryHilbertPairing
  change
    Complex.re
        (completedBoundaryReducedChannel
          (convolutionPair (0 : ZetaAdmissibleFunction) 0)) +
      0 * 0 =
    0
  calc
    Complex.re
        (completedBoundaryReducedChannel
          (convolutionPair (0 : ZetaAdmissibleFunction) 0)) +
      0 * 0 =
        Complex.re 0 + 0 * 0 := by
      exact congrArg
        (fun z : ℂ => Complex.re z + 0 * 0)
        completedBoundaryReducedChannel_convolutionPair_zero_zero
    _ = 0 + 0 * 0 := by
      exact congrArg (fun x : ℝ => x + 0 * 0) Complex.zero_re
    _ = 0 + 0 := by
      exact congrArg (fun x : ℝ => 0 + x) (zero_mul 0)
    _ = 0 := by
      exact zero_add 0

/-- The zero Hilbert source pairs trivially on the left. -/
theorem completedBoundaryHilbertPairing_zero_left
    (Y : CompletedBoundaryHilbertSource) :
    completedBoundaryHilbertPairing
        (0 : CompletedBoundaryHilbertSource)
        Y =
      0 := by
  unfold completedBoundaryHilbertPairing
  change
    Complex.re
        (completedBoundaryReducedChannel
          (convolutionPair (0 : ZetaAdmissibleFunction) Y.seed)) +
      0 * Y.correctionCoordinate =
    0
  calc
    Complex.re
        (completedBoundaryReducedChannel
          (convolutionPair (0 : ZetaAdmissibleFunction) Y.seed)) +
      0 * Y.correctionCoordinate =
        Complex.re 0 + 0 * Y.correctionCoordinate := by
      exact congrArg
        (fun z : ℂ => Complex.re z + 0 * Y.correctionCoordinate)
        (completedBoundaryReducedChannel_convolutionPair_zero_left Y.seed)
    _ = 0 + 0 * Y.correctionCoordinate := by
      exact congrArg (fun x : ℝ => x + 0 * Y.correctionCoordinate) Complex.zero_re
    _ = 0 + 0 := by
      exact congrArg (fun x : ℝ => 0 + x) (zero_mul Y.correctionCoordinate)
    _ = 0 := by
      exact zero_add 0

/-- The zero Hilbert source pairs trivially on the right. -/
theorem completedBoundaryHilbertPairing_zero_right
    (X : CompletedBoundaryHilbertSource) :
    completedBoundaryHilbertPairing
        X
        (0 : CompletedBoundaryHilbertSource) =
      0 := by
  unfold completedBoundaryHilbertPairing
  change
    Complex.re
        (completedBoundaryReducedChannel
          (convolutionPair X.seed (0 : ZetaAdmissibleFunction))) +
      X.correctionCoordinate * 0 =
    0
  calc
    Complex.re
        (completedBoundaryReducedChannel
          (convolutionPair X.seed (0 : ZetaAdmissibleFunction))) +
      X.correctionCoordinate * 0 =
        Complex.re 0 + X.correctionCoordinate * 0 := by
      exact congrArg
        (fun z : ℂ => Complex.re z + X.correctionCoordinate * 0)
        (completedBoundaryReducedChannel_convolutionPair_zero_right X.seed)
    _ = 0 + X.correctionCoordinate * 0 := by
      exact congrArg (fun x : ℝ => x + X.correctionCoordinate * 0) Complex.zero_re
    _ = 0 + 0 := by
      exact congrArg (fun x : ℝ => 0 + x) (mul_zero X.correctionCoordinate)
    _ = 0 := by
      exact zero_add 0

/-- The zero Hilbert source is lower-weight radical. -/
theorem completedBoundaryHilbertSource_zero_lowerWeightRadical :
    CompletedBoundaryHilbertSource.LowerWeightRadical
      (0 : CompletedBoundaryHilbertSource) := by
  intro T
  exact
    ⟨completedBoundaryHilbertPairing_zero_left T,
      completedBoundaryHilbertPairing_zero_right T⟩

/-- Adding a lower-weight radical Hilbert source does not change the reduced time-pairing
scalar, provided the completed Hilbert pairing is additive in both variables. -/
theorem completedBoundaryTimePairingScalar_eq_of_add_lowerWeightRadical
    (B_add_left :
      ∀ x y z : CompletedBoundaryHilbertSource,
        completedBoundaryHilbertPairing (x + y) z =
          completedBoundaryHilbertPairing x z +
            completedBoundaryHilbertPairing y z)
    (B_add_right :
      ∀ x y z : CompletedBoundaryHilbertSource,
        completedBoundaryHilbertPairing x (y + z) =
          completedBoundaryHilbertPairing x y +
            completedBoundaryHilbertPairing x z)
    (Y D : CompletedBoundaryHilbertSource)
    (hD : CompletedBoundaryHilbertSource.LowerWeightRadical D) :
    completedBoundaryTimePairingScalar (Y + D) =
      completedBoundaryTimePairingScalar Y := by
  have hDYD :
      completedBoundaryHilbertPairing D (Y + D) = 0 :=
    (hD (Y + D)).1
  have hYD :
      completedBoundaryHilbertPairing Y D = 0 :=
    (hD Y).2
  unfold completedBoundaryTimePairingScalar
  calc
    completedBoundaryHilbertPairing (Y + D) (Y + D) =
        completedBoundaryHilbertPairing Y (Y + D) +
          completedBoundaryHilbertPairing D (Y + D) := by
      exact B_add_left Y D (Y + D)
    _ =
        completedBoundaryHilbertPairing Y (Y + D) + 0 := by
      exact congrArg
        (fun x : ℝ => completedBoundaryHilbertPairing Y (Y + D) + x)
        hDYD
    _ =
        completedBoundaryHilbertPairing Y (Y + D) := by
      exact add_zero (completedBoundaryHilbertPairing Y (Y + D))
    _ =
        completedBoundaryHilbertPairing Y Y +
          completedBoundaryHilbertPairing Y D := by
      exact B_add_right Y Y D
    _ =
        completedBoundaryHilbertPairing Y Y + 0 := by
      exact congrArg
        (fun x : ℝ => completedBoundaryHilbertPairing Y Y + x)
        hYD
    _ =
        completedBoundaryHilbertPairing Y Y := by
      exact add_zero (completedBoundaryHilbertPairing Y Y)

/-- The additive decomposition `X = Y + (X - Y)` for Hilbert sources. -/
theorem completedBoundaryHilbertSource_eq_add_sub
    (X Y : CompletedBoundaryHilbertSource) :
    X = Y + (X - Y) := by
  apply CompletedBoundaryHilbertSource.ext
  · change X.seed = Y.seed + (X.seed + -Y.seed)
    exact
      (calc
        Y.seed + (X.seed + -Y.seed) =
            (Y.seed + X.seed) + -Y.seed := by
          exact (add_assoc Y.seed X.seed (-Y.seed)).symm
        _ = (X.seed + Y.seed) + -Y.seed := by
          exact congrArg (fun Z : ZetaAdmissibleFunction => Z + -Y.seed)
            (add_comm Y.seed X.seed)
        _ = X.seed + (Y.seed + -Y.seed) := by
          exact add_assoc X.seed Y.seed (-Y.seed)
        _ = X.seed + 0 := by
          exact congrArg (fun Z : ZetaAdmissibleFunction => X.seed + Z)
            (add_right_neg Y.seed)
        _ = X.seed := by
          exact add_zero X.seed).symm
  · change X.correctionCoordinate =
      Y.correctionCoordinate + (X.correctionCoordinate + -Y.correctionCoordinate)
    exact
      (calc
        Y.correctionCoordinate +
            (X.correctionCoordinate + -Y.correctionCoordinate) =
            (Y.correctionCoordinate + X.correctionCoordinate) +
              -Y.correctionCoordinate := by
          exact
            (add_assoc Y.correctionCoordinate X.correctionCoordinate
              (-Y.correctionCoordinate)).symm
        _ = (X.correctionCoordinate + Y.correctionCoordinate) +
              -Y.correctionCoordinate := by
          exact congrArg (fun Z : ℝ => Z + -Y.correctionCoordinate)
            (add_comm Y.correctionCoordinate X.correctionCoordinate)
        _ = X.correctionCoordinate +
              (Y.correctionCoordinate + -Y.correctionCoordinate) := by
          exact
            add_assoc X.correctionCoordinate Y.correctionCoordinate
              (-Y.correctionCoordinate)
        _ = X.correctionCoordinate + 0 := by
          exact congrArg (fun Z : ℝ => X.correctionCoordinate + Z)
            (add_right_neg Y.correctionCoordinate)
        _ = X.correctionCoordinate := by
          exact add_zero X.correctionCoordinate).symm

/-- Two Hilbert-source representatives have the same reduced time-pairing scalar when their
difference is lower-weight radical, provided the completed Hilbert pairing is additive in both
variables. -/
theorem completedBoundaryTimePairingScalar_eq_of_lowerWeightRadical_sub
    (B_add_left :
      ∀ x y z : CompletedBoundaryHilbertSource,
        completedBoundaryHilbertPairing (x + y) z =
          completedBoundaryHilbertPairing x z +
            completedBoundaryHilbertPairing y z)
    (B_add_right :
      ∀ x y z : CompletedBoundaryHilbertSource,
        completedBoundaryHilbertPairing x (y + z) =
          completedBoundaryHilbertPairing x y +
            completedBoundaryHilbertPairing x z)
    (X Y : CompletedBoundaryHilbertSource)
    (hD : CompletedBoundaryHilbertSource.LowerWeightRadical (X - Y)) :
    completedBoundaryTimePairingScalar X =
      completedBoundaryTimePairingScalar Y := by
  have hdecomp : X = Y + (X - Y) :=
    completedBoundaryHilbertSource_eq_add_sub X Y
  calc
    completedBoundaryTimePairingScalar X =
        completedBoundaryTimePairingScalar (Y + (X - Y)) := by
      exact congrArg completedBoundaryTimePairingScalar hdecomp
    _ =
        completedBoundaryTimePairingScalar Y := by
      exact completedBoundaryTimePairingScalar_eq_of_add_lowerWeightRadical
        B_add_left
        B_add_right
        Y
        (X - Y)
        hD

/-- Rearranging the real parts of the reduced channel plus pole channel. -/
theorem completedBoundaryReduced_re_add_pole_re_middle_swap
    (p a q r : ℝ) :
    (p + a + r) + q = p + a + q + r := by
  calc
    (p + a + r) + q = ((p + a) + r) + q := by
      rfl
    _ = (p + a) + (r + q) := by
      exact add_assoc (p + a) r q
    _ = (p + a) + (q + r) := by
      exact congrArg (fun x : ℝ => (p + a) + x) (add_comm r q)
    _ = ((p + a) + q) + r := by
      exact (add_assoc (p + a) q r).symm
    _ = p + a + q + r := by
      rfl

/-- Rearranging the real parts of the reduced channel plus pole channel. -/
theorem completedBoundaryReduced_re_add_pole_re
    (p a q r : ℂ) :
    Complex.re (p + a + r) + Complex.re q =
      Complex.re (p + a + q + r) := by
  calc
    Complex.re (p + a + r) + Complex.re q =
        (Complex.re (p + a) + Complex.re r) + Complex.re q := by
      exact congrArg (fun x : ℝ => x + Complex.re q)
        (Complex.add_re (p + a) r)
    _ =
        (Complex.re p + Complex.re a + Complex.re r) + Complex.re q := by
      exact congrArg (fun x : ℝ => (x + Complex.re r) + Complex.re q)
        (Complex.add_re p a)
    _ =
        Complex.re p + Complex.re a + Complex.re q + Complex.re r := by
      exact completedBoundaryReduced_re_add_pole_re_middle_swap
        (Complex.re p) (Complex.re a) (Complex.re q) (Complex.re r)
    _ =
        Complex.re (p + a + q) + Complex.re r := by
      exact congrArg (fun x : ℝ => x + Complex.re r)
        ((congrArg (fun x : ℝ => x + Complex.re q)
          (Complex.add_re p a)).symm)
    _ =
        Complex.re (p + a + q + r) := by
      exact (Complex.add_re (p + a + q) r).symm

/-- The Hilbert pairing of a realized seed with itself is the real completed boundary
channel on its autocorrelation probe.  The affine pole/correction contribution is represented
by the explicit correction coordinate in `CompletedBoundaryHilbertSource`. -/
theorem completedBoundaryHilbertPairing_source_self_eq_boundaryChannel_re
    (f : ZetaAdmissibleFunction) :
    completedBoundaryHilbertPairing
        (completedBoundaryHilbertSource f)
        (completedBoundaryHilbertSource f) =
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) := by
  let g : ZetaAdmissibleFunction := convolutionAutocorrelation f
  let p : ℂ := primeBoundaryChannel g
  let a : ℂ := archimedeanBoundaryChannel g
  let q : ℂ := poleBoundaryChannel g
  let r : ℂ := completionBoundaryChannel g
  have hconv : convolutionPair f f = g := by
    unfold g
    exact convolutionPair_self f
  have hcorr :
      (completedBoundaryHilbertSource f).correctionCoordinate *
          (completedBoundaryHilbertSource f).correctionCoordinate =
        Complex.re q := by
    have hcoord :
        (completedBoundaryHilbertSource f).correctionCoordinate *
            (completedBoundaryHilbertSource f).correctionCoordinate =
          ZetaHermitianPacketEnsemble.correctionPacketGram
            (zetaCompletedHermitianBoundaryDefect f) :=
      completedBoundaryHilbertSource_correctionCoordinate_sq f
    have hq :
        Complex.re q =
          ZetaHermitianPacketEnsemble.correctionPacketGram
            (zetaCompletedHermitianBoundaryDefect f) := by
      unfold q
      unfold g
      change
        Complex.re
            (zetaCompletedExplicitFormulaCorrectionContribution
              (convolutionAutocorrelation f)) =
          ZetaHermitianPacketEnsemble.correctionPacketGram
            (zetaCompletedHermitianBoundaryDefect f)
      have howner :
          zetaCompletedExplicitFormulaCorrectionContribution
              (convolutionAutocorrelation f) =
            zetaCompletedExplicitFormulaCorrectionConvolutionContribution f :=
        zetaCompletedExplicitFormulaCorrectionContribution_convolutionAutocorrelation_eq_owner
          f
      calc
        Complex.re
            (zetaCompletedExplicitFormulaCorrectionContribution
              (convolutionAutocorrelation f)) =
            Complex.re
              (zetaCompletedExplicitFormulaCorrectionConvolutionContribution f) := by
          exact congrArg Complex.re howner
        _ =
            ZetaHermitianPacketEnsemble.correctionPacketGram
              (zetaCompletedHermitianBoundaryDefect f) := by
          exact
            zetaCompletedExplicitFormulaCorrectionConvolutionChannel_holographic
              f
    exact hcoord.trans hq.symm
  have hchannel :
      completedBoundaryChannel g = p + a + q + r := by
    unfold p
    unfold a
    unfold q
    unfold r
    exact completedBoundaryChannel_eq_prime_add_archimedean_add_pole_add_completion g
  have hreduced :
      primeBoundaryChannel (convolutionPair f f) +
          archimedeanBoundaryChannel (convolutionPair f f) +
          completionBoundaryChannel (convolutionPair f f) =
        p + a + r := by
    calc
      primeBoundaryChannel (convolutionPair f f) +
          archimedeanBoundaryChannel (convolutionPair f f) +
          completionBoundaryChannel (convolutionPair f f) =
        primeBoundaryChannel g +
            archimedeanBoundaryChannel g +
            completionBoundaryChannel g := by
        exact congrArg
          (fun u : ZetaAdmissibleFunction =>
            primeBoundaryChannel u + archimedeanBoundaryChannel u +
              completionBoundaryChannel u)
          hconv
      _ = p + a + r := by
        rfl
  unfold completedBoundaryHilbertPairing
  unfold completedBoundaryHilbertSource
  unfold completedBoundaryReducedChannel
  calc
    Complex.re
          (primeBoundaryChannel (convolutionPair f f) +
            archimedeanBoundaryChannel (convolutionPair f f) +
            completionBoundaryChannel (convolutionPair f f)) +
        (completedBoundaryHilbertSource f).correctionCoordinate *
          (completedBoundaryHilbertSource f).correctionCoordinate =
        Complex.re (p + a + r) +
          (completedBoundaryHilbertSource f).correctionCoordinate *
            (completedBoundaryHilbertSource f).correctionCoordinate := by
      exact congrArg₂ HAdd.hAdd
        (congrArg Complex.re hreduced)
        rfl
    _ = Complex.re (p + a + r) + Complex.re q := by
      exact congrArg
        (fun x : ℝ => Complex.re (p + a + r) + x)
        hcorr
    _ = Complex.re (p + a + q + r) := by
      exact completedBoundaryReduced_re_add_pole_re p a q r
    _ = Complex.re (completedBoundaryChannel g) := by
      exact congrArg Complex.re hchannel.symm

/-- The reconstructed prime convolution channel and the positive prime-defect channel add to
the finite prime diagonal debt. -/
theorem zetaCompletedExplicitFormulaPrimeConvolutionContribution_re_add_positiveChannel_eq_diagonalDebt_re
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) +
        completedPrimeDefectKernelPositiveChannel f =
      Complex.re (zetaPrimeDefectKernelDiagonalDebt f) := by
  let P : ℂ := zetaPrimeDefectKernelPositiveForm f
  let B : ℂ := zetaCompletedExplicitFormulaPrimeConvolutionContribution f
  let D : ℂ := zetaPrimeDefectKernelDiagonalDebt f
  have hpositive :
      completedPrimeDefectKernelPositiveChannel f = Complex.re P := by
    exact completedPrimeDefectKernelPositiveChannel_eq_finitePositiveForm_re f
  have hbalance :
      P + B = D := by
    exact zetaCompletedExplicitFormulaPrimeConvolutionContribution_add_primeDefectKernelPositiveForm_eq_diagonalDebt
      f
  calc
    Complex.re B + completedPrimeDefectKernelPositiveChannel f =
        Complex.re B + Complex.re P := by
      exact congrArg (fun x : ℝ => Complex.re B + x) hpositive
    _ = Complex.re P + Complex.re B := by
      exact add_comm (Complex.re B) (Complex.re P)
    _ = Complex.re (P + B) := by
      exact (Complex.add_re P B).symm
    _ = Complex.re D := by
      exact congrArg Complex.re hbalance

/-- The finite time-distribution window of an autocorrelation is the physical
off-diagonal prime window. -/
theorem finitePrimeTimeDistributionWindow_convolutionAutocorrelation_eq_physical
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) =
      finitePhysicalPrimeOffDiagonalWindow N f := by
  unfold finitePrimeTimeDistributionWindow
  unfold finitePhysicalPrimeOffDiagonalWindow
  unfold finitePartPrimeOffDiagonalWindow
  unfold zetaPrimeOffDiagonalChannel
  exact Finset.sum_congr rfl
    (fun ι _hι =>
      completedPrimeTimeDistributionCoordinate_convolutionAutocorrelation_eq_physical
        ι f)

/-- The finite time-distribution windows exhaust the completed time distribution pairing. -/
theorem finitePrimeTimeDistributionWindow_convolutionAutocorrelation_tendsto_timePairing
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ =>
        finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f))
      atTop
      (𝓝 (completedPrimeTimeDistributionPairing
        (convolutionAutocorrelation f))) := by
  have hfun :
      (fun N : ℕ =>
          finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f)) =
        fun N : ℕ => finitePhysicalPrimeOffDiagonalWindow N f := by
    funext N
    exact finitePrimeTimeDistributionWindow_convolutionAutocorrelation_eq_physical
      N f
  have hphysical :
      Tendsto
        (fun N : ℕ => finitePhysicalPrimeOffDiagonalWindow N f)
        atTop
        (𝓝 (completedPhysicalPrimeOffDiagonalChannel f)) :=
    finitePhysicalPrimeOffDiagonalWindow_tendsto_completedPhysicalPrimeOffDiagonalChannel
      f
  have hlimit :
      completedPhysicalPrimeOffDiagonalChannel f =
        completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) :=
    completedPhysicalPrimeOffDiagonalChannel_eq_timeDistributionPairing f
  have hphysical_time :
      Tendsto
        (fun N : ℕ => finitePhysicalPrimeOffDiagonalWindow N f)
        atTop
        (𝓝 (completedPrimeTimeDistributionPairing
          (convolutionAutocorrelation f))) :=
    Eq.subst
      (motive := fun x : ℝ =>
        Tendsto
          (fun N : ℕ => finitePhysicalPrimeOffDiagonalWindow N f)
          atTop
          (𝓝 x))
      hlimit
      hphysical
  exact Eq.subst
    (motive := fun u : ℕ → ℝ =>
      Tendsto u atTop
        (𝓝 (completedPrimeTimeDistributionPairing
          (convolutionAutocorrelation f))))
    hfun.symm
    hphysical_time

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
