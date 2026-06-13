import Boundary.LFunctions.ZetaPrimeAutocorrelationControl

/-!
# Prime horizontal decay

This file owns product-form horizontal control and the finite contour-transport
decay statements used by completed prime tomography.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- Product-form horizontal control for the completed prime contour transport.

This is the long-term horizontal-decay API for the RH lane: the horizontal integrand is
controlled by the product of the completed-zeta logarithmic derivative and the probe
transform.  It does not require the logarithmic derivative to have rapid decay by itself. -/
structure CompletedPrimeProductHorizontalControl
    (f : ZetaAdmissibleFunction) where
  product_strip_decay :
    ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ),
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          z ∈ E.carrier →
          ‖completedZetaNegLogDeriv z‖ *
              ‖zetaCompletedExplicitFormulaPhi
                (convolutionAutocorrelation f) (z - 1 / 2)‖
            ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ))}

/-- The completed prime contour transport has product-form horizontal control. -/
theorem completedPrimeProductHorizontalControl_of_autocorrelation
    (f : ZetaAdmissibleFunction) :
    CompletedPrimeProductHorizontalControl f := by
  exact
	    { product_strip_decay :=
	        fun a b E N =>
	          completedZetaNegLogDeriv_times_shiftedAutocorrelationPhi_zeroExcisedRapidStripDecay
	            f a b E N }

/-- Product-form horizontal envelope for the sampled prime contour family. -/
def sampledProductHorizontalEnvelope
    (C : ℝ) (N : ℕ) : ℕ → ℝ :=
  fun M =>
    C *
      (1 + ‖(M : ℝ)‖) ^ (-(N : ℤ)) *
      (2 * horizontalEdgeLength completedPrimeContourTransportFamily.c)

/-- Product-form horizontal envelope constants exist for the sampled prime contour family. -/
theorem exists_sampledProductHorizontalEnvelopeConstant
    (f : ZetaAdmissibleFunction)
    (hcontrol : CompletedPrimeProductHorizontalControl f)
    (E : CompletedZetaZeroExcisedStrip
      (min completedPrimeContourTransportFamily.c
        (1 - completedPrimeContourTransportFamily.c))
      (max completedPrimeContourTransportFamily.c
        (1 - completedPrimeContourTransportFamily.c)))
    (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        z ∈ E.carrier →
        ‖completedZetaNegLogDeriv z‖ *
            ‖zetaCompletedExplicitFormulaPhi
              (convolutionAutocorrelation f) (z - 1 / 2)‖
          ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ)) := by
  exact hcontrol.product_strip_decay
    (min completedPrimeContourTransportFamily.c
      (1 - completedPrimeContourTransportFamily.c))
    (max completedPrimeContourTransportFamily.c
      (1 - completedPrimeContourTransportFamily.c))
    E
    N

/-- The time-side contour-transport coordinates are summable at an autocorrelation probe. -/
theorem summable_completedPrimeTimeDistributionCoordinate_convolutionAutocorrelation
    (f : ZetaAdmissibleFunction) :
    Summable
      (fun ι : ZetaPrimePowerIndex =>
        completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f)) := by
  exact (summable_zetaPrimeOffDiagonalCoordinate f).congr
    (fun ι : ZetaPrimePowerIndex =>
      (completedPrimeTimeDistributionCoordinate_convolutionAutocorrelation_eq_physical
        ι f).symm)

/-- Nongenuine indices have zero contour-realized prime distribution coordinate. -/
theorem completedPrimeContourRealizedTimeDistributionCoordinate_eq_zero_of_not_isGenuine
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction)
    (hι : ¬ ZetaPrimePowerIndex.IsGenuine ι) :
    completedPrimeContourRealizedTimeDistributionCoordinate
      ι (convolutionAutocorrelation f) = 0 := by
  have hweight : ι.weight = 0 :=
    ZetaPrimePowerIndex.weight_eq_zero_of_not_isGenuine ι hι
  unfold completedPrimeContourRealizedTimeDistributionCoordinate
  calc
    Complex.re
        (-((ι.weight : ℂ) *
          (zetaCompletedSpectralLaplaceTransform
              (convolutionAutocorrelation f) ι.center +
            star
              (zetaCompletedSpectralLaplaceTransform
                (convolutionAutocorrelation f) ι.center)))) =
        Complex.re
          (-((0 : ℂ) *
            (zetaCompletedSpectralLaplaceTransform
                (convolutionAutocorrelation f) ι.center +
              star
                (zetaCompletedSpectralLaplaceTransform
                  (convolutionAutocorrelation f) ι.center)))) := by
      exact congrArg
        (fun x : ℝ =>
          Complex.re
            (-((x : ℂ) *
              (zetaCompletedSpectralLaplaceTransform
                  (convolutionAutocorrelation f) ι.center +
                star
                  (zetaCompletedSpectralLaplaceTransform
                    (convolutionAutocorrelation f) ι.center)))))
        hweight
    _ = Complex.re (-(0 : ℂ)) := by
      exact congrArg (fun x : ℂ => Complex.re (-x))
        (zero_mul
          (zetaCompletedSpectralLaplaceTransform
              (convolutionAutocorrelation f) ι.center +
            star
              (zetaCompletedSpectralLaplaceTransform
                (convolutionAutocorrelation f) ι.center)))
    _ = Complex.re (0 : ℂ) := by
      exact congrArg Complex.re (neg_zero : -(0 : ℂ) = 0)
    _ = 0 := by
      exact Complex.zero_re

/-- Rectangular prime-power height used by the contour-localization majorant. -/
def primeContourLocalizationHeight (ι : ZetaPrimePowerIndex) : ℕ :=
  max ι.p ι.n

/-- Polynomial contour-localization majorant on prime-power coordinates. -/
noncomputable def completedPrimeContourLocalizationMajorant
    (C : ℝ) (k : ℕ) (ι : ZetaPrimePowerIndex) : ℝ :=
  C *
    (1 + ‖((primeContourLocalizationHeight ι : ℕ) : ℝ)‖) ^
      (-(k + 3 : ℤ))

/-- The contour-localization majorant is nonnegative when its constant is nonnegative. -/
theorem completedPrimeContourLocalizationMajorant_nonnegative
    {C : ℝ} (hC : 0 ≤ C) (k : ℕ) (ι : ZetaPrimePowerIndex) :
    0 ≤ completedPrimeContourLocalizationMajorant C k ι := by
  unfold completedPrimeContourLocalizationMajorant
  have hbase :
      0 ≤
        (1 + ‖((primeContourLocalizationHeight ι : ℕ) : ℝ)‖) ^
          (-(k + 3 : ℤ)) :=
    zpow_nonneg
      (add_nonneg zero_le_one
        (norm_nonneg (((primeContourLocalizationHeight ι : ℕ) : ℝ))))
      (-(k + 3 : ℤ))
  exact mul_nonneg hC hbase

/-- Polynomial prime-power height decay is summable in the two prime-power coordinates. -/
theorem summable_completedPrimeContourLocalizationMajorant
    (C : ℝ) (k : ℕ) :
    Summable
      (fun ι : ZetaPrimePowerIndex =>
        completedPrimeContourLocalizationMajorant C k ι) := by
  sorry

/-- Completed contour localization gives a polynomially summable coordinate majorant.

This is the owner analytic estimate: product-form horizontal decay, prime-power counting, and
tomographic residue localization give constants whose height-majorant dominates every
coordinate remainder majorant. -/
theorem exists_completedPrimeContourLocalizationMajorant_bound
    (f : ZetaAdmissibleFunction) :
    ∃ C : ℝ, ∃ k : ℕ,
      0 < C ∧
      ∀ ι : ZetaPrimePowerIndex,
        completedPrimeContourTransportCoordinateRemainderMajorant ι f ≤
          completedPrimeContourLocalizationMajorant C k ι := by
  sorry

/-- The coordinate-remainder majorant is summable from the completed contour-localization
estimate for the contour-transport family.

This is the analytic owner step behind prime contour transport.  It is not a consequence
of polynomial decay in the prime-power center alone; the completed localization data must
provide the genuinely summable coordinate control. -/
theorem summable_completedPrimeContourTransportCoordinateRemainderMajorant_of_contourLocalization
    (f : ZetaAdmissibleFunction) :
    Summable
      (fun ι : ZetaPrimePowerIndex =>
        completedPrimeContourTransportCoordinateRemainderMajorant ι f) := by
  rcases exists_completedPrimeContourLocalizationMajorant_bound f with
    ⟨C, k, hCpos, hbound⟩
  have hloc :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          completedPrimeContourLocalizationMajorant C k ι) :=
    summable_completedPrimeContourLocalizationMajorant C k
  have hnormBound :
      ∀ ι : ZetaPrimePowerIndex,
        ‖completedPrimeContourTransportCoordinateRemainderMajorant ι f‖ ≤
          completedPrimeContourLocalizationMajorant C k ι := by
    intro ι
    have hmajorant_nonneg :
        0 ≤ completedPrimeContourTransportCoordinateRemainderMajorant ι f :=
      completedPrimeContourTransportCoordinateRemainderMajorant_nonnegative ι f
    have hnorm :
        ‖completedPrimeContourTransportCoordinateRemainderMajorant ι f‖ =
          completedPrimeContourTransportCoordinateRemainderMajorant ι f :=
      Real.norm_of_nonneg hmajorant_nonneg
    exact Eq.subst
      (motive := fun x : ℝ =>
        x ≤ completedPrimeContourLocalizationMajorant C k ι)
      hnorm.symm
      (hbound ι)
  exact Summable.of_norm_bounded
    (fun ι : ZetaPrimePowerIndex =>
      completedPrimeContourLocalizationMajorant C k ι)
    hloc
    hnormBound

/-- The contour-transport coordinate-remainder majorant is summable by the prime
tomography residue theorem and horizontal contour decay. -/
theorem summable_completedPrimeContourTransportCoordinateRemainderMajorant_of_horizontalDecay
    (f : ZetaAdmissibleFunction) :
    Summable
      (fun ι : ZetaPrimePowerIndex =>
        completedPrimeContourTransportCoordinateRemainderMajorant ι f) := by
  exact
    summable_completedPrimeContourTransportCoordinateRemainderMajorant_of_contourLocalization f

/-- The contour-transport coordinate remainder is summable by horizontal contour decay. -/
theorem summable_completedPrimeContourTransportCoordinateRemainder_of_horizontalDecay
    (f : ZetaAdmissibleFunction) :
    Summable
      (fun ι : ZetaPrimePowerIndex =>
        completedPrimeContourTransportCoordinateRemainder ι f) := by
  have hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          completedPrimeContourTransportCoordinateRemainderMajorant ι f) :=
    summable_completedPrimeContourTransportCoordinateRemainderMajorant_of_horizontalDecay f
  unfold completedPrimeContourTransportCoordinateRemainderMajorant at hmajorant
  exact hmajorant.of_norm

/-- A contour-realized prime coordinate is the physical time coordinate plus the
contour-transport remainder. -/
theorem completedPrimeContourRealizedTimeDistributionCoordinate_eq_remainder_add_time
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    completedPrimeContourRealizedTimeDistributionCoordinate
        ι (convolutionAutocorrelation f) =
      completedPrimeContourTransportCoordinateRemainder ι f +
        completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f) := by
  unfold completedPrimeContourTransportCoordinateRemainder
  exact (sub_add_cancel
    (completedPrimeContourRealizedTimeDistributionCoordinate
      ι (convolutionAutocorrelation f))
    (completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f))).symm

/-- The contour-realized prime distribution coordinates are summable at an
autocorrelation probe. -/
theorem summable_completedPrimeContourRealizedTimeDistributionCoordinate_convolutionAutocorrelation
    (f : ZetaAdmissibleFunction) :
    Summable
      (fun ι : ZetaPrimePowerIndex =>
        completedPrimeContourRealizedTimeDistributionCoordinate
          ι (convolutionAutocorrelation f)) := by
  have hrem :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          completedPrimeContourTransportCoordinateRemainder ι f) :=
    summable_completedPrimeContourTransportCoordinateRemainder_of_horizontalDecay f
  have htime :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          completedPrimeTimeDistributionCoordinate ι
            (convolutionAutocorrelation f)) :=
    summable_completedPrimeTimeDistributionCoordinate_convolutionAutocorrelation f
  exact (hrem.add htime).congr
    (fun ι : ZetaPrimePowerIndex =>
      (completedPrimeContourRealizedTimeDistributionCoordinate_eq_remainder_add_time
        ι f).symm)

/-- The finite contour-realized prime windows converge to the completed contour-realized
prime distribution.  This is a wrapper around the owner horizontal/contour summability
theorem above. -/
theorem finitePrimeContourRealizedWindow_tendsto_completed
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ =>
        finitePrimeContourRealizedTimeDistributionWindow N
          (convolutionAutocorrelation f))
      atTop
      (𝓝
        (completedPrimeContourRealizedTimeDistributionPairing
          (convolutionAutocorrelation f))) := by
  have hsum :
      Summable (fun ι : ZetaPrimePowerIndex =>
        completedPrimeContourRealizedTimeDistributionCoordinate
          ι (convolutionAutocorrelation f)) :=
    summable_completedPrimeContourRealizedTimeDistributionCoordinate_convolutionAutocorrelation f
  have hzero :
      ∀ ι : ZetaPrimePowerIndex, ¬ ZetaPrimePowerIndex.IsGenuine ι →
        completedPrimeContourRealizedTimeDistributionCoordinate
          ι (convolutionAutocorrelation f) = 0 := by
    intro ι hι
    exact
      completedPrimeContourRealizedTimeDistributionCoordinate_eq_zero_of_not_isGenuine
        ι (convolutionAutocorrelation f) hι
  unfold finitePrimeContourRealizedTimeDistributionWindow
  unfold completedPrimeContourRealizedTimeDistributionPairing
  unfold completedPrimeSpectralDistributionPairing
  exact ZetaPrimePowerIndex.tendsto_sum_window_tsum_of_summable
    (fun ι : ZetaPrimePowerIndex =>
      completedPrimeContourRealizedTimeDistributionCoordinate
        ι (convolutionAutocorrelation f))
    hsum hzero

/-- The finite contour-transport remainder tends to the completed difference between the
contour-realized and time-side prime channels. -/
theorem finitePrimeContourTransportRemainder_tendsto_boundaryDifference
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ => finitePrimeContourTransportRemainder N f)
      atTop
      (𝓝 (completedPrimeContourTransportBoundaryDifference f)) := by
  have hcontour :
      Tendsto
        (fun N : ℕ =>
          finitePrimeContourRealizedTimeDistributionWindow N
            (convolutionAutocorrelation f))
        atTop
        (𝓝
          (completedPrimeContourRealizedTimeDistributionPairing
            (convolutionAutocorrelation f))) :=
    finitePrimeContourRealizedWindow_tendsto_completed f
  have htime :
      Tendsto
        (fun N : ℕ =>
          finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f))
        atTop
        (𝓝 (completedPrimeTimeDistributionPairing (convolutionAutocorrelation f))) :=
    finitePrimeTimeDistributionWindow_tendsto_completed f
  have hdifference :
      Tendsto
        (fun N : ℕ =>
          finitePrimeContourRealizedTimeDistributionWindow N
              (convolutionAutocorrelation f) -
            finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f))
        atTop
        (𝓝
          (completedPrimeContourRealizedTimeDistributionPairing
              (convolutionAutocorrelation f) -
            completedPrimeTimeDistributionPairing (convolutionAutocorrelation f))) := by
    exact hcontour.sub htime
  unfold finitePrimeContourTransportRemainder
  unfold completedPrimeContourTransportBoundaryDifference
  exact hdifference

/-- A real coordinate family is summable when its norm is bounded by a summable nonnegative
majorant. -/
theorem summable_real_family_of_norm_le_majorant
    (u v : ZetaPrimePowerIndex → ℝ)
    (hv : Summable v)
    (hv_nonneg : ∀ ι : ZetaPrimePowerIndex, 0 ≤ v ι)
    (hbound : ∀ ι : ZetaPrimePowerIndex, ‖u ι‖ ≤ v ι) :
    Summable u := by
  exact Summable.of_norm_bounded v hv hbound

/-- The completed contour-transport coordinate remainder is summable. -/
theorem summable_completedPrimeContourTransportCoordinateRemainder
    (f : ZetaAdmissibleFunction) :
    Summable
      (fun ι : ZetaPrimePowerIndex =>
        completedPrimeContourTransportCoordinateRemainder ι f) := by
  exact summable_completedPrimeContourTransportCoordinateRemainder_of_horizontalDecay f

/-- The completed contour-transport coordinate remainder majorant is summable. -/
theorem summable_completedPrimeContourTransportCoordinateRemainderMajorant
    (f : ZetaAdmissibleFunction) :
    Summable
      (fun ι : ZetaPrimePowerIndex =>
        completedPrimeContourTransportCoordinateRemainderMajorant ι f) := by
  exact summable_completedPrimeContourTransportCoordinateRemainderMajorant_of_horizontalDecay f

/-- The tail of the contour-transport coordinate remainder is controlled by its own
coordinate-remainder majorant tail. -/
theorem norm_coordinateRemainderTail_le_coordinateRemainderMajorantTail
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    ‖(∑' ι : ZetaPrimePowerIndex,
        if ι ∈ ZetaPrimePowerIndex.window N then
          0
        else
          completedPrimeContourTransportCoordinateRemainder ι f)‖ ≤
      ∑' ι : ZetaPrimePowerIndex,
        if ι ∈ ZetaPrimePowerIndex.window N then
          0
        else
          completedPrimeContourTransportCoordinateRemainderMajorant ι f := by
  let u : ZetaPrimePowerIndex → ℝ :=
    fun ι => completedPrimeContourTransportCoordinateRemainder ι f
  let v : ZetaPrimePowerIndex → ℝ :=
    fun ι => completedPrimeContourTransportCoordinateRemainderMajorant ι f
  have hv : Summable v := by
    exact summable_completedPrimeContourTransportCoordinateRemainderMajorant f
  have hbound : ∀ ι : ZetaPrimePowerIndex, ‖u ι‖ ≤ v ι := by
    intro ι
    unfold u
    unfold v
    exact norm_completedPrimeContourTransportCoordinateRemainder_le_remainderMajorant ι f
  change
    ‖(∑' ι : ZetaPrimePowerIndex, ZetaPrimePowerIndex.spectralTail u N ι)‖ ≤
      ∑' ι : ZetaPrimePowerIndex, ZetaPrimePowerIndex.spectralTail v N ι
  exact
    ZetaPrimePowerIndex.norm_spectralTail_tsum_le_spectralTail_tsum_of_norm_le
      u v hv hbound N

/-- The two horizontal edge envelopes combine into the product envelope with the explicit
factor `2`. -/
theorem two_horizontalEdgeEnvelope_eq_productEnvelope
    (A B L : ℝ) :
    A * B * L + A * B * L = A * B * (2 * L) := by
  calc
    A * B * L + A * B * L =
        (A * B) * L + (A * B) * L := by
      rfl
    _ = 2 * ((A * B) * L) := by
      exact (two_mul ((A * B) * L)).symm
    _ = (2 * (A * B)) * L := by
      exact mul_assoc 2 (A * B) L
    _ = ((A * B) * 2) * L := by
      exact congrArg (fun x : ℝ => x * L) (mul_comm 2 (A * B))
    _ = (A * B) * (2 * L) := by
      exact (mul_assoc (A * B) 2 L).symm
    _ = A * B * (2 * L) := by
      rfl

/-- Product-form control bounds the top horizontal contour integrand pointwise. -/
theorem sampledTopHorizontalIntegrand_norm_le_productEnvelope
    (f : ZetaAdmissibleFunction)
    (C : ℝ)
    (hC :
      ∀ z : ℂ,
        min completedPrimeContourTransportFamily.c
            (1 - completedPrimeContourTransportFamily.c) ≤ z.re →
        z.re ≤ max completedPrimeContourTransportFamily.c
            (1 - completedPrimeContourTransportFamily.c) →
        ‖completedZetaNegLogDeriv z‖ *
            ‖zetaCompletedExplicitFormulaPhi
              (convolutionAutocorrelation f) (z - 1 / 2)‖
          ≤ C * (1 + ‖z.im‖) ^ (-(1 : ℤ)))
    (N : ℕ) (x : ℝ)
    (hx :
      x ∈ Set.uIcc completedPrimeContourTransportFamily.c
        (1 - completedPrimeContourTransportFamily.c)) :
    ‖completedZetaNegLogDeriv
          (zetaCompletedExplicitFormulaTopPath
            (completedPrimeContourTransportFamily.rectangle (N : ℝ)) x) *
        zetaCompletedExplicitFormulaPhi
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormulaTopPath
            (completedPrimeContourTransportFamily.rectangle (N : ℝ)) x - 1 / 2)‖ ≤
      C * (1 + ‖(N : ℝ)‖) ^ (-(1 : ℤ)) := by
  let r : ExplicitFormulaRectangle :=
    completedPrimeContourTransportFamily.rectangle (N : ℝ)
  let z : ℂ := zetaCompletedExplicitFormulaTopPath r x
  have hstrip :
      min completedPrimeContourTransportFamily.c
          (1 - completedPrimeContourTransportFamily.c) ≤ z.re ∧
        z.re ≤
          max completedPrimeContourTransportFamily.c
            (1 - completedPrimeContourTransportFamily.c) := by
    unfold z
    unfold r
    exact zetaCompletedExplicitFormulaTopPath_re_mem_uIcc_bounds
      (completedPrimeContourTransportFamily.rectangle (N : ℝ)) x hx
  have hprod :
      ‖completedZetaNegLogDeriv z‖ *
          ‖zetaCompletedExplicitFormulaPhi
            (convolutionAutocorrelation f) (z - 1 / 2)‖
        ≤ C * (1 + ‖z.im‖) ^ (-(1 : ℤ)) :=
    hC z hstrip.1 hstrip.2
  have him :
      ‖z.im‖ = ‖(N : ℝ)‖ := by
    unfold z
    unfold r
    exact zetaCompletedExplicitFormulaTopPath_im_norm
      (completedPrimeContourTransportFamily.rectangle (N : ℝ)) x
  have hproduct_norm :
      ‖completedZetaNegLogDeriv z *
          zetaCompletedExplicitFormulaPhi
            (convolutionAutocorrelation f) (z - 1 / 2)‖
        ≤ ‖completedZetaNegLogDeriv z‖ *
            ‖zetaCompletedExplicitFormulaPhi
              (convolutionAutocorrelation f) (z - 1 / 2)‖ :=
    norm_mul_le _ _
  have htarget_product :
      ‖completedZetaNegLogDeriv z‖ *
          ‖zetaCompletedExplicitFormulaPhi
            (convolutionAutocorrelation f) (z - 1 / 2)‖
        ≤ C * (1 + ‖(N : ℝ)‖) ^ (-(1 : ℤ)) := by
    exact Eq.subst
      (motive := fun y : ℝ =>
        ‖completedZetaNegLogDeriv z‖ *
            ‖zetaCompletedExplicitFormulaPhi
              (convolutionAutocorrelation f) (z - 1 / 2)‖
          ≤ C * (1 + y) ^ (-(1 : ℤ)))
      him
      hprod
  exact hproduct_norm.trans htarget_product

/-- Product-form control bounds the bottom horizontal contour integrand pointwise. -/
theorem sampledBottomHorizontalIntegrand_norm_le_productEnvelope
    (f : ZetaAdmissibleFunction)
    (C : ℝ)
    (hC :
      ∀ z : ℂ,
        min completedPrimeContourTransportFamily.c
            (1 - completedPrimeContourTransportFamily.c) ≤ z.re →
        z.re ≤ max completedPrimeContourTransportFamily.c
            (1 - completedPrimeContourTransportFamily.c) →
        ‖completedZetaNegLogDeriv z‖ *
            ‖zetaCompletedExplicitFormulaPhi
              (convolutionAutocorrelation f) (z - 1 / 2)‖
          ≤ C * (1 + ‖z.im‖) ^ (-(1 : ℤ)))
    (N : ℕ) (x : ℝ)
    (hx :
      x ∈ Set.uIcc completedPrimeContourTransportFamily.c
        (1 - completedPrimeContourTransportFamily.c)) :
    ‖completedZetaNegLogDeriv
          (zetaCompletedExplicitFormulaBottomPath
            (completedPrimeContourTransportFamily.rectangle (N : ℝ)) x) *
        zetaCompletedExplicitFormulaPhi
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormulaBottomPath
            (completedPrimeContourTransportFamily.rectangle (N : ℝ)) x - 1 / 2)‖ ≤
      C * (1 + ‖(N : ℝ)‖) ^ (-(1 : ℤ)) := by
  let r : ExplicitFormulaRectangle :=
    completedPrimeContourTransportFamily.rectangle (N : ℝ)
  let z : ℂ := zetaCompletedExplicitFormulaBottomPath r x
  have hstrip :
      min completedPrimeContourTransportFamily.c
          (1 - completedPrimeContourTransportFamily.c) ≤ z.re ∧
        z.re ≤
          max completedPrimeContourTransportFamily.c
            (1 - completedPrimeContourTransportFamily.c) := by
    unfold z
    unfold r
    exact zetaCompletedExplicitFormulaBottomPath_re_mem_uIcc_bounds
      (completedPrimeContourTransportFamily.rectangle (N : ℝ)) x hx
  have hprod :
      ‖completedZetaNegLogDeriv z‖ *
          ‖zetaCompletedExplicitFormulaPhi
            (convolutionAutocorrelation f) (z - 1 / 2)‖
        ≤ C * (1 + ‖z.im‖) ^ (-(1 : ℤ)) :=
    hC z hstrip.1 hstrip.2
  have him :
      ‖z.im‖ = ‖(N : ℝ)‖ := by
    unfold z
    unfold r
    exact zetaCompletedExplicitFormulaBottomPath_im_norm
      (completedPrimeContourTransportFamily.rectangle (N : ℝ)) x
  have hproduct_norm :
      ‖completedZetaNegLogDeriv z *
          zetaCompletedExplicitFormulaPhi
            (convolutionAutocorrelation f) (z - 1 / 2)‖
        ≤ ‖completedZetaNegLogDeriv z‖ *
            ‖zetaCompletedExplicitFormulaPhi
              (convolutionAutocorrelation f) (z - 1 / 2)‖ :=
    norm_mul_le _ _
  have htarget_product :
      ‖completedZetaNegLogDeriv z‖ *
          ‖zetaCompletedExplicitFormulaPhi
            (convolutionAutocorrelation f) (z - 1 / 2)‖
        ≤ C * (1 + ‖(N : ℝ)‖) ^ (-(1 : ℤ)) := by
    exact Eq.subst
      (motive := fun y : ℝ =>
        ‖completedZetaNegLogDeriv z‖ *
            ‖zetaCompletedExplicitFormulaPhi
              (convolutionAutocorrelation f) (z - 1 / 2)‖
          ≤ C * (1 + y) ^ (-(1 : ℤ)))
      him
      hprod
  exact hproduct_norm.trans htarget_product

/-- Product-form control bounds the top horizontal contour integral. -/
theorem sampledTopHorizontalIntegral_norm_le_productEnvelope
    (f : ZetaAdmissibleFunction)
    (C : ℝ)
    (hC :
      ∀ z : ℂ,
        min completedPrimeContourTransportFamily.c
            (1 - completedPrimeContourTransportFamily.c) ≤ z.re →
        z.re ≤ max completedPrimeContourTransportFamily.c
            (1 - completedPrimeContourTransportFamily.c) →
        ‖completedZetaNegLogDeriv z‖ *
            ‖zetaCompletedExplicitFormulaPhi
              (convolutionAutocorrelation f) (z - 1 / 2)‖
          ≤ C * (1 + ‖z.im‖) ^ (-(1 : ℤ)))
    (N : ℕ) :
    ‖zetaCompletedExplicitFormulaTopLineIntegral
        (convolutionAutocorrelation f)
        (completedPrimeContourTransportFamily.rectangle (N : ℝ))‖ ≤
      C * (1 + ‖(N : ℝ)‖) ^ (-(1 : ℤ)) *
        horizontalEdgeLength completedPrimeContourTransportFamily.c := by
  unfold zetaCompletedExplicitFormulaTopLineIntegral
  exact norm_setIntegral_uIcc_le_horizontalEdgeLength_mul
    (fun x : ℝ =>
      completedZetaNegLogDeriv
          (zetaCompletedExplicitFormulaTopPath
            (completedPrimeContourTransportFamily.rectangle (N : ℝ)) x) *
        zetaCompletedExplicitFormulaPhi
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormulaTopPath
            (completedPrimeContourTransportFamily.rectangle (N : ℝ)) x - 1 / 2))
    completedPrimeContourTransportFamily.c
    (C * (1 + ‖(N : ℝ)‖) ^ (-(1 : ℤ)))
    (fun x hx =>
      sampledTopHorizontalIntegrand_norm_le_productEnvelope
        f C hC N x hx)

/-- Product-form control bounds the bottom horizontal contour integral. -/
theorem sampledBottomHorizontalIntegral_norm_le_productEnvelope
    (f : ZetaAdmissibleFunction)
    (C : ℝ)
    (hC :
      ∀ z : ℂ,
        min completedPrimeContourTransportFamily.c
            (1 - completedPrimeContourTransportFamily.c) ≤ z.re →
        z.re ≤ max completedPrimeContourTransportFamily.c
            (1 - completedPrimeContourTransportFamily.c) →
        ‖completedZetaNegLogDeriv z‖ *
            ‖zetaCompletedExplicitFormulaPhi
              (convolutionAutocorrelation f) (z - 1 / 2)‖
          ≤ C * (1 + ‖z.im‖) ^ (-(1 : ℤ)))
    (N : ℕ) :
    ‖zetaCompletedExplicitFormulaBottomLineIntegral
        (convolutionAutocorrelation f)
        (completedPrimeContourTransportFamily.rectangle (N : ℝ))‖ ≤
      C * (1 + ‖(N : ℝ)‖) ^ (-(1 : ℤ)) *
        horizontalEdgeLength completedPrimeContourTransportFamily.c := by
  unfold zetaCompletedExplicitFormulaBottomLineIntegral
  exact norm_setIntegral_uIcc_le_horizontalEdgeLength_mul
    (fun x : ℝ =>
      completedZetaNegLogDeriv
          (zetaCompletedExplicitFormulaBottomPath
            (completedPrimeContourTransportFamily.rectangle (N : ℝ)) x) *
        zetaCompletedExplicitFormulaPhi
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormulaBottomPath
            (completedPrimeContourTransportFamily.rectangle (N : ℝ)) x - 1 / 2))
    completedPrimeContourTransportFamily.c
    (C * (1 + ‖(N : ℝ)‖) ^ (-(1 : ℤ)))
    (fun x hx =>
      sampledBottomHorizontalIntegrand_norm_le_productEnvelope
        f C hC N x hx)

/-- Product-form control bounds the top-minus-bottom sampled horizontal contour
difference. -/
theorem sampledHorizontalDifference_norm_le_twoEdgeProductEnvelope
    (f : ZetaAdmissibleFunction)
    (C : ℝ)
    (hC :
      ∀ z : ℂ,
        min completedPrimeContourTransportFamily.c
            (1 - completedPrimeContourTransportFamily.c) ≤ z.re →
        z.re ≤ max completedPrimeContourTransportFamily.c
            (1 - completedPrimeContourTransportFamily.c) →
        ‖completedZetaNegLogDeriv z‖ *
            ‖zetaCompletedExplicitFormulaPhi
              (convolutionAutocorrelation f) (z - 1 / 2)‖
          ≤ C * (1 + ‖z.im‖) ^ (-(1 : ℤ)))
    (N : ℕ) :
    ‖sampledHorizontalDifference N f‖ ≤
      sampledProductHorizontalEnvelope C 1 N := by
  let A : ℝ := C
  let B : ℝ := (1 + ‖(N : ℝ)‖) ^ (-(1 : ℤ))
  let L : ℝ := horizontalEdgeLength completedPrimeContourTransportFamily.c
  have htop :
      ‖zetaCompletedExplicitFormulaTopLineIntegral
          (convolutionAutocorrelation f)
          (completedPrimeContourTransportFamily.rectangle (N : ℝ))‖ ≤
        A * B * L := by
    exact sampledTopHorizontalIntegral_norm_le_productEnvelope f C hC N
  have hbottom :
      ‖zetaCompletedExplicitFormulaBottomLineIntegral
          (convolutionAutocorrelation f)
          (completedPrimeContourTransportFamily.rectangle (N : ℝ))‖ ≤
        A * B * L := by
    exact sampledBottomHorizontalIntegral_norm_le_productEnvelope f C hC N
  have hnorm :
      ‖sampledHorizontalDifference N f‖ ≤
        A * B * L + A * B * L := by
    have hcomplex :
        ‖sampledHorizontalDifferenceComplex N f‖ ≤
          A * B * L + A * B * L := by
      unfold sampledHorizontalDifferenceComplex
      exact (norm_sub_le
      (zetaCompletedExplicitFormulaTopLineIntegral
        (convolutionAutocorrelation f)
        (completedPrimeContourTransportFamily.rectangle (N : ℝ)))
      (zetaCompletedExplicitFormulaBottomLineIntegral
        (convolutionAutocorrelation f)
        (completedPrimeContourTransportFamily.rectangle (N : ℝ)))).trans
      (add_le_add htop hbottom)
    have hreal :
        ‖sampledHorizontalDifference N f‖ ≤
          ‖sampledHorizontalDifferenceComplex N f‖ := by
      unfold sampledHorizontalDifference
      exact Complex.abs_re_le_abs (sampledHorizontalDifferenceComplex N f)
    exact hreal.trans hcomplex
  have henvelope :
      A * B * L + A * B * L =
        sampledProductHorizontalEnvelope C 1 N := by
    unfold sampledProductHorizontalEnvelope
    unfold A
    unfold B
    unfold L
    exact two_horizontalEdgeEnvelope_eq_productEnvelope
      C
      ((1 + ‖(N : ℝ)‖) ^ (-(1 : ℤ)))
      (horizontalEdgeLength completedPrimeContourTransportFamily.c)
  exact hnorm.trans (le_of_eq henvelope)

/-- The sampled horizontal difference is bounded by the product-form horizontal envelope. -/
theorem sampledHorizontalDifference_norm_le_productEnvelope
    (f : ZetaAdmissibleFunction)
    (C : ℝ)
    (hC :
      ∀ z : ℂ,
        min completedPrimeContourTransportFamily.c
            (1 - completedPrimeContourTransportFamily.c) ≤ z.re →
        z.re ≤ max completedPrimeContourTransportFamily.c
            (1 - completedPrimeContourTransportFamily.c) →
        ‖completedZetaNegLogDeriv z‖ *
            ‖zetaCompletedExplicitFormulaPhi
              (convolutionAutocorrelation f) (z - 1 / 2)‖
          ≤ C * (1 + ‖z.im‖) ^ (-(1 : ℤ)))
    (N : ℕ) :
    ‖sampledHorizontalDifference N f‖ ≤
      sampledProductHorizontalEnvelope C 1 N := by
  exact sampledHorizontalDifference_norm_le_twoEdgeProductEnvelope f C hC N

/-- The product-form sampled horizontal envelope tends to zero. -/
theorem sampledProductHorizontalEnvelope_tendsto_zero
    (C : ℝ)
    (k : ℕ) :
    Tendsto
      (fun N : ℕ => sampledProductHorizontalEnvelope C k.succ N)
      atTop
      (𝓝 0) := by
  let L : ℝ := 2 * horizontalEdgeLength completedPrimeContourTransportFamily.c
  have hpowReal :
      Tendsto
        (fun T : ℝ => (1 + ‖T‖) ^ (-(k.succ : ℤ)))
        atTop
        (𝓝 (0 : ℝ)) :=
    tendsto_one_add_norm_pow_neg_atTop k
  have hpowNat :
      Tendsto
        (fun N : ℕ => (1 + ‖(N : ℝ)‖) ^ (-(k.succ : ℤ)))
        atTop
        (𝓝 (0 : ℝ)) :=
    hpowReal.comp tendsto_natCast_atTop_atTop
  have hscaled :
      Tendsto
        (fun N : ℕ => (C * L) * (1 + ‖(N : ℝ)‖) ^ (-(k.succ : ℤ)))
        atTop
        (𝓝 0) := by
    exact Eq.subst
      (motive := fun x : ℝ =>
        Tendsto
          (fun N : ℕ => (C * L) * (1 + ‖(N : ℝ)‖) ^ (-(k.succ : ℤ)))
          atTop
          (𝓝 x))
      (mul_zero (C * L))
      (hpowNat.const_mul (C * L))
  have hrewrite :
      (fun N : ℕ => sampledProductHorizontalEnvelope C k.succ N) =
        fun N : ℕ =>
          (C * L) * (1 + ‖(N : ℝ)‖) ^ (-(k.succ : ℤ)) := by
    funext N
    unfold sampledProductHorizontalEnvelope
    unfold L
    calc
      C *
          (1 + ‖(N : ℝ)‖) ^ (-(k.succ : ℤ)) *
          (2 * horizontalEdgeLength completedPrimeContourTransportFamily.c) =
          (C *
            (2 * horizontalEdgeLength completedPrimeContourTransportFamily.c)) *
            (1 + ‖(N : ℝ)‖) ^ (-(k.succ : ℤ)) := by
        let A : ℝ := C
        let B : ℝ := (1 + ‖(N : ℝ)‖) ^ (-(k.succ : ℤ))
        let D : ℝ := 2 * horizontalEdgeLength completedPrimeContourTransportFamily.c
        change A * B * D = (A * D) * B
        calc
          A * B * D = A * (B * D) := by
            exact mul_assoc A B D
          _ = A * (D * B) := by
            exact congrArg (fun x : ℝ => A * x) (mul_comm B D)
          _ = A * D * B := by
            exact (mul_assoc A D B).symm
  exact Eq.subst
    (motive := fun u : ℕ → ℝ => Tendsto u atTop (𝓝 0))
    hrewrite.symm
    hscaled

/-- Product-form horizontal control implies decay of the sampled horizontal difference. -/
theorem sampledHorizontalDifference_tendsto_zero_of_productHorizontalControl
    (f : ZetaAdmissibleFunction)
    (hcontrol : CompletedPrimeProductHorizontalControl f) :
    Tendsto
      (fun N : ℕ => sampledHorizontalDifference N f)
      atTop
      (𝓝 0) := by
  rcases exists_sampledProductHorizontalEnvelopeConstant f hcontrol 1 with
    ⟨C, _hCpos, hCbound⟩
  have hbound :
      ∀ N : ℕ,
        ‖sampledHorizontalDifference N f‖ ≤
          sampledProductHorizontalEnvelope C 1 N := by
    intro N
    exact sampledHorizontalDifference_norm_le_productEnvelope f C hCbound N
  have henvelope :
      Tendsto
        (fun N : ℕ => sampledProductHorizontalEnvelope C 1 N)
        atTop
        (𝓝 0) :=
    sampledProductHorizontalEnvelope_tendsto_zero C 0
  exact squeeze_zero_norm'
    (Eventually.of_forall hbound)
    henvelope

/-- Contour-residue tomography bounds the residual finite prime error, after subtracting
the horizontal contour sides, by the omitted coordinate-remainder majorant tail. -/
theorem finitePrimeContourTransportTomographicError_residueTailDomination
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    ‖finitePrimeContourTransportTomographicError N f‖ ≤
      ∑' ι : ZetaPrimePowerIndex,
        if ι ∈ ZetaPrimePowerIndex.window N then
          0
        else
          completedPrimeContourTransportCoordinateRemainderMajorant ι f := by
  have htail :
      finitePrimeContourTransportTomographicError N f =
        ∑' ι : ZetaPrimePowerIndex,
          if ι ∈ ZetaPrimePowerIndex.window N then
            0
          else
            completedPrimeContourTransportCoordinateRemainder ι f :=
    finitePrimeContourTransportTomographicError_eq_coordinateRemainderTail N f
  exact Eq.subst
    (motive := fun x : ℝ =>
      ‖x‖ ≤
        ∑' ι : ZetaPrimePowerIndex,
          if ι ∈ ZetaPrimePowerIndex.window N then
            0
          else
            completedPrimeContourTransportCoordinateRemainderMajorant ι f)
    htail.symm
    (norm_coordinateRemainderTail_le_coordinateRemainderMajorantTail N f)

/-- The residual is controlled by the coordinate-remainder tail majorant. -/
theorem finitePrimeContourTransportTomographicError_coordinateDomination
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    ‖finitePrimeContourTransportTomographicError N f‖ ≤
      ∑' ι : ZetaPrimePowerIndex,
        if ι ∈ ZetaPrimePowerIndex.window N then
          0
        else
          completedPrimeContourTransportCoordinateRemainderMajorant ι f := by
  exact finitePrimeContourTransportTomographicError_residueTailDomination N f

/-- The residual majorant is controlled by the coordinate-remainder tail majorant. -/
theorem finitePrimeContourTransportTomographicErrorMajorant_le_coordinateRemainderTail
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeContourTransportTomographicErrorMajorant N f ≤
      finitePrimeContourTransportTomographicCoordinateRemainderTailMajorant N f := by
  unfold finitePrimeContourTransportTomographicErrorMajorant
  unfold finitePrimeContourTransportTomographicCoordinateRemainderTailMajorant
  exact finitePrimeContourTransportTomographicError_coordinateDomination N f

/-- The spectral tail majorant controlling the finite prime tomographic residual tends to
zero. -/
theorem primeWindow_spectralTail_tendsto_zero_of_summable
    (f : ZetaAdmissibleFunction)
    (u : ZetaPrimePowerIndex → ℝ)
    (hsum : Summable u)
    (hnonneg : ∀ ι : ZetaPrimePowerIndex, 0 ≤ u ι)
    (hzero : ∀ ι : ZetaPrimePowerIndex, ¬ ZetaPrimePowerIndex.IsGenuine ι → u ι = 0) :
    Tendsto
      (fun N : ℕ =>
        ∑' ι : ZetaPrimePowerIndex,
          if ι ∈ ZetaPrimePowerIndex.window N then
            0
          else
            u ι)
      atTop
      (𝓝 0) := by
  have hwindow :
      Tendsto
        (fun N : ℕ => ∑ ι in ZetaPrimePowerIndex.window N, u ι)
        atTop
        (𝓝 (∑' ι : ZetaPrimePowerIndex, u ι)) :=
    ZetaPrimePowerIndex.tendsto_sum_window_tsum_of_summable u hsum hzero
  have htail_as_difference :
      (fun N : ℕ =>
        ∑' ι : ZetaPrimePowerIndex,
          if ι ∈ ZetaPrimePowerIndex.window N then
            0
          else
            u ι) =
        (fun N : ℕ =>
          (∑' ι : ZetaPrimePowerIndex, u ι) -
            ∑ ι in ZetaPrimePowerIndex.window N, u ι) := by
    funext N
    exact ZetaPrimePowerIndex.spectralTail_eq_tsum_sub_windowSum u hsum N
  have hdifference :
      Tendsto
        (fun N : ℕ =>
          (∑' ι : ZetaPrimePowerIndex, u ι) -
            ∑ ι in ZetaPrimePowerIndex.window N, u ι)
        atTop
        (𝓝 ((∑' ι : ZetaPrimePowerIndex, u ι) -
          (∑' ι : ZetaPrimePowerIndex, u ι))) := by
    exact tendsto_const_nhds.sub hwindow
  have hzero_target :
      (∑' ι : ZetaPrimePowerIndex, u ι) -
          (∑' ι : ZetaPrimePowerIndex, u ι) =
        0 := by
    exact sub_self (∑' ι : ZetaPrimePowerIndex, u ι)
  have htail :
      Tendsto
        (fun N : ℕ =>
          (∑' ι : ZetaPrimePowerIndex, u ι) -
            ∑ ι in ZetaPrimePowerIndex.window N, u ι)
        atTop
        (𝓝 0) :=
    Eq.subst
      (motive := fun x : ℝ =>
        Tendsto
          (fun N : ℕ =>
            (∑' ι : ZetaPrimePowerIndex, u ι) -
              ∑ ι in ZetaPrimePowerIndex.window N, u ι)
          atTop
          (𝓝 x))
      hzero_target
      hdifference
  exact Eq.subst
    (motive := fun v : ℕ → ℝ => Tendsto v atTop (𝓝 0))
    htail_as_difference.symm
    htail

/-- Nongenuine indices have zero contour-transport coordinate remainder. -/
theorem completedPrimeContourTransportCoordinateRemainder_eq_zero_of_not_isGenuine
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction)
    (hι : ¬ ZetaPrimePowerIndex.IsGenuine ι) :
    completedPrimeContourTransportCoordinateRemainder ι f = 0 := by
  have hcontour :
      completedPrimeContourRealizedTimeDistributionCoordinate
          ι (convolutionAutocorrelation f) = 0 :=
    completedPrimeContourRealizedTimeDistributionCoordinate_eq_zero_of_not_isGenuine
      ι f hι
  have htime :
      completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f) = 0 := by
    have hphysical :
        completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f) =
          zetaPrimeOffDiagonalCoordinate ι f :=
      completedPrimeTimeDistributionCoordinate_convolutionAutocorrelation_eq_physical ι f
    exact hphysical.trans
      (zetaPrimeOffDiagonalCoordinate_eq_zero_of_not_isGenuine ι f hι)
  unfold completedPrimeContourTransportCoordinateRemainder
  exact congrArg₂ Sub.sub hcontour htime

/-- Nongenuine indices have zero coordinate-remainder majorant. -/
theorem completedPrimeContourTransportCoordinateRemainderMajorant_eq_zero_of_not_isGenuine
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction)
    (hι : ¬ ZetaPrimePowerIndex.IsGenuine ι) :
    completedPrimeContourTransportCoordinateRemainderMajorant ι f = 0 := by
  unfold completedPrimeContourTransportCoordinateRemainderMajorant
  exact congrArg norm
    (completedPrimeContourTransportCoordinateRemainder_eq_zero_of_not_isGenuine ι f hι)

/-- The coordinate-remainder tail majorant controlling the finite prime tomographic residual
tends to zero. -/
theorem finitePrimeContourTransportTomographicCoordinateRemainderTailMajorant_tendsto_zero_of_summable
    (f : ZetaAdmissibleFunction)
    (hsum :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          completedPrimeContourTransportCoordinateRemainderMajorant ι f)) :
    Tendsto
      (fun N : ℕ =>
        finitePrimeContourTransportTomographicCoordinateRemainderTailMajorant N f)
      atTop
      (𝓝 0) := by
  unfold finitePrimeContourTransportTomographicCoordinateRemainderTailMajorant
  exact primeWindow_spectralTail_tendsto_zero_of_summable
    f
    (fun ι : ZetaPrimePowerIndex =>
      completedPrimeContourTransportCoordinateRemainderMajorant ι f)
    hsum
    (fun ι : ZetaPrimePowerIndex =>
      completedPrimeContourTransportCoordinateRemainderMajorant_nonnegative ι f)
    (fun ι hι =>
      completedPrimeContourTransportCoordinateRemainderMajorant_eq_zero_of_not_isGenuine
        ι f hι)

/-- The coordinate-remainder tail majorant controlling the finite prime tomographic residual
tends to zero. -/
theorem finitePrimeContourTransportTomographicCoordinateRemainderTailMajorant_tendsto_zero
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ =>
        finitePrimeContourTransportTomographicCoordinateRemainderTailMajorant N f)
      atTop
      (𝓝 0) := by
  exact
    finitePrimeContourTransportTomographicCoordinateRemainderTailMajorant_tendsto_zero_of_summable
      f
      (summable_completedPrimeContourTransportCoordinateRemainderMajorant f)

/-- The finite prime tomographic residual majorant tends to zero. -/
theorem finitePrimeContourTransportTomographicErrorMajorant_tendsto_zero
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ => finitePrimeContourTransportTomographicErrorMajorant N f)
      atTop
      (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (finitePrimeContourTransportTomographicCoordinateRemainderTailMajorant_tendsto_zero f)
    ?_ ?_
  · exact Eventually.of_forall
      (fun N => norm_nonneg (finitePrimeContourTransportTomographicError N f))
  · exact Eventually.of_forall
      (fun N =>
        finitePrimeContourTransportTomographicErrorMajorant_le_coordinateRemainderTail N f)

/-- The residual finite prime tomography error tends to zero. -/
theorem finitePrimeContourTransportTomographicError_tendsto_zero
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ => finitePrimeContourTransportTomographicError N f)
      atTop
      (𝓝 0) := by
  exact squeeze_zero_norm'
    (Eventually.of_forall
      (fun N =>
        norm_finitePrimeContourTransportTomographicError_le_majorant N f))
    (finitePrimeContourTransportTomographicErrorMajorant_tendsto_zero f)

/-- The sampled horizontal top-minus-bottom contour remainder tends to zero along the
prime-window height parameter. -/
theorem sampledHorizontalDifference_tendsto_zero_ownerHorizontalDecay
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ => sampledHorizontalDifference N f)
      atTop
      (𝓝 0) := by
  have hcontrol : CompletedPrimeProductHorizontalControl f :=
    completedPrimeProductHorizontalControl_of_autocorrelation f
  exact sampledHorizontalDifference_tendsto_zero_of_productHorizontalControl f hcontrol

/-- Owner horizontal-decay theorem for the finite prime contour-transport remainder.

The finite contour-transport remainder tends to zero after the horizontal sides of the
completed contour shift have been discharged.  This is the analytic input that drives prime
tomography; tomography must not be used to prove it. -/
theorem finitePrimeContourTransportRemainder_tendsto_zero_ownerHorizontalDecay
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ => finitePrimeContourTransportRemainder N f)
      atTop
      (𝓝 0) := by
  have hsampled :
      Tendsto
        (fun N : ℕ => sampledHorizontalDifference N f)
        atTop
        (𝓝 0) :=
    sampledHorizontalDifference_tendsto_zero_ownerHorizontalDecay f
  have herror :
      Tendsto
        (fun N : ℕ => finitePrimeContourTransportTomographicError N f)
        atTop
        (𝓝 0) :=
    finitePrimeContourTransportTomographicError_tendsto_zero f
  have hsum :
      Tendsto
        (fun N : ℕ =>
          sampledHorizontalDifference N f +
            finitePrimeContourTransportTomographicError N f)
        atTop
        (𝓝 (0 + 0)) :=
    hsampled.add herror
  have hfunctions :
      (fun N : ℕ => finitePrimeContourTransportRemainder N f) =
        (fun N : ℕ =>
          sampledHorizontalDifference N f +
            finitePrimeContourTransportTomographicError N f) := by
    funext N
    exact finitePrimeContourTransportRemainder_eq_sampledHorizontalDifference_add_error N f
  have htarget :
      Tendsto
        (fun N : ℕ =>
          sampledHorizontalDifference N f +
            finitePrimeContourTransportTomographicError N f)
        atTop
        (𝓝 0) :=
    Eq.subst
      (motive := fun x : ℝ =>
        Tendsto
          (fun N : ℕ =>
            sampledHorizontalDifference N f +
              finitePrimeContourTransportTomographicError N f)
          atTop
          (𝓝 x))
      (add_zero 0)
      hsum
  exact Eq.subst
    (motive := fun u : ℕ → ℝ =>
      Tendsto u atTop (𝓝 0))
    hfunctions.symm
    htarget

/-- Owner horizontal-decay consequence for the completed prime contour transport.

Since the finite contour-transport remainder tends both to the completed boundary
difference and, by horizontal decay, to zero, the completed boundary difference is zero. -/
theorem completedPrimeContourTransportBoundaryDifference_eq_zero_ownerHorizontalDecay
    (f : ZetaAdmissibleFunction) :
    completedPrimeContourTransportBoundaryDifference f = 0 := by
  have hboundary :
      Tendsto
        (fun N : ℕ => finitePrimeContourTransportRemainder N f)
        atTop
        (𝓝 (completedPrimeContourTransportBoundaryDifference f)) :=
    finitePrimeContourTransportRemainder_tendsto_boundaryDifference f
  have hzero :
      Tendsto
        (fun N : ℕ => finitePrimeContourTransportRemainder N f)
        atTop
        (𝓝 0) :=
    finitePrimeContourTransportRemainder_tendsto_zero_ownerHorizontalDecay f
  exact tendsto_nhds_unique hboundary hzero

/-- Completed horizontal-decay transport identifies the time-side prime distribution with
the contour-realized prime distribution. -/
theorem completedPrimeTimeDistributionPairing_eq_contourRealizedPrimeChannel_ownerHorizontalDecay
    (f : ZetaAdmissibleFunction) :
    completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) =
      completedPrimeContourRealizedTimeDistributionPairing
        (convolutionAutocorrelation f) := by
  have hzero :
      completedPrimeContourTransportBoundaryDifference f = 0 :=
    completedPrimeContourTransportBoundaryDifference_eq_zero_ownerHorizontalDecay f
  unfold completedPrimeContourTransportBoundaryDifference at hzero
  let C : ℝ :=
    completedPrimeContourRealizedTimeDistributionPairing
      (convolutionAutocorrelation f)
  let T : ℝ :=
    completedPrimeTimeDistributionPairing (convolutionAutocorrelation f)
  change C - T = 0 at hzero
  change T = C
  have hadd :
      T + (C - T) = C := by
    calc
      T + (C - T) = T + (C + -T) := by
        exact congrArg (fun x : ℝ => T + x) (sub_eq_add_neg C T)
      _ = (T + C) + -T := by
        exact (add_assoc T C (-T)).symm
      _ = (C + T) + -T := by
        exact congrArg (fun x : ℝ => x + -T) (add_comm T C)
      _ = C + (T + -T) := by
        exact add_assoc C T (-T)
      _ = C + 0 := by
        exact congrArg (fun x : ℝ => C + x) (add_right_neg T)
      _ = C := by
        exact add_zero C
  calc
    T = T + 0 := by
      exact (add_zero T).symm
    _ = T + (C - T) := by
      exact congrArg (fun x : ℝ => T + x) hzero.symm
    _ = C := by
      exact hadd

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
