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

/-- The time-side completed prime coordinate family at an autocorrelation probe. -/
def completedPrimeTimeCoordinateFamily
    (f : ZetaAdmissibleFunction) : ZetaPrimePowerIndex → ℝ :=
  fun ι : ZetaPrimePowerIndex =>
    completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f)

/-- The contour-realized completed prime coordinate family at an autocorrelation probe. -/
def completedPrimeContourRealizedCoordinateFamily
    (f : ZetaAdmissibleFunction) : ZetaPrimePowerIndex → ℝ :=
  fun ι : ZetaPrimePowerIndex =>
    completedPrimeContourRealizedTimeDistributionCoordinate
      ι (convolutionAutocorrelation f)

/-- The completed prime contour-transport coordinate-remainder family at an
autocorrelation probe. -/
def completedPrimeContourRemainderCoordinateFamily
    (f : ZetaAdmissibleFunction) : ZetaPrimePowerIndex → ℝ :=
  completedPrimeContourTransportCoordinateRemainderFamily f

/-- Horizontal-decay compatibility wrapper for time-side prime-coordinate summability. -/
theorem summable_completedPrimeTimeDistributionCoordinate_convolutionAutocorrelation_ownerHorizontalDecay
    (f : ZetaAdmissibleFunction) :
    Summable (completedPrimeTimeCoordinateFamily f) := by
  exact summable_completedPrimeTimeDistributionCoordinate_convolutionAutocorrelation f

/-- Horizontal-decay compatibility wrapper for nongenuine contour-realized coordinates. -/
theorem completedPrimeContourRealizedTimeDistributionCoordinate_eq_zero_of_not_isGenuine_ownerHorizontalDecay
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction)
    (hι : ¬ ZetaPrimePowerIndex.IsGenuine ι) :
    completedPrimeContourRealizedTimeDistributionCoordinate
      ι (convolutionAutocorrelation f) = 0 := by
  exact completedPrimeContourRealizedTimeDistributionCoordinate_eq_zero_of_not_isGenuine
    ι (convolutionAutocorrelation f) hι

/-- A contour-realized prime coordinate is the physical time coordinate plus the
contour-transport remainder. -/
theorem completedPrimeContourRealizedTimeDistributionCoordinate_eq_remainder_add_time
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    completedPrimeContourRealizedTimeDistributionCoordinate
        ι (convolutionAutocorrelation f) =
      completedPrimeContourTransportCoordinateRemainder ι f +
        completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f) := by
  have hsub :
      completedPrimeContourTransportCoordinateRemainder ι f =
        completedPrimeContourRealizedTimeDistributionCoordinate
            ι (convolutionAutocorrelation f) -
          completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f) :=
    completedPrimeContourTransportCoordinateRemainder_eq_contour_sub_time ι f
  calc
    completedPrimeContourRealizedTimeDistributionCoordinate
        ι (convolutionAutocorrelation f) =
        (completedPrimeContourRealizedTimeDistributionCoordinate
            ι (convolutionAutocorrelation f) -
          completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f)) +
          completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f) := by
      exact (sub_add_cancel
        (completedPrimeContourRealizedTimeDistributionCoordinate
          ι (convolutionAutocorrelation f))
        (completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f))).symm
    _ =
        completedPrimeContourTransportCoordinateRemainder ι f +
          completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f) := by
      exact congrArg
        (fun x : ℝ =>
          x + completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f))
        hsub.symm

/-- The coordinate-remainder family is the pointwise difference between the contour-realized
prime coordinate family and the time-side prime coordinate family. -/
theorem completedPrimeContourTransportCoordinateRemainderFamily_eq_contour_sub_time_family
    (f : ZetaAdmissibleFunction) :
    completedPrimeContourTransportCoordinateRemainderFamily f =
      fun ι : ZetaPrimePowerIndex =>
        completedPrimeContourRealizedCoordinateFamily f ι -
          completedPrimeTimeCoordinateFamily f ι := by
  funext ι
  exact completedPrimeContourTransportCoordinateRemainder_eq_contour_sub_time ι f

/-- A real coordinate family is summable when its norm is bounded by a summable nonnegative
majorant. -/
theorem summable_real_family_of_norm_le_majorant
    (u v : ZetaPrimePowerIndex → ℝ)
    (hv : Summable v)
    (hv_nonneg : ∀ ι : ZetaPrimePowerIndex, 0 ≤ v ι)
    (hbound : ∀ ι : ZetaPrimePowerIndex, ‖u ι‖ ≤ v ι) :
    Summable u := by
  exact Summable.of_norm_bounded v hv hbound

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

/-- Nongenuine indices have zero contour-transport coordinate remainder. -/
theorem completedPrimeContourTransportCoordinateRemainder_eq_zero_of_not_isGenuine
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction)
    (hι : ¬ ZetaPrimePowerIndex.IsGenuine ι) :
    completedPrimeContourTransportCoordinateRemainder ι f = 0 := by
  have hcontour :
    completedPrimeContourRealizedTimeDistributionCoordinate
          ι (convolutionAutocorrelation f) = 0 :=
    completedPrimeContourRealizedTimeDistributionCoordinate_eq_zero_of_not_isGenuine_ownerHorizontalDecay
      ι f hι
  have htime :
      completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f) = 0 := by
    have hphysical :
        completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f) =
          zetaPrimeOffDiagonalCoordinate ι f :=
      completedPrimeTimeDistributionCoordinate_convolutionAutocorrelation_eq_physical ι f
    exact hphysical.trans
      (zetaPrimeOffDiagonalCoordinate_eq_zero_of_not_isGenuine ι f hι)
  have hsub :
      completedPrimeContourTransportCoordinateRemainder ι f =
        completedPrimeContourRealizedTimeDistributionCoordinate
            ι (convolutionAutocorrelation f) -
          completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f) :=
    completedPrimeContourTransportCoordinateRemainder_eq_contour_sub_time ι f
  have hzeros :
      completedPrimeContourRealizedTimeDistributionCoordinate
            ι (convolutionAutocorrelation f) -
          completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f) =
        0 - 0 :=
    congrArg₂ Sub.sub hcontour htime
  exact hsub.trans (hzeros.trans (sub_self 0))

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

/-- The completed finite-window/GNS contour realization identifies the raw spectral
contour scalar. -/
theorem completedPrimeContourFiniteWindowGNSRealization_rawSpectral
    (f : ZetaAdmissibleFunction) :
    completedPrimeContourRealizedFiniteWindowPairing f =
      completedPrimeContourRealizedTimeDistributionPairing
        (convolutionAutocorrelation f) := by
  exact
    (completedPrimeFiniteWindowGNSContourRealization_identifies_rawSpectral_and_tail_tendsto
      f).left

/-- The completed finite-window/GNS contour realization kills the omitted coordinate tail. -/
theorem completedPrimeContourFiniteWindowGNSRealization_tail_tendsto_zero
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ => completedPrimeContourTransportCoordinateRemainderTail N f)
      atTop
      (𝓝 0) := by
  exact
    (completedPrimeFiniteWindowGNSContourRealization_identifies_rawSpectral_and_tail_tendsto
      f).right

/-- The omitted coordinate-remainder tail tends to zero in the completed horizontal
realization.

This compatibility wrapper consumes the split tail theorem
`finitePrimeHorizontalResidueCoordinateShadow_window_sub_residueShadow_tendsto_zero`.
It is not a consequence of sampled-horizontal edge decay alone: the sampled horizontal
term controls the visible edge contribution, while this theorem controls the omitted
completed tail. -/
theorem completedPrimeContourTransportCoordinateRemainderTail_tendsto_zero_ownerTailLocalization
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ => completedPrimeContourTransportCoordinateRemainderTail N f)
      atTop
      (𝓝 0) := by
  exact completedPrimeContourTransportCoordinateRemainderTail_tendsto_zero f

/-- The omitted coordinate-remainder tail tends to zero in the completed horizontal
realization.

This compatibility wrapper exposes the tail-localization theorem under the horizontal
decay owner name consumed by the finite-window transport proof. -/
theorem completedPrimeContourTransportCoordinateRemainderTail_tendsto_zero_ownerHorizontalDecay
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ => completedPrimeContourTransportCoordinateRemainderTail N f)
      atTop
      (𝓝 0) := by
  exact
    completedPrimeContourTransportCoordinateRemainderTail_tendsto_zero_ownerTailLocalization
      f

/-- Owner horizontal-decay theorem for the finite prime coordinate-remainder window.

The coordinate-remainder window is the sampled horizontal term plus the omitted
coordinate-remainder tail.  The sampled horizontal term decays by product-form horizontal
control; the tail is the remaining completed two-face/GNS tail-localization input. -/
theorem finitePrimeContourTransportCoordinateRemainderWindow_tendsto_zero_ownerHorizontalDecay
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ => finitePrimeContourTransportCoordinateRemainderWindow N f)
      atTop
      (𝓝 0) := by
  have hsampled :
      Tendsto
        (fun N : ℕ => sampledHorizontalDifference N f)
        atTop
        (𝓝 0) :=
    sampledHorizontalDifference_tendsto_zero_ownerHorizontalDecay f
  have htail :
      Tendsto
        (fun N : ℕ => completedPrimeContourTransportCoordinateRemainderTail N f)
        atTop
        (𝓝 0) :=
    completedPrimeContourTransportCoordinateRemainderTail_tendsto_zero_ownerHorizontalDecay
      f
  have hsum :
      Tendsto
        (fun N : ℕ =>
          sampledHorizontalDifference N f +
            completedPrimeContourTransportCoordinateRemainderTail N f)
        atTop
        (𝓝 (0 + 0)) :=
    hsampled.add htail
  have hzero : (0 : ℝ) + 0 = 0 :=
    add_zero 0
  have hwindow :
      (fun N : ℕ => finitePrimeContourTransportCoordinateRemainderWindow N f) =
        (fun N : ℕ =>
          sampledHorizontalDifference N f +
            completedPrimeContourTransportCoordinateRemainderTail N f) := by
    funext N
    exact
      (sampledHorizontalDifference_add_coordinateRemainderTail_eq_coordinateRemainderWindow
        N f).symm
  exact Eq.subst
    (motive := fun u : ℕ → ℝ => Tendsto u atTop (𝓝 0))
    hwindow.symm
    (Eq.subst
      (motive := fun x : ℝ =>
        Tendsto
          (fun N : ℕ =>
            sampledHorizontalDifference N f +
              completedPrimeContourTransportCoordinateRemainderTail N f)
          atTop
          (𝓝 x))
      hzero
      hsum)

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
  have hwindow :
      Tendsto
        (fun N : ℕ => finitePrimeContourTransportCoordinateRemainderWindow N f)
        atTop
        (𝓝 0) :=
    finitePrimeContourTransportCoordinateRemainderWindow_tendsto_zero_ownerHorizontalDecay f
  have hrem :
      (fun N : ℕ => finitePrimeContourTransportRemainder N f) =
        (fun N : ℕ => finitePrimeContourTransportCoordinateRemainderWindow N f) := by
    funext N
    exact finitePrimeContourTransportRemainder_eq_coordinateRemainderWindow N f
  exact Eq.subst
    (motive := fun u : ℕ → ℝ => Tendsto u atTop (𝓝 0))
    hrem.symm
    hwindow

/-- Owner horizontal-decay theorem for the residual finite prime tomography error.

The residual error is the finite contour-transport remainder after subtracting the sampled
horizontal difference.  Both terms tend to zero: the first by the finite transport
remainder theorem, the second by product-form horizontal control. -/
theorem finitePrimeContourTransportTomographicError_tendsto_zero_ownerHorizontalDecay
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ => finitePrimeContourTransportTomographicError N f)
      atTop
      (𝓝 0) := by
  have hremainder :
      Tendsto
        (fun N : ℕ => finitePrimeContourTransportRemainder N f)
        atTop
        (𝓝 0) :=
    finitePrimeContourTransportRemainder_tendsto_zero_ownerHorizontalDecay f
  have hsampled :
      Tendsto
        (fun N : ℕ => sampledHorizontalDifference N f)
        atTop
        (𝓝 0) :=
    sampledHorizontalDifference_tendsto_zero_ownerHorizontalDecay f
  have hdiff :
      Tendsto
        (fun N : ℕ =>
          finitePrimeContourTransportRemainder N f -
            sampledHorizontalDifference N f)
        atTop
        (𝓝 (0 - 0)) :=
    hremainder.sub hsampled
  have hzero : (0 : ℝ) - 0 = 0 :=
    sub_self 0
  have herror :
      (fun N : ℕ => finitePrimeContourTransportTomographicError N f) =
        (fun N : ℕ =>
          finitePrimeContourTransportRemainder N f -
            sampledHorizontalDifference N f) := by
    funext N
    exact finitePrimeContourTransportTomographicError_eq_remainder_sub_sampled N f
  exact Eq.subst
    (motive := fun u : ℕ → ℝ =>
      Tendsto u atTop (𝓝 0))
    herror.symm
    (Eq.subst
      (motive := fun x : ℝ =>
        Tendsto
          (fun N : ℕ =>
            finitePrimeContourTransportRemainder N f -
              sampledHorizontalDifference N f)
          atTop
          (𝓝 x))
      hzero
      hdiff)

/-- The residual finite prime tomography error tends to zero. -/
theorem finitePrimeContourTransportTomographicError_tendsto_zero
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ => finitePrimeContourTransportTomographicError N f)
      atTop
      (𝓝 0) := by
  exact finitePrimeContourTransportTomographicError_tendsto_zero_ownerHorizontalDecay f

/-- Finite contour-realized prime windows converge to the completed time-side prime
distribution after horizontal contour transport.

This is the honest completed-window convergence available from horizontal decay: the finite
contour-realized window is the finite time-side window plus the finite transport remainder,
and the transport remainder tends to zero.  It does not use real-axis spectral-coordinate
summability. -/
theorem finitePrimeContourRealizedTimeDistributionWindow_tendsto_timeDistributionPairing_ownerHorizontalDecay
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ =>
        finitePrimeContourRealizedTimeDistributionWindow N
          (convolutionAutocorrelation f))
      atTop
      (𝓝 (completedPrimeTimeDistributionPairing (convolutionAutocorrelation f))) := by
  let T : ℝ :=
    completedPrimeTimeDistributionPairing (convolutionAutocorrelation f)
  have htime :
      Tendsto
        (fun N : ℕ =>
          finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f))
        atTop
        (𝓝 T) :=
    finitePrimeTimeDistributionWindow_tendsto_completed f
  have hremainder :
      Tendsto
        (fun N : ℕ => finitePrimeContourTransportRemainder N f)
        atTop
        (𝓝 0) :=
    finitePrimeContourTransportRemainder_tendsto_zero_ownerHorizontalDecay f
  have hsum :
      Tendsto
        (fun N : ℕ =>
          finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) +
            finitePrimeContourTransportRemainder N f)
        atTop
        (𝓝 (T + 0)) :=
    htime.add hremainder
  have htarget : T + 0 = T :=
    add_zero T
  have hshiftedLimit :
      Tendsto
        (fun N : ℕ =>
          finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) +
            finitePrimeContourTransportRemainder N f)
        atTop
        (𝓝 T) :=
    Eq.subst
      (motive := fun x : ℝ =>
        Tendsto
          (fun N : ℕ =>
            finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) +
              finitePrimeContourTransportRemainder N f)
          atTop
          (𝓝 x))
      htarget
      hsum
  have hwindow :
      (fun N : ℕ =>
        finitePrimeContourRealizedTimeDistributionWindow N
          (convolutionAutocorrelation f)) =
        (fun N : ℕ =>
          finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) +
            finitePrimeContourTransportRemainder N f) := by
    funext N
    have hcoordinate :
        finitePrimeContourRealizedTimeDistributionWindow N
            (convolutionAutocorrelation f) =
          finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) +
            finitePrimeContourTransportCoordinateRemainderWindow N f :=
      finitePrimeContourRealizedTimeDistributionWindow_eq_timeWindow_add_coordinateRemainderWindow
        N f
    have hremainder :
        finitePrimeContourTransportCoordinateRemainderWindow N f =
          finitePrimeContourTransportRemainder N f :=
      (finitePrimeContourTransportRemainder_eq_coordinateRemainderWindow N f).symm
    exact hcoordinate.trans
      (congrArg
        (fun x : ℝ =>
          finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) + x)
        hremainder)
  exact Eq.subst
    (motive := fun u : ℕ → ℝ => Tendsto u atTop (𝓝 T))
    hwindow.symm
    hshiftedLimit

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
