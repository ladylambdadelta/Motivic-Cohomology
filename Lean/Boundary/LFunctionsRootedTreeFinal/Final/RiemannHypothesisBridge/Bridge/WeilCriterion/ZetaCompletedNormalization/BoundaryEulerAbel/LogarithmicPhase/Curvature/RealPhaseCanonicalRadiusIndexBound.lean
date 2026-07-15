import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseNegativeModeIndex
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.CanonicalSharpStationaryPacket

/-!
# Canonical stationary radius in mode coordinates

The canonical radius is the square root of the stationary center.  For a
negative mode it is bounded by `sqrt ‖t‖ / sqrt (natAbs m)`, and hence by the
global scale divided by the same mode square root.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Real.one_le_two_pi :
    (1 : ℝ) ≤ 2 * Real.pi :=
  Real.logarithmicPhase_one_le_two_pi

theorem Real.modeIndex_le_twoPi_mul_modeIndex
    {k : ℕ} :
    (k : ℝ) ≤ 2 * Real.pi * (k : ℝ) := by
  have hk := Nat.cast_nonneg k
  have hmul := mul_le_mul_of_nonneg_right Real.one_le_two_pi hk
  exact Eq.subst (motive := fun value : ℝ => value ≤ 2 * Real.pi * (k : ℝ))
    (one_mul (k : ℝ)).symm hmul

theorem Real.norm_div_twoPiIndex_le_norm_div_index
    (t : ℝ) {k : ℕ} (hk : 0 < k) :
    ‖t‖ / (2 * Real.pi * (k : ℝ)) ≤ ‖t‖ / (k : ℝ) := by
  have hkPos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hdenom := Real.modeIndex_le_twoPi_mul_modeIndex (k := k)
  exact div_le_div_of_nonneg_left (norm_nonneg t) hkPos hdenom

theorem Complex.logarithmicPhase_stationaryCenter_le_norm_div_modeIndex
    (t : ℝ) (ht : 1 ≤ ‖t‖) {m : ℤ} (hm : m < 0) :
    Complex.logarithmicPhaseFourierStationaryPoint t m ≤
      ‖t‖ / (Complex.logarithmicPhaseNegativeModeIndex m : ℝ) := by
  have hcenter :=
    Complex.logarithmicPhase_stationaryCenter_eq_norm_div_modeIndex t ht hm
  have hindexPos := Complex.logarithmicPhaseNegativeModeIndex_pos hm
  exact Eq.subst (motive := fun value : ℝ => value ≤ _)
    hcenter.symm
    (Real.norm_div_twoPiIndex_le_norm_div_index t hindexPos)

theorem Real.sqrt_norm_div_nat_eq
    (t : ℝ) {k : ℕ} (hk : 0 < k) :
    Real.sqrt (‖t‖ / (k : ℝ)) =
      Real.sqrt ‖t‖ / Real.sqrt (k : ℝ) := by
  exact Real.sqrt_div (norm_nonneg t) (k : ℝ)

theorem Complex.logarithmicPhaseCanonicalRadius_le_sqrtNorm_div_sqrtIndex
    (t : ℝ) (ht : 1 ≤ ‖t‖) {m : ℤ} (hm : m < 0) :
    Complex.logarithmicPhasePoissonCanonicalRadius t m ≤
      Real.sqrt ‖t‖ /
        Real.sqrt (Complex.logarithmicPhaseNegativeModeIndex m : ℝ) := by
  unfold Complex.logarithmicPhasePoissonCanonicalRadius
  have hcenter :=
    Complex.logarithmicPhase_stationaryCenter_le_norm_div_modeIndex t ht hm
  have hsqrt := Real.sqrt_le_sqrt hcenter
  have hindexPos := Complex.logarithmicPhaseNegativeModeIndex_pos hm
  exact le_trans hsqrt
    (le_of_eq (Real.sqrt_norm_div_nat_eq t hindexPos))

theorem Real.sqrt_norm_le_BProcessScale
    (t : ℝ) :
    Real.sqrt ‖t‖ ≤ Complex.logarithmicPhaseBProcessScale t := by
  unfold Complex.logarithmicPhaseBProcessScale
  exact Real.sqrt_le_sqrt (le_add_of_nonneg_left zero_le_one)

theorem Complex.logarithmicPhaseCanonicalRadius_le_scale_div_sqrtIndex
    (t : ℝ) (ht : 1 ≤ ‖t‖) {m : ℤ} (hm : m < 0) :
    Complex.logarithmicPhasePoissonCanonicalRadius t m ≤
      Complex.logarithmicPhaseBProcessScale t /
        Real.sqrt (Complex.logarithmicPhaseNegativeModeIndex m : ℝ) := by
  have hbase :=
    Complex.logarithmicPhaseCanonicalRadius_le_sqrtNorm_div_sqrtIndex
      t ht hm
  have hdenomNonneg :=
    Real.sqrt_nonneg (Complex.logarithmicPhaseNegativeModeIndex m : ℝ)
  have hdivision := div_le_div_of_nonneg_right
    (Real.sqrt_norm_le_BProcessScale t) hdenomNonneg
  exact le_trans hbase hdivision

theorem Real.scale_div_sqrtIndex_eq_scale_mul_invSqrt
    (t : ℝ) (k : ℕ) :
    Complex.logarithmicPhaseBProcessScale t / Real.sqrt (k : ℝ) =
      Complex.logarithmicPhaseBProcessScale t *
        (Real.sqrt (k : ℝ))⁻¹ :=
  div_eq_mul_inv _ _

theorem Complex.logarithmicPhaseCanonicalRadius_le_scale_mul_invSqrtIndex
    (t : ℝ) (ht : 1 ≤ ‖t‖) {m : ℤ} (hm : m < 0) :
    Complex.logarithmicPhasePoissonCanonicalRadius t m ≤
      Complex.logarithmicPhaseBProcessScale t *
        (Real.sqrt (Complex.logarithmicPhaseNegativeModeIndex m : ℝ))⁻¹ := by
  have hbound :=
    Complex.logarithmicPhaseCanonicalRadius_le_scale_div_sqrtIndex t ht hm
  exact le_trans hbound
    (le_of_eq
      (Real.scale_div_sqrtIndex_eq_scale_mul_invSqrt
        t (Complex.logarithmicPhaseNegativeModeIndex m)))

theorem Complex.sum_canonicalRadii_le_scale_mul_invSqrtSum
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    (M : Finset ℤ)
    (hM : ∀ m ∈ M, m < 0) :
    (∑ m ∈ M, Complex.logarithmicPhasePoissonCanonicalRadius t m) ≤
      ∑ m ∈ M,
        Complex.logarithmicPhaseBProcessScale t *
          (Real.sqrt (Complex.logarithmicPhaseNegativeModeIndex m : ℝ))⁻¹ := by
  exact Finset.sum_le_sum (fun m hm =>
    Complex.logarithmicPhaseCanonicalRadius_le_scale_mul_invSqrtIndex
      t ht (hM m hm))

theorem Complex.sum_canonicalRadii_le_scale_mul_two_sqrt
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    (M : Finset ℤ) (N : ℕ)
    (hMneg : ∀ m ∈ M, m < 0)
    (hMupper : ∀ m ∈ M,
      Complex.logarithmicPhaseNegativeModeIndex m ≤ N) :
    (∑ m ∈ M, Complex.logarithmicPhasePoissonCanonicalRadius t m) ≤
      Complex.logarithmicPhaseBProcessScale t *
        (2 * Real.sqrt (N : ℝ)) := by
  have hpoint := Complex.sum_canonicalRadii_le_scale_mul_invSqrtSum
    t ht M hMneg
  have hfactor :
      (∑ m ∈ M,
        Complex.logarithmicPhaseBProcessScale t *
          (Real.sqrt (Complex.logarithmicPhaseNegativeModeIndex m : ℝ))⁻¹) =
        Complex.logarithmicPhaseBProcessScale t *
          (∑ m ∈ M,
            (Real.sqrt
              (Complex.logarithmicPhaseNegativeModeIndex m : ℝ))⁻¹) := by
    exact (Finset.mul_sum M
      (fun m : ℤ =>
        (Real.sqrt (Complex.logarithmicPhaseNegativeModeIndex m : ℝ))⁻¹)
      (Complex.logarithmicPhaseBProcessScale t)).symm
  have hsum := Complex.sum_negativeMode_invSqrt_le_two_sqrt
    M N hMneg hMupper
  have hscaled := mul_le_mul_of_nonneg_left hsum
    (Complex.logarithmicPhaseBProcessScale_nonneg t)
  exact le_trans hpoint
    (Eq.subst (motive := fun value : ℝ => value ≤ _)
      hfactor.symm hscaled)

end

end LFunctions
end Boundary
