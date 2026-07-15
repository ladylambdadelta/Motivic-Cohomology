import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedPositiveNatReindex
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedFarNegativeGap

/-!
# Residual-enhanced far-negative gap

At the floor-defined lower frequency endpoint there is a nonnegative residual
between angular frequency and logarithmic slope.  Moving one integer farther
into the negative ray adds exactly `2π`.  Retaining this residual converts the
full left-inactive gap into the same affine shifted form used on the positive
ray.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseFarNegativeResidualGap
    (t : ℝ) (a : ℤ) : ℝ :=
  2 * Real.pi *
      (-(Complex.logarithmicPhasePoissonModeRangeLower t a : ℝ)) -
    ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a

theorem Complex.logarithmicPhaseFarNegativeResidualGap_nonneg
    (t : ℝ) (a : ℤ) (ha : 1 ≤ a) :
    0 ≤ Complex.logarithmicPhaseFarNegativeResidualGap t a := by
  unfold Complex.logarithmicPhaseFarNegativeResidualGap
  exact sub_nonneg.mpr
    (Complex.modeRangeLower_quantitative_baseline t a ha)

theorem Complex.logarithmicPhaseLeftInactiveGap_eq_residual_add_distance
    (t : ℝ) (a m : ℤ) :
    Complex.logarithmicPhaseLeftInactiveGap t m
        (Complex.logarithmicPhaseQuantitativeSupportLeft a) =
      Complex.logarithmicPhaseFarNegativeResidualGap t a +
        2 * Real.pi *
          (Complex.logarithmicPhaseFarNegativeDistance t a m : ℝ) := by
  unfold Complex.logarithmicPhaseLeftInactiveGap
  unfold Complex.logarithmicPhaseFarNegativeResidualGap
  have hangular := Complex.farNegative_angular_decomposition t a m
  have hsubAdd :
      (2 * Real.pi *
          (-(Complex.logarithmicPhasePoissonModeRangeLower t a : ℝ)) +
        2 * Real.pi *
          (Complex.logarithmicPhaseFarNegativeDistance t a m : ℝ)) -
          ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a =
        (2 * Real.pi *
          (-(Complex.logarithmicPhasePoissonModeRangeLower t a : ℝ)) -
          ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a) +
        2 * Real.pi *
          (Complex.logarithmicPhaseFarNegativeDistance t a m : ℝ) := by
    exact Eq.trans
      (sub_eq_add_neg _ _)
      (Eq.trans
        (add_assoc _ _ _)
        (Eq.trans
          (congrArg (fun value : ℝ =>
            2 * Real.pi *
              (-(Complex.logarithmicPhasePoissonModeRangeLower t a : ℝ)) +
              value)
            (add_comm
              (2 * Real.pi *
                (Complex.logarithmicPhaseFarNegativeDistance t a m : ℝ))
              (-(‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a))))
          (Eq.trans
            (add_assoc _ _ _).symm
            (congrArg
              (fun value : ℝ => value +
                2 * Real.pi *
                  (Complex.logarithmicPhaseFarNegativeDistance t a m : ℝ))
              (sub_eq_add_neg _ _).symm))))
  exact Eq.trans
    (congrArg
      (fun angular : ℝ =>
        angular - ‖t‖ /
          Complex.logarithmicPhaseQuantitativeSupportLeft a)
      hangular)
    hsubAdd

def Complex.logarithmicPhaseFarNegativeEquivNat
    (t : ℝ) (a : ℤ) :
    Complex.logarithmicPhasePoissonFarNegativeModes t a ≃ ℕ :=
  (Complex.logarithmicPhaseFarNegativeEquivPositive t a).trans
    Complex.logarithmicPhasePositiveIntegerEquivNat

theorem Complex.logarithmicPhaseFarNegativeEquivNat_apply_distance
    (t : ℝ) (a : ℤ)
    (m : Complex.logarithmicPhasePoissonFarNegativeModes t a) :
    Complex.logarithmicPhaseFarNegativeEquivNat t a m =
      Complex.logarithmicPhasePositiveIntegerEquivNat
        (Complex.logarithmicPhaseFarNegativeEquivPositive t a m) := by
  exact rfl

theorem Complex.logarithmicPhaseFarNegativeEquivNat_symm_distance
    (t : ℝ) (a : ℤ) (n : ℕ) :
    Complex.logarithmicPhaseFarNegativeDistance t a
        ((Complex.logarithmicPhaseFarNegativeEquivNat t a).symm n) =
      (((Complex.logarithmicPhasePositiveIntegerEquivNat).symm n :
        Complex.logarithmicPhasePoissonPositiveTailModes) : ℤ) := by
  have hfarPositive :
      Complex.logarithmicPhaseFarNegativeEquivPositive t a
          ((Complex.logarithmicPhaseFarNegativeEquivNat t a).symm n) =
        (Complex.logarithmicPhasePositiveIntegerEquivNat).symm n := by
    exact (Complex.logarithmicPhaseFarNegativeEquivPositive t a).apply_symm_apply
      ((Complex.logarithmicPhasePositiveIntegerEquivNat).symm n)
  have hcoe := congrArg
    (fun value : Complex.logarithmicPhasePoissonPositiveTailModes =>
      (value : ℤ)) hfarPositive
  exact Eq.trans
    (Complex.logarithmicPhaseFarNegativeEquivPositive_apply_coe
      t a ((Complex.logarithmicPhaseFarNegativeEquivNat t a).symm n)).symm
    hcoe

theorem Complex.logarithmicPhaseFarNegativeEquivNat_symm_distance_real
    (t : ℝ) (a : ℤ) (n : ℕ) :
    (Complex.logarithmicPhaseFarNegativeDistance t a
      ((Complex.logarithmicPhaseFarNegativeEquivNat t a).symm n) : ℝ) =
      (n : ℝ) + 1 := by
  have hdistance :=
    Complex.logarithmicPhaseFarNegativeEquivNat_symm_distance t a n
  have hcast := congrArg (fun value : ℤ => (value : ℝ)) hdistance
  have hpositive :=
    Complex.logarithmicPhasePositiveIntegerEquivNat_symm_real_value n
  exact Eq.trans hcast hpositive

theorem Complex.logarithmicPhaseFarNegativeGap_eq_affine
    (t : ℝ) (a : ℤ) (n : ℕ) :
    Complex.logarithmicPhaseLeftInactiveGap t
        ((Complex.logarithmicPhaseFarNegativeEquivNat t a).symm n : ℤ)
        (Complex.logarithmicPhaseQuantitativeSupportLeft a) =
      Complex.logarithmicPhaseFarNegativeResidualGap t a +
        Complex.logarithmicPhaseAngularStep * ((n : ℝ) + 1) := by
  have hdecompose :=
    Complex.logarithmicPhaseLeftInactiveGap_eq_residual_add_distance
      t a ((Complex.logarithmicPhaseFarNegativeEquivNat t a).symm n : ℤ)
  have hdistance :=
    Complex.logarithmicPhaseFarNegativeEquivNat_symm_distance_real t a n
  unfold Complex.logarithmicPhaseAngularStep
  exact Eq.trans hdecompose
    (congrArg
      (fun distance : ℝ =>
        Complex.logarithmicPhaseFarNegativeResidualGap t a +
          2 * Real.pi * distance)
      hdistance)

theorem Complex.enhancedFarNegative_inverseSquare_eq_shiftedTerm
    (t : ℝ) (a : ℤ) (n : ℕ) :
    1 / (Complex.logarithmicPhaseLeftInactiveGap t
      ((Complex.logarithmicPhaseFarNegativeEquivNat t a).symm n : ℤ)
      (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 2 =
      Real.shiftedInverseSquareTerm
        (Complex.logarithmicPhaseFarNegativeResidualGap t a)
        Complex.logarithmicPhaseAngularStep n := by
  unfold Real.shiftedInverseSquareTerm
  exact congrArg (fun gap : ℝ => 1 / gap ^ 2)
    (Complex.logarithmicPhaseFarNegativeGap_eq_affine t a n)

theorem Complex.enhancedFarNegative_inverseCube_eq_shiftedTerm
    (t : ℝ) (a : ℤ) (n : ℕ) :
    1 / (Complex.logarithmicPhaseLeftInactiveGap t
      ((Complex.logarithmicPhaseFarNegativeEquivNat t a).symm n : ℤ)
      (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 3 =
      Real.shiftedInverseCubeTerm
        (Complex.logarithmicPhaseFarNegativeResidualGap t a)
        Complex.logarithmicPhaseAngularStep n := by
  unfold Real.shiftedInverseCubeTerm
  exact congrArg (fun gap : ℝ => 1 / gap ^ 3)
    (Complex.logarithmicPhaseFarNegativeGap_eq_affine t a n)

theorem Complex.enhancedFarNegative_inverseFourth_eq_shiftedTerm
    (t : ℝ) (a : ℤ) (n : ℕ) :
    1 / (Complex.logarithmicPhaseLeftInactiveGap t
      ((Complex.logarithmicPhaseFarNegativeEquivNat t a).symm n : ℤ)
      (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 4 =
      Real.shiftedInverseFourthTerm
        (Complex.logarithmicPhaseFarNegativeResidualGap t a)
        Complex.logarithmicPhaseAngularStep n := by
  unfold Real.shiftedInverseFourthTerm
  exact congrArg (fun gap : ℝ => 1 / gap ^ 4)
    (Complex.logarithmicPhaseFarNegativeGap_eq_affine t a n)

theorem Complex.tsum_farNegative_comp_equivNat
    (t : ℝ) (a : ℤ)
    (f : Complex.logarithmicPhasePoissonFarNegativeModes t a → ℝ) :
    (∑' m : Complex.logarithmicPhasePoissonFarNegativeModes t a, f m) =
      ∑' n : ℕ, f ((Complex.logarithmicPhaseFarNegativeEquivNat t a).symm n) := by
  let e := Complex.logarithmicPhaseFarNegativeEquivNat t a
  let g : ℕ → ℝ := fun n : ℕ => f (e.symm n)
  have hpointwise :
      ∀ m : Complex.logarithmicPhasePoissonFarNegativeModes t a,
        f m = g (e m) :=
    fun m =>
      congrArg f (e.symm_apply_apply m).symm
  have hleft :
      (∑' m : Complex.logarithmicPhasePoissonFarNegativeModes t a, f m) =
        ∑' m : Complex.logarithmicPhasePoissonFarNegativeModes t a, g (e m) :=
    tsum_congr hpointwise
  have hreindex :
      (∑' m : Complex.logarithmicPhasePoissonFarNegativeModes t a, g (e m)) =
        ∑' n : ℕ, g n :=
    e.tsum_eq g
  exact Eq.trans hleft hreindex

theorem Complex.tsum_farNegative_inverseSquare_eq_shifted
    (t : ℝ) (a : ℤ) :
    (∑' m : Complex.logarithmicPhasePoissonFarNegativeModes t a,
      1 / (Complex.logarithmicPhaseLeftInactiveGap t m
        (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 2) =
      ∑' n : ℕ, Real.shiftedInverseSquareTerm
        (Complex.logarithmicPhaseFarNegativeResidualGap t a)
        Complex.logarithmicPhaseAngularStep n := by
  have hreindex := Complex.tsum_farNegative_comp_equivNat t a
    (fun m : Complex.logarithmicPhasePoissonFarNegativeModes t a =>
      1 / (Complex.logarithmicPhaseLeftInactiveGap t m
        (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 2)
  have hterms := tsum_congr
    (fun n => Complex.enhancedFarNegative_inverseSquare_eq_shiftedTerm t a n)
  exact Eq.trans hreindex hterms

theorem Complex.tsum_farNegative_inverseCube_eq_shifted
    (t : ℝ) (a : ℤ) :
    (∑' m : Complex.logarithmicPhasePoissonFarNegativeModes t a,
      1 / (Complex.logarithmicPhaseLeftInactiveGap t m
        (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 3) =
      ∑' n : ℕ, Real.shiftedInverseCubeTerm
        (Complex.logarithmicPhaseFarNegativeResidualGap t a)
        Complex.logarithmicPhaseAngularStep n := by
  have hreindex := Complex.tsum_farNegative_comp_equivNat t a
    (fun m : Complex.logarithmicPhasePoissonFarNegativeModes t a =>
      1 / (Complex.logarithmicPhaseLeftInactiveGap t m
        (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 3)
  have hterms := tsum_congr
    (fun n => Complex.enhancedFarNegative_inverseCube_eq_shiftedTerm t a n)
  exact Eq.trans hreindex hterms

theorem Complex.tsum_farNegative_inverseFourth_eq_shifted
    (t : ℝ) (a : ℤ) :
    (∑' m : Complex.logarithmicPhasePoissonFarNegativeModes t a,
      1 / (Complex.logarithmicPhaseLeftInactiveGap t m
        (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 4) =
      ∑' n : ℕ, Real.shiftedInverseFourthTerm
        (Complex.logarithmicPhaseFarNegativeResidualGap t a)
        Complex.logarithmicPhaseAngularStep n := by
  have hreindex := Complex.tsum_farNegative_comp_equivNat t a
    (fun m : Complex.logarithmicPhasePoissonFarNegativeModes t a =>
      1 / (Complex.logarithmicPhaseLeftInactiveGap t m
        (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 4)
  have hterms := tsum_congr
    (fun n => Complex.enhancedFarNegative_inverseFourth_eq_shiftedTerm t a n)
  exact Eq.trans hreindex hterms

end
end LFunctions
end Boundary
