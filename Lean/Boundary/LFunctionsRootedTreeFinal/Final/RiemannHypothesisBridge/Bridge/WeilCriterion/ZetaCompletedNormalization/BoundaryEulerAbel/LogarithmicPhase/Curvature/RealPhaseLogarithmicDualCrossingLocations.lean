import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicDualShiftGeometry

/-!
# Explicit principal crossings of dual logarithmic shifts

For positive `h` and a positive integer level `q`, the absolute derivative of
the dual shifted phase meets `2*pi*q` when

`x*(x+h) = ‖t‖*h/(2*pi*q)`.

The positive solution is

`(sqrt (h^2 + 4*‖t‖*h/(2*pi*q)) - h)/2`.

This owner records the quadratic algebra, positivity, exact crossing equation,
and order of these crossing locations.  It replaces abstract crossing
witnesses by a canonical formula owned by the logarithmic phase.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Real.positiveQuadraticRoot
    (h D : ℝ) : ℝ :=
  (Real.sqrt (h ^ 2 + 4 * D) - h) / 2

def Complex.logarithmicPhaseDualCrossingScale
    (t h : ℝ) (q : ℕ) : ℝ :=
  ‖t‖ * h / (2 * Real.pi * (q : ℝ))

def Complex.logarithmicPhaseDualCrossingLocation
    (t h : ℝ) (q : ℕ) : ℝ :=
  Real.positiveQuadraticRoot h
    (Complex.logarithmicPhaseDualCrossingScale t h q)

theorem Real.four_pos : (0 : ℝ) < 4 := by
  exact OfNat.zero_lt_ofNat

theorem Real.two_ne_zero : (2 : ℝ) ≠ 0 := by
  exact ne_of_gt zero_lt_two

theorem Real.sq_add_four_mul_pos
    {h D : ℝ} (hD : 0 < D) :
    0 < h ^ 2 + 4 * D := by
  have hsquare := sq_nonneg h
  have hfourD := mul_pos Real.four_pos hD
  exact add_pos_of_nonneg_of_pos hsquare hfourD

theorem Real.h_sq_lt_h_sq_add_four_mul
    {h D : ℝ} (hD : 0 < D) :
    h ^ 2 < h ^ 2 + 4 * D := by
  exact lt_add_of_pos_right _ (mul_pos Real.four_pos hD)

theorem Real.sqrt_sq_lt_sqrt_sq_add_four_mul
    {h D : ℝ} (hh : 0 ≤ h) (hD : 0 < D) :
    h < Real.sqrt (h ^ 2 + 4 * D) := by
  have hradicand := Real.h_sq_lt_h_sq_add_four_mul hD
  have hsqrtStrict := Real.sqrt_lt_sqrt hradicand
  have hsqrtSq : Real.sqrt (h ^ 2) = h := by
    exact Eq.trans (Real.sqrt_sq_eq_abs h) (abs_of_nonneg hh)
  exact Eq.subst (motive := fun z : ℝ => z < _)
    hsqrtSq.symm hsqrtStrict

theorem Real.positiveQuadraticRoot_pos
    {h D : ℝ} (hh : 0 ≤ h) (hD : 0 < D) :
    0 < Real.positiveQuadraticRoot h D := by
  unfold Real.positiveQuadraticRoot
  have hnumerator : 0 < Real.sqrt (h ^ 2 + 4 * D) - h :=
    sub_pos.mpr (Real.sqrt_sq_lt_sqrt_sq_add_four_mul hh hD)
  exact div_pos hnumerator zero_lt_two

theorem Real.two_mul_positiveQuadraticRoot
    (h D : ℝ) :
    2 * Real.positiveQuadraticRoot h D =
      Real.sqrt (h ^ 2 + 4 * D) - h := by
  unfold Real.positiveQuadraticRoot
  exact mul_div_cancel_left₀
    (Real.sqrt (h ^ 2 + 4 * D) - h) Real.two_ne_zero

theorem Real.two_mul_positiveQuadraticRoot_add_h
    (h D : ℝ) :
    2 * Real.positiveQuadraticRoot h D + h =
      Real.sqrt (h ^ 2 + 4 * D) := by
  have hdouble := Real.two_mul_positiveQuadraticRoot h D
  exact Eq.trans (congrArg (fun z : ℝ => z + h) hdouble)
    (sub_add_cancel _ h)

theorem Real.square_two_mul_root_add_h
    {h D : ℝ} (hD : 0 ≤ D) :
    (2 * Real.positiveQuadraticRoot h D + h) ^ 2 =
      h ^ 2 + 4 * D := by
  have hradicand : 0 ≤ h ^ 2 + 4 * D :=
    add_nonneg (sq_nonneg h) (mul_nonneg (le_of_lt Real.four_pos) hD)
  have hsqrtSq := Real.sq_sqrt hradicand
  exact Eq.trans
    (congrArg (fun z : ℝ => z ^ 2)
      (Real.two_mul_positiveQuadraticRoot_add_h h D))
    hsqrtSq

theorem Real.two_root_add_h_sq_expand
    (r h : ℝ) :
    (2 * r + h) ^ 2 = 4 * (r * (r + h)) + h ^ 2 := by
  calc
    (2 * r + h) ^ 2 =
        (2 * r + h) * (2 * r + h) := pow_two _
    _ = (2 * r) * (2 * r) + (2 * r) * h +
          (h * (2 * r) + h * h) := by
            exact Eq.trans
              (add_mul (2 * r) h (2 * r + h))
              (congrArg₂ (fun x y : ℝ => x + y)
                (mul_add (2 * r) (2 * r) h)
                (mul_add h (2 * r) h))
    _ = 4 * (r * r) + 4 * (r * h) + h ^ 2 := by
      exact congrArg₂ (fun x y : ℝ => x + y)
        (Eq.trans
          (add_assoc ((2 * r) * (2 * r)) ((2 * r) * h) (h * (2 * r)))
          (congrArg₂ (fun x y : ℝ => x + y)
            (Eq.trans
              (mul_assoc 2 r (2 * r)).symm
              (Eq.trans
                (congrArg (fun z : ℝ => z * r) (mul_assoc 2 2 r))
                (congrArg (fun z : ℝ => z * (r * r)) (show (2 : ℝ) * 2 = 4 from rfl))))
            (Eq.trans
              (add_comm ((2 * r) * h) (h * (2 * r)))
              (Eq.trans
                (congrArg₂ (fun x y : ℝ => x + y)
                  (Eq.trans (mul_assoc h 2 r).symm
                    (congrArg (fun z : ℝ => z * r) (mul_comm h 2)))
                  rfl)
                (Eq.trans
                  (two_mul (2 * (r * h))).symm
                  (Eq.trans
                    (mul_assoc 2 2 (r * h)).symm
                    (congrArg (fun z : ℝ => z * (r * h))
                      (show (2 : ℝ) * 2 = 4 from rfl))))))))
        (pow_two h).symm
    _ = 4 * (r * (r + h)) + h ^ 2 := by
      exact congrArg (fun z : ℝ => z + h ^ 2)
        (Eq.trans
          (mul_add 4 (r * r) (r * h)).symm
          (congrArg (fun z : ℝ => 4 * z)
            (Eq.trans (mul_add r r h) rfl)))

theorem Real.positiveQuadraticRoot_mul_add
    {h D : ℝ} (hD : 0 ≤ D) :
    Real.positiveQuadraticRoot h D *
        (Real.positiveQuadraticRoot h D + h) = D := by
  let r := Real.positiveQuadraticRoot h D
  have hsquare := Real.square_two_mul_root_add_h hD
  have hexpand := Real.two_root_add_h_sq_expand r h
  have hfour :
      4 * (r * (r + h)) + h ^ 2 = h ^ 2 + 4 * D :=
    Eq.trans hexpand.symm hsquare
  have hcancel : 4 * (r * (r + h)) = 4 * D := by
    exact add_left_cancel
      (Eq.trans
        (add_comm (h ^ 2) (4 * (r * (r + h))))
        (Eq.trans hfour (add_comm (h ^ 2) (4 * D)).symm))
  have hfourNe : (4 : ℝ) ≠ 0 := ne_of_gt Real.four_pos
  exact (mul_left_cancel₀ hfourNe hcancel)

theorem Complex.logarithmicPhaseDualCrossingScale_pos
    (t : ℝ) (ht : 1 ≤ ‖t‖) {h : ℝ} (hh : 0 < h)
    {q : ℕ} (hq : 0 < q) :
    0 < Complex.logarithmicPhaseDualCrossingScale t h q := by
  unfold Complex.logarithmicPhaseDualCrossingScale
  have hnorm : 0 < ‖t‖ := lt_of_lt_of_le zero_lt_one ht
  have hnumerator := mul_pos hnorm hh
  have hqReal : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq
  have hdenom := mul_pos Complex.two_mul_pi_pos hqReal
  exact div_pos hnumerator hdenom

theorem Complex.logarithmicPhaseDualCrossingLocation_pos
    (t : ℝ) (ht : 1 ≤ ‖t‖) {h : ℝ} (hh : 0 < h)
    {q : ℕ} (hq : 0 < q) :
    0 < Complex.logarithmicPhaseDualCrossingLocation t h q := by
  unfold Complex.logarithmicPhaseDualCrossingLocation
  exact Real.positiveQuadraticRoot_pos (le_of_lt hh)
    (Complex.logarithmicPhaseDualCrossingScale_pos t ht hh hq)

theorem Complex.logarithmicPhaseDualCrossingLocation_quadratic
    (t h : ℝ) {q : ℕ} (hq : 0 < q) :
    Complex.logarithmicPhaseDualCrossingLocation t h q *
        (Complex.logarithmicPhaseDualCrossingLocation t h q + h) =
      Complex.logarithmicPhaseDualCrossingScale t h q := by
  unfold Complex.logarithmicPhaseDualCrossingLocation
  exact Real.positiveQuadraticRoot_mul_add
    (div_nonneg
      (mul_nonneg (norm_nonneg t) (le_of_lt (Nat.cast_pos.mpr hq)))
      (mul_nonneg (le_of_lt Complex.two_mul_pi_pos) (Nat.cast_nonneg q)))

theorem Complex.logarithmicPhaseDualCrossingLocation_derivative_abs_eq_level
    (t : ℝ) (ht : 1 ≤ ‖t‖) {h : ℝ} (hh : 0 < h)
    {q : ℕ} (hq : 0 < q) :
    |Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h
        (Complex.logarithmicPhaseDualCrossingLocation t h q)| =
      2 * Real.pi * (q : ℝ) := by
  have hx :=
    Complex.logarithmicPhaseDualCrossingLocation_pos t ht hh hq
  have habs :=
    Complex.logarithmicPhaseDualShiftedDifferenceDerivative_abs_eq
      t (le_of_lt hh) hx
  have hquad :=
    Complex.logarithmicPhaseDualCrossingLocation_quadratic t h hq
  have hqReal : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq
  have hangular : 0 < 2 * Real.pi * (q : ℝ) :=
    mul_pos Complex.two_mul_pi_pos hqReal
  have hnormh : 0 < ‖t‖ * h :=
    mul_pos (lt_of_lt_of_le zero_lt_one ht) hh
  unfold Complex.logarithmicPhaseDualCrossingScale at hquad
  exact Eq.trans habs
    (Eq.trans
      (congrArg (fun denominator : ℝ => ‖t‖ * h / denominator) hquad)
      (div_div_cancel₀ (‖t‖ * h) (2 * Real.pi * (q : ℝ))
        (ne_of_gt hnormh) (ne_of_gt hangular)))

theorem Complex.logarithmicPhaseDualCrossingScale_antitone
    (t : ℝ) {h : ℝ} (hh : 0 ≤ h)
    {q₁ q₂ : ℕ} (hq₁ : 0 < q₁) (hqq : q₁ ≤ q₂) :
    Complex.logarithmicPhaseDualCrossingScale t h q₂ ≤
      Complex.logarithmicPhaseDualCrossingScale t h q₁ := by
  unfold Complex.logarithmicPhaseDualCrossingScale
  have hnumerator := mul_nonneg (norm_nonneg t) hh
  have hq₁Real : (0 : ℝ) < (q₁ : ℝ) := Nat.cast_pos.mpr hq₁
  have hdenom₁ : 0 < 2 * Real.pi * (q₁ : ℝ) :=
    mul_pos Complex.two_mul_pi_pos hq₁Real
  have hdenom := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hqq)
    (le_of_lt Complex.two_mul_pi_pos)
  exact div_le_div_of_nonneg_left hnumerator hdenom₁ hdenom

theorem Real.positiveQuadraticRoot_mono_D
    (h : ℝ) {D₁ D₂ : ℝ} (hD : D₁ ≤ D₂) :
    Real.positiveQuadraticRoot h D₁ ≤
      Real.positiveQuadraticRoot h D₂ := by
  unfold Real.positiveQuadraticRoot
  have hradicand := add_le_add_left
    (mul_le_mul_of_nonneg_left hD (le_of_lt Real.four_pos)) (h ^ 2)
  have hsqrt := Real.sqrt_le_sqrt hradicand
  have hsub := sub_le_sub_right hsqrt h
  exact div_le_div_of_nonneg_right hsub (le_of_lt zero_lt_two)

theorem Complex.logarithmicPhaseDualCrossingLocation_antitone_level
    (t : ℝ) {h : ℝ} (hh : 0 ≤ h)
    {q₁ q₂ : ℕ} (hq₁ : 0 < q₁) (hqq : q₁ ≤ q₂) :
    Complex.logarithmicPhaseDualCrossingLocation t h q₂ ≤
      Complex.logarithmicPhaseDualCrossingLocation t h q₁ := by
  unfold Complex.logarithmicPhaseDualCrossingLocation
  exact Real.positiveQuadraticRoot_mono_D h
    (Complex.logarithmicPhaseDualCrossingScale_antitone t hh hq₁ hqq)

end

end LFunctions
end Boundary
