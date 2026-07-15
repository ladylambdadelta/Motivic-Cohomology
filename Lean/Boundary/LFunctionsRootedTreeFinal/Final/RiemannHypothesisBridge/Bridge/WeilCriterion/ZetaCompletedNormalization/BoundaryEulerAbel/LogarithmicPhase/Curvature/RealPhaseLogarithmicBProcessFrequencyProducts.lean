import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicBProcessTermBounds

/-!
# Frequency-cardinality products for the balanced B-process

This owner proves the four cancellation estimates contributed by the genuine
frequency-length part of the mode cardinality.  The reciprocal-tail products
cancel `‖t‖`; the central product reduces to `‖t‖ / S`; and the crossing
product reduces to `‖t‖ / a`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

private theorem realOfNat_mul_eq_of_nat_eq
    (a b c : ℕ) (h : a * b = c) :
    (a : ℝ) * (b : ℝ) = (c : ℝ) :=
  Eq.trans (Nat.cast_mul a b).symm
    (congrArg (fun value : ℕ => (value : ℝ)) h)

private theorem real_three_mul_two_eq_six :
    (3 : ℝ) * 2 = 6 := by
  have hthree : ((3 : ℕ) : ℝ) = 3 := Nat.cast_ofNat
  have htwo : ((2 : ℕ) : ℝ) = 2 := Nat.cast_ofNat
  have hsix : ((6 : ℕ) : ℝ) = 6 := Nat.cast_ofNat
  exact Eq.trans
    (congrArg₂ (fun left right : ℝ => left * right)
      hthree.symm htwo.symm)
    (Eq.trans (realOfNat_mul_eq_of_nat_eq 3 2 6 rfl) hsix)

private theorem real_six_mul_two_eq_twelve :
    (6 : ℝ) * 2 = 12 := by
  have hsix : ((6 : ℕ) : ℝ) = 6 := Nat.cast_ofNat
  have htwo : ((2 : ℕ) : ℝ) = 2 := Nat.cast_ofNat
  have htwelve : ((12 : ℕ) : ℝ) = 12 := Nat.cast_ofNat
  exact Eq.trans
    (congrArg₂ (fun left right : ℝ => left * right)
      hsix.symm htwo.symm)
    (Eq.trans (realOfNat_mul_eq_of_nat_eq 6 2 12 rfl) htwelve)

theorem Real.div_mul_div_eq_mul_div_mul
    (a b c d : ℝ) :
    (a / b) * (c / d) = (a * c) / (b * d) := by
  calc
    (a / b) * (c / d) = ((a / b) * c) / d :=
      (mul_div_assoc (a / b) c d).symm
    _ = (a * c) / (b * d) :=
      Real.div_mul_div_reassociate a b c d

theorem Real.longGeometry_b_div_a_le_two
    {t : ℝ} {a b : ℕ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    (b : ℝ) / (a : ℝ) ≤ 2 := by
  have haPos : 0 < (a : ℝ) :=
    Nat.cast_pos.mpr
      (Real.logarithmicPhaseLongBranchGeometry_zero_lt_a hgeometry)
  have hba := Real.natCast_blockRight_le_two_mul_blockLeft
    (Real.logarithmicPhaseLongBranchGeometry_comparable hgeometry)
  exact (div_le_iff₀ haPos).mpr hba

theorem Real.three_mul_norm_div_a_mul_four_thirds_eq
    (norm a : ℝ) :
    (3 * (norm / a)) * (4 / 3) = 4 * (norm / a) := by
  have hthreePos : (0 : ℝ) < 3 :=
    Nat.cast_pos.mpr (Nat.succ_pos 2)
  have hthreeNe : (3 : ℝ) ≠ 0 := ne_of_gt hthreePos
  have hthreeMulFourDivThree :
      (3 : ℝ) * (4 / 3) = 4 := by
    calc
      (3 : ℝ) * (4 / 3) = (3 * 4) / 3 :=
        (mul_div_assoc 3 4 3).symm
      _ = 4 := mul_div_cancel_left₀ 4 hthreeNe
  calc
    (3 * (norm / a)) * (4 / 3) =
        (norm / a) * (3 * (4 / 3)) := by
      calc
        (3 * (norm / a)) * (4 / 3) =
            3 * ((norm / a) * (4 / 3)) :=
          mul_assoc 3 (norm / a) (4 / 3)
        _ = 3 * ((4 / 3) * (norm / a)) := by
          exact congrArg (fun value : ℝ => 3 * value)
            (mul_comm (norm / a) (4 / 3))
        _ = (3 * (4 / 3)) * (norm / a) :=
          (mul_assoc 3 (4 / 3) (norm / a)).symm
        _ = (norm / a) * (3 * (4 / 3)) :=
          mul_comm _ _
    _ = (norm / a) * 4 := by
      exact congrArg (fun value : ℝ => (norm / a) * value)
        hthreeMulFourDivThree
    _ = 4 * (norm / a) := mul_comm _ _

theorem Real.three_norm_div_a_mul_two_b_scale_div_norm_eq
    (norm a b scale : ℝ)
    (hnorm : norm ≠ 0)
    (ha : a ≠ 0) :
    (3 * (norm / a)) * (2 * (b * scale / norm)) =
      6 * ((b / a) * scale) := by
  have hcancel :
      (norm / a) * (b * scale / norm) = (b / a) * scale := by
    calc
      (norm / a) * (b * scale / norm) =
          (norm * a⁻¹) * ((b * scale) * norm⁻¹) := by
        exact congrArg₂ (fun left right : ℝ => left * right)
          (div_eq_mul_inv norm a)
          (div_eq_mul_inv (b * scale) norm)
      _ = (norm * norm⁻¹) * (a⁻¹ * (b * scale)) := by
        calc
          (norm * a⁻¹) * ((b * scale) * norm⁻¹) =
              norm * (a⁻¹ * ((b * scale) * norm⁻¹)) :=
            mul_assoc norm a⁻¹ ((b * scale) * norm⁻¹)
          _ = norm * ((a⁻¹ * (b * scale)) * norm⁻¹) := by
            exact congrArg (fun value : ℝ => norm * value)
              (mul_assoc a⁻¹ (b * scale) norm⁻¹).symm
          _ = norm * (norm⁻¹ * (a⁻¹ * (b * scale))) := by
            exact congrArg (fun value : ℝ => norm * value)
              (mul_comm (a⁻¹ * (b * scale)) norm⁻¹)
          _ = (norm * norm⁻¹) * (a⁻¹ * (b * scale)) :=
            (mul_assoc norm norm⁻¹ (a⁻¹ * (b * scale))).symm
      _ = 1 * (a⁻¹ * (b * scale)) := by
        exact congrArg (fun value : ℝ => value * (a⁻¹ * (b * scale)))
          (mul_inv_cancel₀ hnorm)
      _ = a⁻¹ * (b * scale) := one_mul _
      _ = (b * a⁻¹) * scale := by
        calc
          a⁻¹ * (b * scale) = (a⁻¹ * b) * scale :=
            (mul_assoc a⁻¹ b scale).symm
          _ = (b * a⁻¹) * scale :=
            congrArg (fun value : ℝ => value * scale)
              (mul_comm a⁻¹ b)
      _ = (b / a) * scale := by
        exact congrArg (fun value : ℝ => value * scale)
          (div_eq_mul_inv b a).symm
  calc
    (3 * (norm / a)) * (2 * (b * scale / norm)) =
        (3 * 2) * ((norm / a) * (b * scale / norm)) := by
      exact mul_mul_mul_comm 3 (norm / a) 2 (b * scale / norm)
    _ = 6 * ((norm / a) * (b * scale / norm)) := by
      exact congrArg
        (fun value : ℝ => value * ((norm / a) * (b * scale / norm)))
        real_three_mul_two_eq_six
    _ = 6 * ((b / a) * scale) :=
      congrArg (fun value : ℝ => 6 * value) hcancel

theorem Real.three_norm_div_a_mul_two_b_div_scale_eq
    (norm a b scale : ℝ) :
    (3 * (norm / a)) * (2 * (b / scale)) =
      6 * ((b / a) * (norm / scale)) := by
  calc
    (3 * (norm / a)) * (2 * (b / scale)) =
        (3 * 2) * ((norm / a) * (b / scale)) := by
      exact mul_mul_mul_comm 3 (norm / a) 2 (b / scale)
    _ = 6 * ((norm / a) * (b / scale)) := by
      exact congrArg
        (fun value : ℝ => value * ((norm / a) * (b / scale)))
        real_three_mul_two_eq_six
    _ = 6 * ((b / a) * (norm / scale)) := by
      exact congrArg (fun value : ℝ => 6 * value)
        (calc
          (norm / a) * (b / scale) =
              (norm * b) / (a * scale) :=
            Real.div_mul_div_eq_mul_div_mul norm a b scale
          _ = (b * norm) / (a * scale) :=
            congrArg (fun value : ℝ => value / (a * scale))
              (mul_comm norm b)
          _ = (b / a) * (norm / scale) := by
            exact (Real.div_mul_div_eq_mul_div_mul b a norm scale).symm)

theorem Complex.frequencyScalar_mul_crossingScalar_le_four_scale
    {t : ℝ} {a b : ℕ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseBProcessFrequencyCardScalar t (a : ℤ) *
        Complex.logarithmicPhaseBProcessCrossingScalar ≤
      4 * Complex.logarithmicPhaseBProcessScale t := by
  have hfrequency :=
    Real.longGeometry_frequencyCardTerm_le_three_norm_div_a hgeometry
  have hcrossingNonneg :=
    Complex.logarithmicPhaseBProcessCrossingScalar_nonneg
  have hproduct := mul_le_mul_of_nonneg_right hfrequency hcrossingNonneg
  have hnormalize :
      (3 * (‖t‖ / (a : ℝ))) *
          Complex.logarithmicPhaseBProcessCrossingScalar =
        4 * (‖t‖ / (a : ℝ)) := by
    unfold Complex.logarithmicPhaseBProcessCrossingScalar
    exact Real.three_mul_norm_div_a_mul_four_thirds_eq ‖t‖ (a : ℝ)
  have hnormA := Real.longGeometry_norm_div_a_le_scale hgeometry
  have hfourNonneg : (0 : ℝ) ≤ 4 := Nat.cast_nonneg 4
  have hscaled := mul_le_mul_of_nonneg_left hnormA hfourNonneg
  exact le_trans hproduct
    (le_trans (le_of_eq hnormalize) hscaled)

theorem Complex.frequencyScalar_mul_tailScalar_le_twelve_scale
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseBProcessFrequencyCardScalar t (a : ℤ) *
        Complex.logarithmicPhaseBProcessTailScalar t (b : ℤ) ≤
      12 * Complex.logarithmicPhaseBProcessScale t := by
  have hfrequency :=
    Real.longGeometry_frequencyCardTerm_le_three_norm_div_a hgeometry
  have htailNonneg :=
    Complex.logarithmicPhaseBProcessTailScalar_nonneg
      t ht (Int.ofNat_zero_le b)
  have hproduct := mul_le_mul_of_nonneg_right hfrequency htailNonneg
  have hnormalize :
      (3 * (‖t‖ / (a : ℝ))) *
          Complex.logarithmicPhaseBProcessTailScalar t (b : ℤ) =
        6 * (((b : ℝ) / (a : ℝ)) *
          Complex.logarithmicPhaseBProcessScale t) := by
    unfold Complex.logarithmicPhaseBProcessTailScalar
    exact Real.three_norm_div_a_mul_two_b_scale_div_norm_eq
      ‖t‖ (a : ℝ) (b : ℝ)
      (Complex.logarithmicPhaseBProcessScale t)
      (ne_of_gt (Complex.logarithmicPhaseBProcess_norm_pos t ht))
      (ne_of_gt
        (Nat.cast_pos.mpr
          (Real.logarithmicPhaseLongBranchGeometry_zero_lt_a hgeometry)))
  have hratio := Real.longGeometry_b_div_a_le_two hgeometry
  have hscaledRatio := mul_le_mul_of_nonneg_right hratio
    (Complex.logarithmicPhaseBProcessScale_nonneg t)
  have hsixNonneg : (0 : ℝ) ≤ 6 := Nat.cast_nonneg 6
  have hsix := mul_le_mul_of_nonneg_left hscaledRatio hsixNonneg
  have hright :
      6 * (2 * Complex.logarithmicPhaseBProcessScale t) =
        12 * Complex.logarithmicPhaseBProcessScale t := by
    exact Eq.trans (mul_assoc 6 2 _).symm
      (congrArg
        (fun value : ℝ =>
          value * Complex.logarithmicPhaseBProcessScale t)
        real_six_mul_two_eq_twelve)
  exact le_trans hproduct
    (le_trans (le_of_eq hnormalize)
      (le_trans hsix (le_of_eq hright)))

theorem Complex.frequencyScalar_mul_centralScalar_le_twelve_scale
    {t : ℝ} {a b : ℕ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseBProcessFrequencyCardScalar t (a : ℤ) *
        Complex.logarithmicPhaseBProcessCentralScalar t (b : ℤ) ≤
      12 * Complex.logarithmicPhaseBProcessScale t := by
  have hfrequency :=
    Real.longGeometry_frequencyCardTerm_le_three_norm_div_a hgeometry
  have hcentralNonneg :=
    Complex.logarithmicPhaseBProcessCentralScalar_nonneg
      t (Int.ofNat_zero_le b)
  have hproduct := mul_le_mul_of_nonneg_right hfrequency hcentralNonneg
  have hnormalize :
      (3 * (‖t‖ / (a : ℝ))) *
          Complex.logarithmicPhaseBProcessCentralScalar t (b : ℤ) =
        6 * (((b : ℝ) / (a : ℝ)) *
          (‖t‖ / Complex.logarithmicPhaseBProcessScale t)) := by
    unfold Complex.logarithmicPhaseBProcessCentralScalar
    exact Real.three_norm_div_a_mul_two_b_div_scale_eq
      ‖t‖ (a : ℝ) (b : ℝ)
      (Complex.logarithmicPhaseBProcessScale t)
  have hratio := Real.longGeometry_b_div_a_le_two hgeometry
  have hnormScale :=
    Complex.logarithmicPhaseBProcess_norm_div_scale_le_scale t
  have hnormDivScaleNonneg :
      0 ≤ ‖t‖ / Complex.logarithmicPhaseBProcessScale t :=
    div_nonneg (norm_nonneg t)
      (Complex.logarithmicPhaseBProcessScale_nonneg t)
  have hratioProduct :=
    mul_le_mul_of_nonneg_right hratio hnormDivScaleNonneg
  have htwoNonneg : (0 : ℝ) ≤ 2 := Nat.cast_nonneg 2
  have hscaleProduct :=
    mul_le_mul_of_nonneg_left hnormScale htwoNonneg
  have hmul := le_trans hratioProduct hscaleProduct
  have hsixNonneg : (0 : ℝ) ≤ 6 := Nat.cast_nonneg 6
  have hsix := mul_le_mul_of_nonneg_left hmul hsixNonneg
  have hright :
      6 * (2 * Complex.logarithmicPhaseBProcessScale t) =
        12 * Complex.logarithmicPhaseBProcessScale t := by
    exact Eq.trans (mul_assoc 6 2 _).symm
      (congrArg
        (fun value : ℝ =>
          value * Complex.logarithmicPhaseBProcessScale t)
        real_six_mul_two_eq_twelve)
  exact le_trans hproduct
    (le_trans (le_of_eq hnormalize)
      (le_trans hsix (le_of_eq hright)))

end

end LFunctions
end Boundary
