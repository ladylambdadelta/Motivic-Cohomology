import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicFiniteInactiveFarSideCardinality
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicSupportComparability

/-!
# Endpoint cancellation in the finite far reciprocal budget

Side-specific cardinality is useful only after multiplication by the matching
endpoint packet cost.  This owner carries out those cancellations explicitly.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Real.five_factor_reassociate
    (a b c d e : ℝ) :
    (a * b) * (c * (d * e)) = c * d * (b * (a * e)) := by
  calc
    (a * b) * (c * (d * e)) = a * (b * (c * (d * e))) :=
      mul_assoc a b (c * (d * e))
    _ = a * (c * (b * (d * e))) := by
      exact congrArg (fun value : ℝ => a * value)
        (mul_left_comm b c (d * e))
    _ = a * (c * (d * (b * e))) := by
      exact congrArg (fun value : ℝ => a * (c * value))
        (mul_left_comm b d e)
    _ = c * (a * (d * (b * e))) :=
      mul_left_comm a c (d * (b * e))
    _ = c * (d * (a * (b * e))) := by
      exact congrArg (fun value : ℝ => c * value)
        (mul_left_comm a d (b * e))
    _ = c * (d * (b * (a * e))) := by
      exact congrArg (fun value : ℝ => c * (d * value))
        (mul_left_comm a b e)
    _ = c * d * (b * (a * e)) :=
      (mul_assoc c d (b * (a * e))).symm

theorem Real.mul_three_swap
    (a b c : ℝ) :
    (a * b) * c = (a * c) * b := by
  calc
    (a * b) * c = a * (b * c) := mul_assoc a b c
    _ = a * (c * b) := congrArg (fun value : ℝ => a * value) (mul_comm b c)
    _ = (a * c) * b := (mul_assoc a c b).symm

theorem Real.endpoint_angular_support_reassociate
    (endpoint support angular scale : ℝ) :
    2 * endpoint * scale * (angular * support)⁻¹ =
      2 * ((endpoint / support) * (1 / angular)) * scale := by
  have hinverse :
      (angular * support)⁻¹ = angular⁻¹ * support⁻¹ :=
    (Commute.all angular support).mul_inv
  have hdivisionEndpoint := div_eq_mul_inv endpoint support
  have hdivisionAngular := div_eq_mul_inv 1 angular
  have honeAngular : (1 : ℝ) * angular⁻¹ = angular⁻¹ := one_mul _
  calc
    2 * endpoint * scale * (angular * support)⁻¹ =
        2 * endpoint * scale * (angular⁻¹ * support⁻¹) := by
      exact congrArg (fun value : ℝ => 2 * endpoint * scale * value)
        hinverse
    _ = 2 * ((endpoint * support⁻¹) * angular⁻¹) * scale := by
      have hinner :
          endpoint * (angular⁻¹ * support⁻¹) =
            (endpoint * support⁻¹) * angular⁻¹ := by
        exact Eq.trans
          (congrArg (fun value : ℝ => endpoint * value)
            (mul_comm angular⁻¹ support⁻¹))
          (mul_assoc endpoint support⁻¹ angular⁻¹).symm
      have hswap :
          2 * endpoint * scale * (angular⁻¹ * support⁻¹) =
            (2 * (endpoint * (angular⁻¹ * support⁻¹))) * scale := by
        exact Eq.trans
          (Eq.trans
            (mul_assoc (2 * endpoint) scale
              (angular⁻¹ * support⁻¹))
            (mul_mul_mul_comm 2 endpoint scale
              (angular⁻¹ * support⁻¹)))
          (Real.mul_three_swap 2 scale
            (endpoint * (angular⁻¹ * support⁻¹)))
      exact Eq.trans hswap
        (congrArg (fun value : ℝ => 2 * value * scale) hinner)
    _ = 2 * ((endpoint / support) * (1 / angular)) * scale := by
      have hpair :
          (endpoint * support⁻¹, angular⁻¹) =
            (endpoint / support, 1 / angular) :=
        Prod.ext hdivisionEndpoint.symm
          (hdivisionAngular.trans honeAngular).symm
      exact congrArg (fun values : ℝ × ℝ =>
        2 * (values.1 * values.2) * scale)
        hpair

theorem Real.frequency_endpoint_scale_cancellation
    (norm endpoint support angular scale : ℝ)
    (hnorm : norm ≠ 0) :
    (norm / (angular * support)) *
        (2 * (endpoint * scale / norm)) =
      2 * ((endpoint / support) * (1 / angular)) * scale := by
  have hcancel : norm⁻¹ * norm = 1 := inv_mul_cancel₀ hnorm
  calc
    (norm / (angular * support)) *
        (2 * (endpoint * scale / norm)) =
      (norm * ((angular * support)⁻¹)) *
        (2 * ((endpoint * scale) * norm⁻¹)) := by
          exact congrArg₂ (fun x y : ℝ => x * y)
            (div_eq_mul_inv norm (angular * support))
            (congrArg (fun value : ℝ => 2 * value)
              (div_eq_mul_inv (endpoint * scale) norm))
    _ = 2 * endpoint * scale *
        (((angular * support)⁻¹) * (norm * norm⁻¹)) := by
          exact Eq.trans
            (Real.five_factor_reassociate norm
              ((angular * support)⁻¹) 2 (endpoint * scale) norm⁻¹)
            (congrArg (fun value : ℝ => value *
              ((angular * support)⁻¹ * (norm * norm⁻¹)))
              (mul_assoc 2 endpoint scale).symm)
    _ = 2 * endpoint * scale * (angular * support)⁻¹ := by
          have hcancelTransport :
              2 * endpoint * scale *
                  ((angular * support)⁻¹ * (norm * norm⁻¹)) =
                2 * endpoint * scale * ((angular * support)⁻¹ * 1) :=
            congrArg (fun value : ℝ =>
              2 * endpoint * scale * ((angular * support)⁻¹ * value))
              (mul_inv_cancel₀ hnorm)
          exact Eq.trans hcancelTransport
            (congrArg (fun value : ℝ => 2 * endpoint * scale * value)
              (mul_one (angular * support)⁻¹))
    _ = 2 * ((endpoint / support) * (1 / angular)) * scale := by
          exact Real.endpoint_angular_support_reassociate
            endpoint support angular scale

theorem Complex.logarithmicPhaseFiniteRightInactive_blockRight_lt_norm_div_six
    {t : ℝ} {a b m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b) :
    (b : ℝ) < ‖t‖ / 6 := by
  have hdata :=
    (Complex.mem_logarithmicPhasePoissonRightInactiveModes_iff
      t a b m).mp hm
  exact lt_of_lt_of_le hdata.2.2
    (Complex.logarithmicPhaseFourierStationaryPoint_le_norm_div_six
      t hdata.2.1)

theorem Complex.logarithmicPhaseFiniteRightFar_blockRight_lt_norm_div_six
    {t : ℝ} {a b m : ℤ}
    (hm : m ∈ Complex.logarithmicPhaseFiniteRightFarModes t a b) :
    (b : ℝ) < ‖t‖ / 6 := by
  have hbase :=
    ((Complex.mem_logarithmicPhaseFiniteRightFarModes_iff
      t a b m).mp hm).1
  exact
    Complex.logarithmicPhaseFiniteRightInactive_blockRight_lt_norm_div_six
      hbase

theorem Real.endpoint_mul_scale_div_norm_le_scale_div_six
    {endpoint norm scale : ℝ}
    (hnorm : 0 < norm)
    (hendpoint : endpoint ≤ norm / 6)
    (hscale : 0 ≤ scale) :
    endpoint * scale / norm ≤ scale / 6 := by
  have hmul := mul_le_mul_of_nonneg_right hendpoint hscale
  have hreorder : (norm / 6) * scale = (scale / 6) * norm := by
    exact Eq.trans (div_mul_eq_mul_div norm 6 scale)
      (Eq.trans
        (congrArg (fun value : ℝ => value / 6) (mul_comm norm scale))
        (div_mul_eq_mul_div scale 6 norm).symm)
  have hright : endpoint * scale ≤ (scale / 6) * norm :=
    le_trans hmul (le_of_eq hreorder)
  exact (div_le_iff₀ hnorm).mpr hright

theorem Real.two_div_six_eq_one_third :
    (2 : ℝ) / 6 = 1 / 3 := by
  have htwo : (2 : ℝ) / 2 = 1 :=
    div_self (ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 1)))
  have hmul : (2 : ℝ) * 3 = 6 := by
    exact (Nat.cast_mul 2 3).symm.trans
      (congrArg Nat.cast (show 2 * 3 = 6 from rfl))
  exact Eq.trans
    (congrArg (fun value : ℝ => (2 : ℝ) / value) hmul.symm)
    (Eq.trans (div_div (2 : ℝ) 2 3).symm
      (congrArg (fun value : ℝ => value / 3) htwo))

theorem Complex.logarithmicPhaseFiniteRightFar_perModeMajorant_le_one_third_scale
    {t : ℝ} {a b m : ℤ}
    (ht : 1 ≤ ‖t‖)
    (hm : m ∈ Complex.logarithmicPhaseFiniteRightFarModes t a b) :
    Complex.logarithmicPhaseFiniteRightFarPerModeReciprocalMajorant t b ≤
      (1 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
  have hnormPos := Complex.logarithmicPhaseBProcess_norm_pos t ht
  have hb :=
    (Complex.logarithmicPhaseFiniteRightFar_blockRight_lt_norm_div_six
      hm).le
  have hsingle := Real.endpoint_mul_scale_div_norm_le_scale_div_six
    hnormPos hb (Complex.logarithmicPhaseBProcessScale_nonneg t)
  have htwice := mul_le_mul_of_nonneg_left hsingle (Nat.cast_nonneg 2)
  unfold Complex.logarithmicPhaseFiniteRightFarPerModeReciprocalMajorant
  have hnormalize :
      2 * (Complex.logarithmicPhaseBProcessScale t / 6) =
        (1 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
    calc
      2 * (Complex.logarithmicPhaseBProcessScale t / 6) =
          (2 * Complex.logarithmicPhaseBProcessScale t) / 6 :=
        (mul_div_assoc (2 : ℝ) _ 6).symm
      _ = (Complex.logarithmicPhaseBProcessScale t * 2) / 6 :=
        congrArg (fun value : ℝ => value / 6)
          (mul_comm (2 : ℝ) (Complex.logarithmicPhaseBProcessScale t))
      _ = Complex.logarithmicPhaseBProcessScale t * ((2 : ℝ) / 6) :=
        mul_div_assoc _ 2 6
      _ = Complex.logarithmicPhaseBProcessScale t * (1 / 3) :=
        congrArg (fun value : ℝ =>
          Complex.logarithmicPhaseBProcessScale t * value)
          Real.two_div_six_eq_one_third
      _ = (1 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t :=
        mul_comm _ _
  exact le_trans htwice (le_of_eq hnormalize)

theorem Real.blockRight_le_quantitativeSupportRight
    (b : ℕ) :
    (b : ℝ) ≤
      Complex.logarithmicPhaseQuantitativeSupportRight (b : ℤ) := by
  unfold Complex.logarithmicPhaseQuantitativeSupportRight
  exact le_add_of_nonneg_right
    (div_nonneg zero_le_one (Nat.cast_nonneg 3))

theorem Real.blockRight_div_supportRight_le_one
    (b : ℕ) :
    (b : ℝ) /
        Complex.logarithmicPhaseQuantitativeSupportRight (b : ℤ) ≤ 1 := by
  have hrightPos :
      0 < Complex.logarithmicPhaseQuantitativeSupportRight (b : ℤ) := by
    unfold Complex.logarithmicPhaseQuantitativeSupportRight
    exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg b)
      (div_pos zero_lt_one (Nat.cast_pos.mpr (Nat.succ_pos 2)))
  exact (div_le_one hrightPos).mpr
    (Real.blockRight_le_quantitativeSupportRight b)

theorem Real.one_div_two_pi_le_one
    : (1 : ℝ) / (2 * Real.pi) ≤ 1 := by
  exact (div_le_one Complex.two_mul_pi_pos).mpr Real.one_le_two_mul_pi

theorem Complex.rightThreshold_mul_endpointScale_eq_ratioScale
    (t : ℝ) (ht : 1 ≤ ‖t‖) (b : ℕ) :
    Complex.logarithmicPhaseFiniteRightFrequencyThreshold t (b : ℤ) *
        Complex.logarithmicPhaseFiniteRightFarPerModeReciprocalMajorant
          t (b : ℤ) =
      2 * (((b : ℝ) /
          Complex.logarithmicPhaseQuantitativeSupportRight (b : ℤ)) *
        ((1 : ℝ) / (2 * Real.pi))) *
          Complex.logarithmicPhaseBProcessScale t := by
  unfold Complex.logarithmicPhaseFiniteRightFrequencyThreshold
  unfold Complex.logarithmicPhaseFiniteRightFarPerModeReciprocalMajorant
  have hnormNe : ‖t‖ ≠ 0 :=
    ne_of_gt (Complex.logarithmicPhaseBProcess_norm_pos t ht)
  exact Real.frequency_endpoint_scale_cancellation
    ‖t‖ (b : ℝ)
    (Complex.logarithmicPhaseQuantitativeSupportRight (b : ℤ))
    (2 * Real.pi)
    (Complex.logarithmicPhaseBProcessScale t)
    hnormNe

theorem Complex.rightThreshold_mul_endpointScale_le_two_scale
    (t : ℝ) (ht : 1 ≤ ‖t‖) (b : ℕ) :
    Complex.logarithmicPhaseFiniteRightFrequencyThreshold t (b : ℤ) *
        Complex.logarithmicPhaseFiniteRightFarPerModeReciprocalMajorant
          t (b : ℤ) ≤
      2 * Complex.logarithmicPhaseBProcessScale t := by
  have hratio := Real.blockRight_div_supportRight_le_one b
  have hpi := Real.one_div_two_pi_le_one
  have hpiNonneg : 0 ≤ (1 : ℝ) / (2 * Real.pi) :=
    div_nonneg zero_le_one Complex.two_mul_pi_pos.le
  have hproduct := mul_le_mul hratio hpi hpiNonneg zero_le_one
  have hscale := mul_le_mul_of_nonneg_right hproduct
    (Complex.logarithmicPhaseBProcessScale_nonneg t)
  have htwice := mul_le_mul_of_nonneg_left hscale (Nat.cast_nonneg 2)
  have htwice' :
      2 * (((b : ℝ) /
        Complex.logarithmicPhaseQuantitativeSupportRight (b : ℤ)) *
          ((1 : ℝ) / (2 * Real.pi)) *
          Complex.logarithmicPhaseBProcessScale t) ≤
        2 * Complex.logarithmicPhaseBProcessScale t := by
    have hrightNorm :
        (1 : ℝ) * 1 * Complex.logarithmicPhaseBProcessScale t =
          Complex.logarithmicPhaseBProcessScale t := by
      exact Eq.trans (mul_assoc 1 1
        (Complex.logarithmicPhaseBProcessScale t))
        (Eq.trans
          (congrArg (fun value : ℝ => (1 : ℝ) * value)
            (one_mul (Complex.logarithmicPhaseBProcessScale t)))
          (one_mul _))
    have hrightTwice :
        (2 : ℝ) *
            (1 * 1 * Complex.logarithmicPhaseBProcessScale t) ≤
          2 * Complex.logarithmicPhaseBProcessScale t :=
      le_of_eq (congrArg (fun value : ℝ => (2 : ℝ) * value) hrightNorm)
    exact le_trans htwice hrightTwice
  exact Eq.subst (motive := fun value : ℝ => value ≤ _)
    (Complex.rightThreshold_mul_endpointScale_eq_ratioScale t ht b).symm
    (Eq.subst
      (motive := fun value : ℝ => value ≤
        2 * Complex.logarithmicPhaseBProcessScale t)
      (mul_assoc 2
        (((b : ℝ) /
          Complex.logarithmicPhaseQuantitativeSupportRight (b : ℤ)) *
            ((1 : ℝ) / (2 * Real.pi)))
        (Complex.logarithmicPhaseBProcessScale t)).symm
      htwice')

theorem Real.blockLeft_div_quantitativeSupportLeft_le_three
    (a : ℕ) (ha : 2 ≤ a) :
    (a : ℝ) /
        Complex.logarithmicPhaseQuantitativeSupportLeft (a : ℤ) ≤ 3 := by
  have hleft := Complex.one_third_a_le_quantitativeSupportLeft a ha
  have hleftPos := Complex.quantitativeSupportLeft_pos_of_two_le a ha
  have hdivide := (div_le_iff₀ hleftPos).mpr
    (show (a : ℝ) ≤ 3 * Complex.logarithmicPhaseQuantitativeSupportLeft (a : ℤ) from by
      have hmul := mul_le_mul_of_nonneg_right hleft
        (show (0 : ℝ) ≤ 3 from Nat.cast_nonneg 3)
      have hcancel : ((a : ℝ) / 3) * 3 = (a : ℝ) :=
        div_mul_cancel₀ (a : ℝ)
          (ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 2)))
      exact le_trans (le_of_eq hcancel.symm)
        (le_trans hmul (le_of_eq (mul_comm _ _))))
  have hnormalize :
      ((a : ℝ) / 3) * 3 = (a : ℝ) := by
    exact div_mul_cancel₀ (a : ℝ)
      (ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 2)))
  exact hdivide

theorem Complex.leftFrequencyTerm_mul_endpointScale_eq_ratioScale
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a : ℕ) :
    (‖t‖ /
        (2 * Real.pi *
          Real.integerBlockCutoffSupportLeftEndpoint (a : ℤ))) *
        Complex.logarithmicPhaseFiniteLeftFarPerModeReciprocalMajorant
          t (a : ℤ) =
      2 * (((a : ℝ) /
          Real.integerBlockCutoffSupportLeftEndpoint (a : ℤ)) *
        ((1 : ℝ) / (2 * Real.pi))) *
          Complex.logarithmicPhaseBProcessScale t := by
  unfold Complex.logarithmicPhaseFiniteLeftFarPerModeReciprocalMajorant
  exact Real.frequency_endpoint_scale_cancellation
    ‖t‖ (a : ℝ)
    (Real.integerBlockCutoffSupportLeftEndpoint (a : ℤ))
    (2 * Real.pi)
    (Complex.logarithmicPhaseBProcessScale t)
    (ne_of_gt (Complex.logarithmicPhaseBProcess_norm_pos t ht))

theorem Real.blockLeft_div_cutoffSupportLeft_le_three
    {t : ℝ} {a b : ℕ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    (a : ℝ) /
        Real.integerBlockCutoffSupportLeftEndpoint (a : ℤ) ≤ 3 := by
  have hleft :=
    Real.longGeometry_one_third_a_le_cutoffSupportLeft hgeometry
  have hleftPos :=
    Complex.integerBlockCutoffSupportLeftEndpoint_pos
      (Int.ofNat_le.mpr
        (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry))
  have hdivide := (div_le_iff₀ hleftPos).mpr
    (show (a : ℝ) ≤ 3 * Real.integerBlockCutoffSupportLeftEndpoint (a : ℤ) from by
      have hmul := mul_le_mul_of_nonneg_right hleft
        (show (0 : ℝ) ≤ 3 from Nat.cast_nonneg 3)
      have hcancel : ((a : ℝ) / 3) * 3 = (a : ℝ) :=
        div_mul_cancel₀ (a : ℝ)
          (ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 2)))
      exact le_trans (le_of_eq hcancel.symm)
        (le_trans hmul (le_of_eq (mul_comm _ _))))
  have hnormalize : ((a : ℝ) / 3) * 3 = (a : ℝ) :=
    div_mul_cancel₀ (a : ℝ)
      (ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 2)))
  exact hdivide

theorem Complex.leftFrequencyTerm_mul_endpointScale_le_six_scale
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    (‖t‖ /
        (2 * Real.pi *
          Real.integerBlockCutoffSupportLeftEndpoint (a : ℤ))) *
        Complex.logarithmicPhaseFiniteLeftFarPerModeReciprocalMajorant
          t (a : ℤ) ≤
      6 * Complex.logarithmicPhaseBProcessScale t := by
  have hratio :=
    Real.blockLeft_div_cutoffSupportLeft_le_three hgeometry
  have hpi := Real.one_div_two_pi_le_one
  have hratioNonneg :
      0 ≤ (a : ℝ) /
        Real.integerBlockCutoffSupportLeftEndpoint (a : ℤ) :=
    div_nonneg (Nat.cast_nonneg a)
      (Complex.integerBlockCutoffSupportLeftEndpoint_pos
        (Int.ofNat_le.mpr
          (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry))).le
  have hpiNonneg : 0 ≤ (1 : ℝ) / (2 * Real.pi) :=
    div_nonneg zero_le_one Complex.two_mul_pi_pos.le
  have hproductFirst := mul_le_mul_of_nonneg_right hratio hpiNonneg
  have hproductSecond := mul_le_mul_of_nonneg_left hpi
    (show (0 : ℝ) ≤ 3 from Nat.cast_nonneg 3)
  have hproduct := le_trans hproductFirst hproductSecond
  have hthree : (3 : ℝ) * 1 = 3 := mul_one 3
  have hproductThree :
      ((a : ℝ) /
          Real.integerBlockCutoffSupportLeftEndpoint (a : ℤ)) *
          ((1 : ℝ) / (2 * Real.pi)) ≤ 3 :=
    le_trans hproduct (le_of_eq hthree)
  have hscale := mul_le_mul_of_nonneg_right hproductThree
    (Complex.logarithmicPhaseBProcessScale_nonneg t)
  have htwice := mul_le_mul_of_nonneg_left hscale (Nat.cast_nonneg 2)
  have hnormalize :
      2 * (3 * Complex.logarithmicPhaseBProcessScale t) =
        6 * Complex.logarithmicPhaseBProcessScale t := by
    exact Eq.trans (mul_assoc 2 3 _).symm
      (congrArg
        (fun coefficient : ℝ => coefficient *
          Complex.logarithmicPhaseBProcessScale t)
        (show (2 : ℝ) * 3 = 6 from
          (Nat.cast_mul 2 3).symm.trans (congrArg Nat.cast (show 2 * 3 = 6 from rfl))))
  have htwice' :
      2 * (((a : ℝ) /
        Real.integerBlockCutoffSupportLeftEndpoint (a : ℤ)) *
          ((1 : ℝ) / (2 * Real.pi)) *
          Complex.logarithmicPhaseBProcessScale t) ≤
      2 * (3 * Complex.logarithmicPhaseBProcessScale t) :=
    htwice
  have htwiceLeft :
      2 * (((a : ℝ) /
        Real.integerBlockCutoffSupportLeftEndpoint (a : ℤ)) *
          ((1 : ℝ) / (2 * Real.pi))) *
          Complex.logarithmicPhaseBProcessScale t ≤
        2 * (3 * Complex.logarithmicPhaseBProcessScale t) :=
    Eq.subst
      (motive := fun value : ℝ => value ≤
        2 * (3 * Complex.logarithmicPhaseBProcessScale t))
      (mul_assoc 2
        (((a : ℝ) /
          Real.integerBlockCutoffSupportLeftEndpoint (a : ℤ)) *
            ((1 : ℝ) / (2 * Real.pi)))
        (Complex.logarithmicPhaseBProcessScale t)).symm
      htwice'
  exact Eq.subst (motive := fun value : ℝ => value ≤ _)
    (Complex.leftFrequencyTerm_mul_endpointScale_eq_ratioScale
      t ht a).symm
    (le_trans htwiceLeft (le_of_eq hnormalize))

theorem Complex.logarithmicPhaseFiniteRightFarBudget_eq_zero_of_empty
    (t : ℝ) (a b : ℤ)
    (hempty : Complex.logarithmicPhaseFiniteRightFarModes t a b = ∅) :
    Complex.logarithmicPhaseFiniteRightFarReciprocalBudget t a b = 0 := by
  unfold Complex.logarithmicPhaseFiniteRightFarReciprocalBudget
  exact Eq.trans
    (congrArg
      (fun modes : Finset ℤ =>
        ∑ m ∈ modes, (
          Complex.logarithmicPhaseLeftReciprocalGap t m (b : ℝ) +
            Complex.logarithmicPhaseLeftReciprocalGap t m (b : ℝ)))
      hempty)
    Finset.sum_empty

theorem Complex.logarithmicPhaseFiniteLeftFarBudget_eq_zero_of_empty
    (t : ℝ) (a b : ℤ)
    (hempty : Complex.logarithmicPhaseFiniteLeftFarModes t a b = ∅) :
    Complex.logarithmicPhaseFiniteLeftFarReciprocalBudget t a b = 0 := by
  unfold Complex.logarithmicPhaseFiniteLeftFarReciprocalBudget
  exact Eq.trans
    (congrArg
      (fun modes : Finset ℤ =>
        ∑ m ∈ modes, (
          Complex.logarithmicPhaseRightReciprocalGap t m (a : ℝ) +
            Complex.logarithmicPhaseRightReciprocalGap t m (a : ℝ)))
      hempty)
    Finset.sum_empty

end

end LFunctions
end Boundary
