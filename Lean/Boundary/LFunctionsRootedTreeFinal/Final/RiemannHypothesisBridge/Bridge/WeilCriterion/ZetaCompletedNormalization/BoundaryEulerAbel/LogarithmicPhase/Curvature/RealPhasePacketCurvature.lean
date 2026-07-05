import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseCurvatureLower
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseShiftedDifference

/-!
# Real-phase packet curvature bounds

This file owns the local reciprocal-curvature packet estimates used by the
long logarithmic B-process branch.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Concrete endpoint data for a nonempty logarithmic derivative-frequency
packet in the positive-frequency long branch. -/
theorem Complex.logarithmicPhaseRealPhase_nonempty_derivPacket_endpoint_data_of_growth
    (t : ℝ)
    (_ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    {m : ℤ}
    (hp :
      (Complex.realPhase_secondDerivative_vdc_derivPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m).Nonempty)
    (_ha : 1 ≤ a)
    (_hab : a ≤ b)
    (hderiv_growth :
      ∀ x y : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        x ≤ y →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (y - x) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)) :
    ∃ p q : ℕ,
      p ∈ Complex.realPhase_secondDerivative_vdc_derivPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m ∧
      q ∈ Complex.realPhase_secondDerivative_vdc_derivPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m ∧
      (p : ℝ) ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) ∧
      (q : ℝ) ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) ∧
      p ≤ q ∧
      (‖t‖ *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          ((q : ℝ) - (p : ℝ)) ≤
        deriv
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          (q : ℝ) -
        deriv
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          (p : ℝ)) ∧
      deriv
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) q -
        deriv
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) p < 1 ∧
      ((Complex.realPhase_secondDerivative_vdc_derivPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m).card : ℝ) ≤
        (((q + 1 : ℕ) : ℝ) - (p : ℝ)) := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  let p : ℕ :=
    (Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).min' hp
  let q : ℕ :=
    (Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).max' hp
  have hp_mem :
      p ∈ Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m :=
    Complex.realPhase_secondDerivative_vdc_derivPacket_min_mem φ hp
  have hq_mem :
      q ∈ Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m :=
    Complex.realPhase_secondDerivative_vdc_derivPacket_max_mem φ hp
  have hp_block_nat : p ∈ Finset.Icc a b :=
    Complex.realPhase_secondDerivative_vdc_derivPacket_mem_block φ hp_mem
  have hq_block_nat : q ∈ Finset.Icc a b :=
    Complex.realPhase_secondDerivative_vdc_derivPacket_mem_block φ hq_mem
  have hp_bounds_nat : a ≤ p ∧ p ≤ b :=
    Finset.mem_Icc.mp hp_block_nat
  have hq_bounds_nat : a ≤ q ∧ q ≤ b :=
    Finset.mem_Icc.mp hq_block_nat
  have hp_interval :
      (p : ℝ) ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) :=
    And.intro
      (Nat.cast_le.mpr hp_bounds_nat.1)
      (Nat.cast_le.mpr
        (le_trans hp_bounds_nat.2 (Nat.le_succ b)))
  have hq_interval :
      (q : ℝ) ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) :=
    And.intro
      (Nat.cast_le.mpr hq_bounds_nat.1)
      (Nat.cast_le.mpr
        (le_trans hq_bounds_nat.2 (Nat.le_succ b)))
  have hp_le_q : p ≤ q :=
    Complex.realPhase_secondDerivative_vdc_derivPacket_min_le_of_mem
      φ hp hq_mem
  have hpq_real : (p : ℝ) ≤ (q : ℝ) :=
    Nat.cast_le.mpr hp_le_q
  have hgrowth :
      (‖t‖ *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          ((q : ℝ) - (p : ℝ)) ≤
        deriv φ (q : ℝ) - deriv φ (p : ℝ)) :=
    hderiv_growth (p : ℝ) (q : ℝ) hp_interval hq_interval hpq_real
  have hwindow :
      deriv φ q - deriv φ p < 1 :=
    Complex.realPhase_secondDerivative_vdc_derivPacket_deriv_sub_lt_one
      φ hp_mem hq_mem
  have hendpoint_card :
      ((Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).card : ℝ) ≤
        (((q + 1 : ℕ) : ℝ) - (p : ℝ)) :=
    Complex.realPhase_secondDerivative_vdc_derivPacket_card_le_endpoint_span
      φ hp
  exact Exists.intro p
    (Exists.intro q
      (And.intro hp_mem
        (And.intro hq_mem
          (And.intro hp_interval
            (And.intro hq_interval
              (And.intro hp_le_q
                (And.intro hgrowth
                  (And.intro hwindow hendpoint_card))))))))

/-- The endpoint span of one nonempty logarithmic derivative packet has
curvature-scale product strictly below one. -/
theorem Complex.logarithmicPhaseRealPhase_nonempty_derivPacket_scaled_span_lt_one
    (t : ℝ)
    (_ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    {p q : ℕ}
    {k : ℤ}
    (hp_mem :
      p ∈ Complex.realPhase_secondDerivative_vdc_derivPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b k)
    (hq_mem :
      q ∈ Complex.realPhase_secondDerivative_vdc_derivPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b k)
    (hgrowth :
      (‖t‖ *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          ((q : ℝ) - (p : ℝ)) ≤
        deriv
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          (q : ℝ) -
        deriv
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          (p : ℝ))) :
    ‖t‖ *
        ((((b + 1 : ℕ) : ℝ) *
          (((b + 1 : ℕ) : ℝ)))⁻¹) *
        ((q : ℝ) - (p : ℝ)) < 1 := by
  have hwindow :
      deriv
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        q -
        deriv
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) p < 1 :=
    Complex.realPhase_secondDerivative_vdc_derivPacket_deriv_sub_lt_one
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      hp_mem hq_mem
  exact lt_of_le_of_lt hgrowth hwindow

/-- Arithmetic conversion from curvature-scaled endpoint span below one to
the reciprocal curvature-scale endpoint bound. -/
theorem Real.logarithmicPhaseRealPhase_span_le_curvatureScale_add_one
    {t : ℝ}
    (ht : 1 ≤ ‖t‖)
    {b p q : ℕ}
    (hscaled :
      ‖t‖ *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          ((q : ℝ) - (p : ℝ)) < 1) :
    (((q + 1 : ℕ) : ℝ) - (p : ℝ)) ≤
      ((((b + 1 : ℕ) : ℝ) * (((b + 1 : ℕ) : ℝ))) / ‖t‖ + 1) := by
  let A : ℝ := ‖t‖
  let B : ℝ := ((b + 1 : ℕ) : ℝ)
  let Bsq : ℝ := B * B
  let x : ℝ := (q : ℝ) - (p : ℝ)
  have hA_pos : 0 < A :=
    lt_of_lt_of_le zero_lt_one ht
  have hB_pos : 0 < B :=
    Nat.cast_pos.mpr (Nat.succ_pos b)
  have hBsq_pos : 0 < Bsq :=
    mul_pos hB_pos hB_pos
  have hcoef_pos : 0 < A * Bsq⁻¹ :=
    mul_pos hA_pos (inv_pos.mpr hBsq_pos)
  have hx_le_curvature : x ≤ Bsq / A := by
    match lt_or_ge 0 x with
    | Or.inl hx_pos =>
        have hscaled_local :
            (A * Bsq⁻¹) * x < 1 := by
          exact hscaled
        have hscaled_comm :
            x * (A * Bsq⁻¹) < 1 :=
          Eq.subst
            (motive := fun r : ℝ => r < 1)
            (mul_comm (A * Bsq⁻¹) x)
            hscaled_local
        have hx_lt_recip :
            x < 1 / (A * Bsq⁻¹) :=
          (lt_div_iff₀ hcoef_pos).mpr hscaled_comm
        have hrecip_eq :
            1 / (A * Bsq⁻¹) = Bsq / A := by
          calc
            1 / (A * Bsq⁻¹) = (A * Bsq⁻¹)⁻¹ :=
              one_div (A * Bsq⁻¹)
            _ = (Bsq⁻¹)⁻¹ * A⁻¹ :=
              mul_inv_rev A Bsq⁻¹
            _ = Bsq * A⁻¹ :=
              congrArg (fun y : ℝ => y * A⁻¹) (inv_inv Bsq)
            _ = Bsq / A :=
              (div_eq_mul_inv Bsq A).symm
        exact
          le_of_lt
            (Eq.subst
              (motive := fun y : ℝ => x < y)
              hrecip_eq
              hx_lt_recip)
    | Or.inr hx_nonpos =>
        have hcurv_nonneg : 0 ≤ Bsq / A :=
          div_nonneg (le_of_lt hBsq_pos) (le_of_lt hA_pos)
        exact le_trans hx_nonpos hcurv_nonneg
  have hspan_eq :
      (((q + 1 : ℕ) : ℝ) - (p : ℝ)) = x + 1 := by
    have hq_succ :
        ((q + 1 : ℕ) : ℝ) = (q : ℝ) + 1 :=
      Nat.cast_add_one q
    calc
      (((q + 1 : ℕ) : ℝ) - (p : ℝ)) =
          ((q : ℝ) + 1) - (p : ℝ) :=
        congrArg (fun y : ℝ => y - (p : ℝ)) hq_succ
      _ = ((q : ℝ) + 1) + (-(p : ℝ)) :=
        sub_eq_add_neg ((q : ℝ) + 1) (p : ℝ)
      _ = (q : ℝ) + (1 + (-(p : ℝ))) :=
        add_assoc (q : ℝ) 1 (-(p : ℝ))
      _ = (q : ℝ) + ((-(p : ℝ)) + 1) :=
        congrArg (fun y : ℝ => (q : ℝ) + y) (add_comm 1 (-(p : ℝ)))
      _ = ((q : ℝ) + (-(p : ℝ))) + 1 :=
        (add_assoc (q : ℝ) (-(p : ℝ)) 1).symm
      _ = ((q : ℝ) - (p : ℝ)) + 1 :=
        congrArg (fun y : ℝ => y + 1)
          (sub_eq_add_neg (q : ℝ) (p : ℝ)).symm
      _ = x + 1 :=
        rfl
  have hsum_le :
      x + 1 ≤ Bsq / A + 1 :=
    add_le_add_right hx_le_curvature 1
  exact
    Eq.subst
      (motive := fun y : ℝ => y ≤ Bsq / A + 1)
      hspan_eq.symm
      hsum_le

/-- A nonempty logarithmic derivative packet is bounded by the reciprocal
curvature scale plus one. -/
theorem Complex.logarithmicPhaseRealPhase_nonempty_derivPacket_card_le_curvatureScale_add_one
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    {m : ℤ}
    (hp :
      (Complex.realPhase_secondDerivative_vdc_derivPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m).Nonempty)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hderiv_growth :
      ∀ x y : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        x ≤ y →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (y - x) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)) :
    ((Complex.realPhase_secondDerivative_vdc_derivPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m).card : ℝ) ≤
      ((((b + 1 : ℕ) : ℝ) * (((b + 1 : ℕ) : ℝ))) / ‖t‖ + 1) := by
  match
    Complex.logarithmicPhaseRealPhase_nonempty_derivPacket_endpoint_data_of_growth
      t ht hp ha hab hderiv_growth with
  | ⟨p, q, hp_mem, hq_mem, hp_interval, hq_interval, hp_le_q,
      hgrowth, hwindow, hendpoint_card⟩ =>
      have hscaled :
          ‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              ((q : ℝ) - (p : ℝ)) < 1 :=
        Complex.logarithmicPhaseRealPhase_nonempty_derivPacket_scaled_span_lt_one
          t ht hp_mem hq_mem hgrowth
      have hendpoint_bound :
          (((q + 1 : ℕ) : ℝ) - (p : ℝ)) ≤
            ((((b + 1 : ℕ) : ℝ) * (((b + 1 : ℕ) : ℝ))) / ‖t‖ + 1) :=
        Real.logarithmicPhaseRealPhase_span_le_curvatureScale_add_one
          ht hscaled
      exact le_trans hendpoint_card hendpoint_bound

/-- Packet-sum bound for one nonempty logarithmic derivative packet by the
reciprocal curvature scale plus one. -/
theorem Complex.logarithmicPhaseRealPhase_nonempty_packetSum_le_curvatureScale_add_one
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    {m : ℤ}
    (hp :
      (Complex.realPhase_secondDerivative_vdc_derivPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m).Nonempty)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hderiv_growth :
      ∀ x y : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        x ≤ y →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (y - x) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)) :
    ‖Complex.realPhase_secondDerivative_vdc_packetSum
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b m‖ ≤
      ((((b + 1 : ℕ) : ℝ) * (((b + 1 : ℕ) : ℝ))) / ‖t‖ + 1) := by
  exact le_trans
    (Complex.realPhase_secondDerivative_vdc_packetSum_norm_le_card
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b m)
    (Complex.logarithmicPhaseRealPhase_nonempty_derivPacket_card_le_curvatureScale_add_one
      t ht hp ha hab hderiv_growth)

/-- An active logarithmic derivative packet is nonempty. -/
theorem Complex.logarithmicPhaseRealPhase_activeDerivPacket_nonempty
    (t : ℝ)
    {a b : ℕ}
    {m : ℤ}
    (hm :
      m ∈
        Complex.realPhase_secondDerivative_vdc_activeDerivPackets
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b) :
    (Complex.realPhase_secondDerivative_vdc_derivPacket
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b m).Nonempty := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  have hexists :
      ∃ n : ℕ,
        n ∈ Finset.Icc a b ∧
          Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ n = m :=
    Finset.mem_image.mp hm
  match hexists with
  | ⟨n, hn_block, hn_index⟩ =>
      have hn_packet :
          n ∈ Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m :=
        (Complex.mem_realPhase_secondDerivative_vdc_derivPacket_iff_index_eq
          φ).mpr
          (And.intro hn_block hn_index)
      exact ⟨n, hn_packet⟩

/-- Uniform reciprocal-curvature-scale packet-sum bound over active
logarithmic derivative packets. -/
theorem Complex.logarithmicPhaseRealPhase_active_packetSum_le_curvatureScale_add_one
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    {m : ℤ}
    (hm :
      m ∈
        Complex.realPhase_secondDerivative_vdc_activeDerivPackets
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hderiv_growth :
      ∀ x y : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        x ≤ y →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (y - x) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)) :
    ‖Complex.realPhase_secondDerivative_vdc_packetSum
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b m‖ ≤
      ((((b + 1 : ℕ) : ℝ) * (((b + 1 : ℕ) : ℝ))) / ‖t‖ + 1) := by
  exact
    Complex.logarithmicPhaseRealPhase_nonempty_packetSum_le_curvatureScale_add_one
      t ht
      (Complex.logarithmicPhaseRealPhase_activeDerivPacket_nonempty t hm)
      ha hab hderiv_growth

/-- Closed reciprocal-curvature-scale packet-sum bound over active logarithmic
derivative packets in the positive-frequency branch. -/
theorem Complex.logarithmicPhaseRealPhase_active_packetSum_le_curvatureScale_add_one_of_nonneg
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    {m : ℤ}
    (hm :
      m ∈
        Complex.realPhase_secondDerivative_vdc_activeDerivPackets
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    ‖Complex.realPhase_secondDerivative_vdc_packetSum
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b m‖ ≤
      ((((b + 1 : ℕ) : ℝ) * (((b + 1 : ℕ) : ℝ))) / ‖t‖ + 1) := by
  exact
    Complex.logarithmicPhaseRealPhase_active_packetSum_le_curvatureScale_add_one
      t ht hm ha hab
      (Complex.logarithmicPhaseRealPhase_deriv_growth_on_integer_block
        t ht ht_nonneg ha hab)

end

end LFunctions
end Boundary
