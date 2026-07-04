import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseEndpointFirstDerivative
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseEndpointRightZero
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseZeroDerivPacketTerminal
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseZeroTerminalIncrement

/-!
# Real-phase right endpoint contribution

This file owns the local reduction from a cardinality estimate for the
right-endpoint zero derivative packet to the corresponding packet contribution
budget.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- If the zero derivative-frequency packet has the right endpoint-cardinality
budget, then its packet sum satisfies the same contribution budget. -/
theorem Complex.logarithmicPhaseRealPhase_endpointRightZeroPacketContribution_le_twentyTarget_of_card
    (t : ℝ)
    {a b : ℕ}
    (hcard :
      ((Complex.realPhase_secondDerivative_vdc_derivPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b 0).card : ℝ) ≤
        20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)))) :
    ‖Complex.realPhase_secondDerivative_vdc_packetSum
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b 0‖ ≤
      20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) :=
  le_trans
    (Complex.realPhase_secondDerivative_vdc_packetSum_norm_le_card
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b 0)
    hcard

/-- If the zero derivative-frequency packet is explicitly a terminal interval
and that terminal interval has the first-derivative monotonicity/separation
data, then the zero packet has the endpoint contribution budget. -/
theorem Complex.logarithmicPhaseRealPhase_endpointRightZeroPacketContribution_le_twentyTarget_of_terminalInterval
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b c : ℕ}
    (hc_one : 1 ≤ c)
    (hcb : c ≤ b)
    (hpacket :
      Complex.realPhase_secondDerivative_vdc_derivPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b 0 =
        Finset.Icc c b)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) c b)
    (hred_mono :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) c b)
    (hsep :
      Complex.realPhase_integerIncrementSeparatedOn
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) c b
        (‖t‖ / ((b + 1 : ℕ) : ℝ))) :
    ‖Complex.realPhase_secondDerivative_vdc_packetSum
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b 0‖ ≤
      20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  have hsum_eq :
      Complex.realPhase_secondDerivative_vdc_packetSum φ a b 0 =
        ∑ n ∈ Finset.Icc c b,
          Complex.exp (Complex.I * (φ n : ℂ)) :=
    congrArg
      (fun S : Finset ℕ =>
        ∑ n ∈ S, Complex.exp (Complex.I * (φ n : ℂ)))
      hpacket
  have hinterval :
      ‖∑ n ∈ Finset.Icc c b,
        Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
        20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) :=
    Complex.logarithmicPhaseRealPhase_firstDerivative_subblock_le_twentyTarget
      t ht hc_one hcb le_rfl hinc_mono hred_mono hsep
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        ‖z‖ ≤
          20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
      hsum_eq.symm
      hinterval

/-- An explicitly empty zero derivative-frequency packet has zero endpoint
contribution. -/
theorem Complex.logarithmicPhaseRealPhase_endpointRightZeroPacketContribution_le_twentyTarget_of_empty
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (hempty :
      Complex.realPhase_secondDerivative_vdc_derivPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b 0 =
        ∅) :
    ‖Complex.realPhase_secondDerivative_vdc_packetSum
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b 0‖ ≤
      20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  have hsum_eq :
      Complex.realPhase_secondDerivative_vdc_packetSum φ a b 0 = 0 :=
    Eq.trans
      (congrArg
        (fun S : Finset ℕ =>
          ∑ n ∈ S, Complex.exp (Complex.I * (φ n : ℂ)))
        hempty)
      Finset.sum_empty
  have htarget_nonneg :
      0 ≤ 20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) :=
    mul_nonneg
      (Nat.cast_nonneg 20)
      (Real.logarithmicPhase_endpoint_sqrt_target_nonneg t ht b)
  have hzero_bound :
      ‖(0 : ℂ)‖ ≤
        20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) :=
    Eq.subst
      (motive := fun left : ℝ =>
        left ≤
          20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
      (norm_zero : ‖(0 : ℂ)‖ = 0).symm
      htarget_nonneg
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        ‖z‖ ≤
          20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
      hsum_eq.symm
      hzero_bound

/-- A nonempty zero derivative-frequency packet is controlled by the
first-derivative endpoint estimate on its terminal interval. -/
theorem Complex.logarithmicPhaseRealPhase_endpointRightZeroPacketContribution_le_twentyTarget_of_nonempty
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hp :
      (Complex.realPhase_secondDerivative_vdc_derivPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b 0).Nonempty) :
    ‖Complex.realPhase_secondDerivative_vdc_packetSum
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b 0‖ ≤
      20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  let packet : Finset ℕ :=
    Complex.realPhase_secondDerivative_vdc_derivPacket φ a b 0
  let c : ℕ := packet.min' hp
  have hc_mem : c ∈ packet :=
    Finset.min'_mem packet hp
  have hc_block : c ∈ Finset.Icc a b :=
    Complex.realPhase_secondDerivative_vdc_derivPacket_mem_block φ hc_mem
  have hc_bounds : a ≤ c ∧ c ≤ b :=
    Finset.mem_Icc.mp hc_block
  have hc_one : 1 ≤ c :=
    le_trans ha hc_bounds.1
  have hpacket :
      Complex.realPhase_secondDerivative_vdc_derivPacket φ a b 0 =
        Finset.Icc c b :=
    Complex.logarithmicPhaseRealPhase_zeroDerivPacket_nonempty_eq_min_Icc
      t ht ht_nonneg ha hp
  have hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        φ c b :=
    Complex.logarithmicPhaseRealPhase_zeroDerivPacket_terminal_integerIncrementMonotoneOn
      t ht_nonneg ha hp
  have hred_mono :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        φ c b :=
    Complex.logarithmicPhaseRealPhase_zeroDerivPacket_terminal_reducedIntegerIncrementMonotoneOn
      t ht ht_nonneg ha hp
  have hsep :
      Complex.realPhase_integerIncrementSeparatedOn
        φ c b
        (‖t‖ / ((b + 1 : ℕ) : ℝ)) :=
    Complex.logarithmicPhaseRealPhase_zeroDerivPacket_terminal_integerIncrementSeparatedOn
      t ht ht_nonneg ha hp
  exact
    Complex.logarithmicPhaseRealPhase_endpointRightZeroPacketContribution_le_twentyTarget_of_terminalInterval
      t ht hc_one hc_bounds.2 hpacket hinc_mono hred_mono hsep

/-- The right endpoint-tail packet family has the endpoint contribution budget. -/
theorem Complex.logarithmicPhaseRealPhase_endpointRightPacket_le_twentyTarget
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a) :
    ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  let packet : Finset ℕ :=
    Complex.realPhase_secondDerivative_vdc_derivPacket φ a b 0
  have hright_to_zero :
      ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets t a b,
          Complex.realPhase_secondDerivative_vdc_packetSum φ a b m‖ ≤
        ‖Complex.realPhase_secondDerivative_vdc_packetSum φ a b 0‖ :=
    Complex.logarithmicPhaseRealPhase_endpointRightPacket_sum_norm_le_zero_packet
      t ht_nonneg ha
  have hzero_budget :
      ‖Complex.realPhase_secondDerivative_vdc_packetSum φ a b 0‖ ≤
        20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
    match packet.eq_empty_or_nonempty with
    | Or.inl hpacket_empty =>
        exact
          Complex.logarithmicPhaseRealPhase_endpointRightZeroPacketContribution_le_twentyTarget_of_empty
            t ht hpacket_empty
    | Or.inr hpacket_nonempty =>
        exact
          Complex.logarithmicPhaseRealPhase_endpointRightZeroPacketContribution_le_twentyTarget_of_nonempty
            t ht ht_nonneg ha hpacket_nonempty
  exact le_trans hright_to_zero hzero_budget

end

end LFunctions
end Boundary
