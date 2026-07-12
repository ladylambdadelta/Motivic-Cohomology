import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.Budgets

/-!
# Direct logarithmic Poisson budget

This is the owner for the exact three-way decomposition of a positive
logarithmic integer block after Poisson reconstruction.  It deliberately
keeps the interior-stationary, endpoint-active, and non-active contributions
separate: the later arithmetic owner must bound these actual quantities,
rather than receiving a packaged analytic witness.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

theorem Finset.sum_const_real_eq_card_mul
    {α : Type*} (s : Finset α) (C : ℝ) :
    (∑ _m ∈ s, C) = (s.card : ℝ) * C := by
  induction s using Finset.induction_on with
  | empty =>
      exact
        Eq.trans
          Finset.sum_empty
          (zero_mul C).symm
  | @insert m s hm ih =>
      have hcard : ((insert m s).card : ℝ) = (s.card : ℝ) + 1 := by
        calc
          ((insert m s).card : ℝ) = ((s.card + 1 : ℕ) : ℝ) :=
            congrArg (fun n : ℕ => (n : ℝ))
              (Finset.card_insert_of_notMem hm)
          _ = (s.card : ℝ) + 1 := Nat.cast_add s.card 1
      calc
        (∑ _x ∈ insert m s, C) = C + ∑ _x ∈ s, C :=
          Finset.sum_insert hm
        _ = C + (s.card : ℝ) * C :=
          congrArg (fun value : ℝ => C + value) ih
        _ = 1 * C + (s.card : ℝ) * C :=
          congrArg (fun value : ℝ => value + (s.card : ℝ) * C)
            (one_mul C).symm
        _ = (1 + (s.card : ℝ)) * C :=
          (add_mul 1 (s.card : ℝ) C).symm
        _ = ((s.card : ℝ) + 1) * C :=
          congrArg (fun value : ℝ => value * C)
            (add_comm 1 (s.card : ℝ))
        _ = ((insert m s).card : ℝ) * C :=
          congrArg (fun value : ℝ => value * C) hcard.symm

def Complex.logarithmicPhasePoissonInteriorBudget
    (t : ℝ) (a b : ℤ) (radius : ℝ) : ℝ :=
  ∑ m ∈ Complex.logarithmicPhasePoissonInteriorActiveModes t a b radius,
    Complex.logarithmicPhaseInteriorStationaryPacketBound t a b m radius

def Complex.logarithmicPhasePoissonEndpointBudget
    (t : ℝ) (a b : ℤ) (radius : ℝ) : ℝ :=
  ∑ m ∈ Complex.logarithmicPhasePoissonEndpointActiveModes t a b radius,
    ‖Complex.integerBlockFourierPacket
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b m‖

def Complex.logarithmicPhasePoissonInactiveBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑' m : {m : ℤ // m ∉ Complex.logarithmicPhasePoissonActiveModes t a b},
    ‖Complex.integerBlockFourierPacket
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b m‖

def Complex.logarithmicPhasePoissonThreeComponentBudget
    (t : ℝ) (a b : ℤ) (radius : ℝ) : ℝ :=
  Complex.logarithmicPhasePoissonInteriorBudget t a b radius +
    Complex.logarithmicPhasePoissonEndpointBudget t a b radius +
      Complex.logarithmicPhasePoissonInactiveBudget t a b

theorem Complex.logarithmicPhasePoissonInteriorBudget_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b)
    (radius : ℝ) (hradius : 0 < radius) :
    0 ≤ Complex.logarithmicPhasePoissonInteriorBudget t a b radius := by
  unfold Complex.logarithmicPhasePoissonInteriorBudget
  exact
    Finset.sum_nonneg
      (fun m hm =>
        have hmem :=
          (Complex.mem_logarithmicPhasePoissonInteriorActiveModes_iff
            t a b m radius).mp hm
        have hpacket :=
          Complex.norm_integerBlockFourierPacket_le_active_stationary_explicit
            t ht ht_nonneg a b m ha hab hmem.2.1
            (Complex.logarithmicPhaseFourierStationaryPoint t m) radius
            rfl hradius hmem.2.2.1 hmem.2.2.2
        exact le_trans (norm_nonneg _) hpacket)

theorem Complex.logarithmicPhasePoissonEndpointBudget_nonneg
    (t : ℝ) (a b : ℤ) (radius : ℝ) :
    0 ≤ Complex.logarithmicPhasePoissonEndpointBudget t a b radius := by
  unfold Complex.logarithmicPhasePoissonEndpointBudget
  exact Finset.sum_nonneg (fun m hm => norm_nonneg _)

theorem Complex.logarithmicPhasePoissonInactiveBudget_nonneg
    (t : ℝ) (a b : ℤ) :
    0 ≤ Complex.logarithmicPhasePoissonInactiveBudget t a b := by
  unfold Complex.logarithmicPhasePoissonInactiveBudget
  exact tsum_nonneg (fun m => norm_nonneg _)

theorem Complex.logarithmicPhasePoissonThreeComponentBudget_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b)
    (radius : ℝ) (hradius : 0 < radius) :
    0 ≤ Complex.logarithmicPhasePoissonThreeComponentBudget t a b radius := by
  unfold Complex.logarithmicPhasePoissonThreeComponentBudget
  exact
    add_nonneg
      (add_nonneg
        (Complex.logarithmicPhasePoissonInteriorBudget_nonneg
          t ht ht_nonneg a b ha hab radius hradius)
        (Complex.logarithmicPhasePoissonEndpointBudget_nonneg t a b radius))
      (Complex.logarithmicPhasePoissonInactiveBudget_nonneg t a b)

theorem Complex.norm_logarithmicPhase_integerBlockFourierPacket_tsum_le_directBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b)
    (radius : ℝ) (hradius : 0 < radius) :
    ‖∑' m : ℤ,
        Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      Complex.logarithmicPhasePoissonThreeComponentBudget t a b radius := by
  have hbudget :=
    Complex.norm_logarithmicPhase_integerBlockFourierPacket_tsum_norm_le_three_component_budget
      t ht ht_nonneg a b ha hab radius hradius
  exact hbudget

theorem Complex.logarithmicPhase_integerBlock_norm_le_directBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b)
    (radius : ℝ) (hradius : 0 < radius) :
    ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
              t (n : ℝ) : ℂ))‖ ≤
      Complex.logarithmicPhasePoissonThreeComponentBudget t a b radius := by
  have hreconstruction :=
    Complex.logarithmicPhase_integerBlock_poisson_packet_reconstruction
      t a b ha hab
  have hpacket :=
    Complex.norm_logarithmicPhase_integerBlockFourierPacket_tsum_le_directBudget
      t ht ht_nonneg a b ha hab radius hradius
  calc
    ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
              t (n : ℝ) : ℂ))‖ =
        ‖∑' m : ℤ,
          Complex.integerBlockFourierPacket
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b m‖ :=
      congrArg norm hreconstruction
    _ ≤ Complex.logarithmicPhasePoissonThreeComponentBudget t a b radius :=
      hpacket

theorem Complex.logarithmicPhasePoissonThreeComponentBudget_eq
    (t : ℝ) (a b : ℤ) (radius : ℝ) :
    Complex.logarithmicPhasePoissonThreeComponentBudget t a b radius =
      (∑ m ∈ Complex.logarithmicPhasePoissonInteriorActiveModes t a b radius,
        Complex.logarithmicPhaseInteriorStationaryPacketBound t a b m radius) +
      (∑ m ∈ Complex.logarithmicPhasePoissonEndpointActiveModes t a b radius,
        ‖Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖) +
      ∑' m : {m : ℤ // m ∉ Complex.logarithmicPhasePoissonActiveModes t a b},
        ‖Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ :=
  rfl

theorem Complex.logarithmicPhasePoissonThreeComponentBudget_upper_of_components
    (t : ℝ) (a b : ℤ) (radius A E N : ℝ)
    (hinterior :
      Complex.logarithmicPhasePoissonInteriorBudget t a b radius ≤ A)
    (hendpoint :
      Complex.logarithmicPhasePoissonEndpointBudget t a b radius ≤ E)
    (hinactive :
      Complex.logarithmicPhasePoissonInactiveBudget t a b ≤ N) :
    Complex.logarithmicPhasePoissonThreeComponentBudget t a b radius ≤
      A + E + N := by
  unfold Complex.logarithmicPhasePoissonThreeComponentBudget
  exact
    add_le_add
      (add_le_add hinterior hendpoint)
      hinactive

theorem Complex.logarithmicPhase_integerBlock_norm_le_of_directBudget_components
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b)
    (radius A E N : ℝ) (hradius : 0 < radius)
    (hinterior :
      Complex.logarithmicPhasePoissonInteriorBudget t a b radius ≤ A)
    (hendpoint :
      Complex.logarithmicPhasePoissonEndpointBudget t a b radius ≤ E)
    (hinactive :
      Complex.logarithmicPhasePoissonInactiveBudget t a b ≤ N) :
    ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
              t (n : ℝ) : ℂ))‖ ≤
      A + E + N := by
  have hpacket :=
    Complex.logarithmicPhase_integerBlock_norm_le_directBudget
      t ht ht_nonneg a b ha hab radius hradius
  have hcomponents :=
    Complex.logarithmicPhasePoissonThreeComponentBudget_upper_of_components
      t a b radius A E N hinterior hendpoint hinactive
  exact le_trans hpacket hcomponents

theorem Complex.logarithmicPhasePoissonInteriorBudget_upper_of_pointwise_bound
    (t : ℝ) (a b : ℤ) (radius C : ℝ)
    (hbound :
      ∀ m : ℤ,
        m ∈ Complex.logarithmicPhasePoissonInteriorActiveModes t a b radius →
          Complex.logarithmicPhaseInteriorStationaryPacketBound t a b m radius ≤ C) :
    Complex.logarithmicPhasePoissonInteriorBudget t a b radius ≤
      ((Complex.logarithmicPhasePoissonInteriorActiveModes t a b radius).card : ℝ) * C := by
  unfold Complex.logarithmicPhasePoissonInteriorBudget
  have hsum :=
    Finset.sum_le_sum
      (fun m hm => hbound m hm)
  have hconstant :
      (∑ m ∈ Complex.logarithmicPhasePoissonInteriorActiveModes t a b radius,
        C) =
        ((Complex.logarithmicPhasePoissonInteriorActiveModes t a b radius).card : ℝ) * C := by
    exact
      Finset.sum_const_real_eq_card_mul
        (Complex.logarithmicPhasePoissonInteriorActiveModes t a b radius) C
  exact hsum.trans_eq hconstant

theorem Complex.logarithmicPhasePoissonEndpointBudget_upper_of_pointwise_bound
    (t : ℝ) (a b : ℤ) (radius C : ℝ)
    (hbound :
      ∀ m : ℤ,
        m ∈ Complex.logarithmicPhasePoissonEndpointActiveModes t a b radius →
          ‖Complex.integerBlockFourierPacket
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b m‖ ≤ C) :
    Complex.logarithmicPhasePoissonEndpointBudget t a b radius ≤
      ((Complex.logarithmicPhasePoissonEndpointActiveModes t a b radius).card : ℝ) * C := by
  unfold Complex.logarithmicPhasePoissonEndpointBudget
  have hsum :=
    Finset.sum_le_sum
      (fun m hm => hbound m hm)
  have hconstant :
      (∑ m ∈ Complex.logarithmicPhasePoissonEndpointActiveModes t a b radius,
        C) =
        ((Complex.logarithmicPhasePoissonEndpointActiveModes t a b radius).card : ℝ) * C := by
    exact
      Finset.sum_const_real_eq_card_mul
        (Complex.logarithmicPhasePoissonEndpointActiveModes t a b radius) C
  exact hsum.trans_eq hconstant

end
end LFunctions
end Boundary
