import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativeBudget
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativeGlobalBudget

/-!
# Three-component quantitative B-process budget

This owner splits the exact quantitative frequency sum into the finite active
stationary family and its complement.  The active family is further split into
canonical interior windows and endpoint packets.  The complement is controlled
by the deterministic mode majorant.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

def Complex.logarithmicPhaseQuantitativeActiveWindowBudget
    (t : ℝ) (a b : ℤ) (radius : ℝ) : ℝ :=
  ∑ m ∈ Complex.logarithmicPhasePoissonInteriorActiveModes t a b radius,
    Complex.logarithmicPhaseQuantitativeInteriorStationaryPacketBound
      t a b m radius

def Complex.logarithmicPhaseQuantitativeCrossingBudget
    (t : ℝ) (a b : ℤ) (radius : ℝ) : ℝ :=
  ∑ m ∈ Complex.logarithmicPhasePoissonEndpointActiveModes t a b radius,
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖

def Complex.logarithmicPhaseQuantitativeComplementTailBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑' m : {m : ℤ //
      m ∉ Complex.logarithmicPhasePoissonActiveModes t a b},
    Complex.logarithmicPhaseQuantitativeModeMajorant t a b m

def Complex.logarithmicPhaseQuantitativeThreeComponentBudget
    (t : ℝ) (a b : ℤ) (radius : ℝ) : ℝ :=
  Complex.logarithmicPhaseQuantitativeActiveWindowBudget t a b radius +
    Complex.logarithmicPhaseQuantitativeCrossingBudget t a b radius +
      Complex.logarithmicPhaseQuantitativeComplementTailBudget t a b

theorem Complex.logarithmicPhaseQuantitativeActiveWindowBudget_nonneg
    (t : ℝ) (a b : ℤ) (radius : ℝ)
    (hbound :
      ∀ m ∈ Complex.logarithmicPhasePoissonInteriorActiveModes t a b radius,
        0 ≤ Complex.logarithmicPhaseQuantitativeInteriorStationaryPacketBound
          t a b m radius) :
    0 ≤ Complex.logarithmicPhaseQuantitativeActiveWindowBudget t a b radius := by
  unfold Complex.logarithmicPhaseQuantitativeActiveWindowBudget
  exact Finset.sum_nonneg (fun m hm => hbound m hm)

theorem Complex.logarithmicPhaseQuantitativeCrossingBudget_nonneg
    (t : ℝ) (a b : ℤ) (radius : ℝ) :
    0 ≤ Complex.logarithmicPhaseQuantitativeCrossingBudget t a b radius := by
  unfold Complex.logarithmicPhaseQuantitativeCrossingBudget
  exact Finset.sum_nonneg (fun m hm => norm_nonneg _)

theorem Complex.logarithmicPhaseQuantitativeComplementTailBudget_nonneg
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    0 ≤ Complex.logarithmicPhaseQuantitativeComplementTailBudget t a b := by
  unfold Complex.logarithmicPhaseQuantitativeComplementTailBudget
  exact tsum_nonneg (fun m =>
    Complex.logarithmicPhaseQuantitativeModeMajorant_nonneg
      t a b m ha hab)

theorem Complex.logarithmicPhaseQuantitativeThreeComponentBudget_nonneg
    (t : ℝ) (a b : ℤ) (radius : ℝ)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hactive :
      ∀ m ∈ Complex.logarithmicPhasePoissonInteriorActiveModes t a b radius,
        0 ≤ Complex.logarithmicPhaseQuantitativeInteriorStationaryPacketBound
          t a b m radius) :
    0 ≤ Complex.logarithmicPhaseQuantitativeThreeComponentBudget
      t a b radius := by
  unfold Complex.logarithmicPhaseQuantitativeThreeComponentBudget
  exact add_nonneg
    (add_nonneg
      (Complex.logarithmicPhaseQuantitativeActiveWindowBudget_nonneg
        t a b radius hactive)
      (Complex.logarithmicPhaseQuantitativeCrossingBudget_nonneg
        t a b radius))
    (Complex.logarithmicPhaseQuantitativeComplementTailBudget_nonneg
      t a b ha hab)

theorem Complex.summable_logarithmicPhaseQuantitativeComplementModeMajorant
    (t : ℝ) (a b : ℤ) :
    Summable
      (fun m : {m : ℤ //
          m ∉ Complex.logarithmicPhasePoissonActiveModes t a b} =>
        Complex.logarithmicPhaseQuantitativeModeMajorant t a b m) := by
  exact
    (Complex.summable_logarithmicPhaseQuantitativeModeMajorant t a b).subtype
      {m : ℤ | m ∉ Complex.logarithmicPhasePoissonActiveModes t a b}

theorem Complex.logarithmicPhaseQuantitativePacket_tsum_eq_active_add_complement
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a) :
    (∑' m : ℤ,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m) =
      (∑' m : {m : ℤ //
          m ∈ Complex.logarithmicPhasePoissonActiveModes t a b},
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m) +
      (∑' m : {m : ℤ //
          m ∉ Complex.logarithmicPhasePoissonActiveModes t a b},
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m) := by
  have hsummable :=
    Complex.summable_logarithmicPhaseQuantitativeBlockFourierPacket
      t a b ha
  let activeSet : Set ℤ :=
    {m : ℤ | m ∈ Complex.logarithmicPhasePoissonActiveModes t a b}
  have hsplit :=
    tsum_subtype_add_tsum_subtype_compl hsummable activeSet
  have hcomplement :
      (activeSetᶜ : Set ℤ) =
        {m : ℤ | m ∉ Complex.logarithmicPhasePoissonActiveModes t a b} := by
    ext m
    rfl
  exact hsplit.symm.trans
    (congrArg₂ (fun first second : ℂ => first + second)
      rfl
      (Eq.subst
        (motive := fun modes : Set ℤ =>
          (∑' m : modes,
            Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m) =
          (∑' m : {m : ℤ //
              m ∉ Complex.logarithmicPhasePoissonActiveModes t a b},
            Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m))
        hcomplement
        rfl))

theorem Complex.norm_logarithmicPhaseQuantitativeComplementPacket_tsum_le_budget
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (htNonneg : 0 ≤ t)
    (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    ‖∑' m : {m : ℤ //
        m ∉ Complex.logarithmicPhasePoissonActiveModes t a b},
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      Complex.logarithmicPhaseQuantitativeComplementTailBudget t a b := by
  have hsummable :=
    Complex.summable_logarithmicPhaseQuantitativeComplementModeMajorant
      t a b
  have hpointwise :
      ∀ m : {m : ℤ //
          m ∉ Complex.logarithmicPhasePoissonActiveModes t a b},
        ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
          Complex.logarithmicPhaseQuantitativeModeMajorant t a b m :=
    fun m =>
      Complex.norm_logarithmicPhaseQuantitativePacket_le_modeMajorant
        t ht htNonneg a b m ha hab
  unfold Complex.logarithmicPhaseQuantitativeComplementTailBudget
  exact tsum_norm_le hsummable hpointwise

theorem Complex.norm_logarithmicPhaseQuantitativeActivePacket_tsum_le_two_components
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (htNonneg : 0 ≤ t)
    (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (radius : ℝ)
    (hradius : 0 < radius) :
    ‖∑' m : {m : ℤ //
        m ∈ Complex.logarithmicPhasePoissonActiveModes t a b},
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      Complex.logarithmicPhaseQuantitativeActiveWindowBudget t a b radius +
        Complex.logarithmicPhaseQuantitativeCrossingBudget t a b radius := by
  exact
    Complex.norm_logarithmicPhaseQuantitative_activePacket_tsum_le_interior_add_endpoint
      t ht htNonneg a b ha hab radius hradius

theorem Complex.norm_logarithmicPhaseQuantitativePacket_tsum_le_threeComponentBudget
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (htNonneg : 0 ≤ t)
    (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (radius : ℝ)
    (hradius : 0 < radius) :
    ‖∑' m : ℤ,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      Complex.logarithmicPhaseQuantitativeThreeComponentBudget
        t a b radius := by
  have hsplit :=
    Complex.logarithmicPhaseQuantitativePacket_tsum_eq_active_add_complement
      t a b ha
  have hactive :=
    Complex.norm_logarithmicPhaseQuantitativeActivePacket_tsum_le_two_components
      t ht htNonneg a b ha hab radius hradius
  have hcomplement :=
    Complex.norm_logarithmicPhaseQuantitativeComplementPacket_tsum_le_budget
      t ht htNonneg a b ha hab
  unfold Complex.logarithmicPhaseQuantitativeThreeComponentBudget
  calc
    ‖∑' m : ℤ,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ =
      ‖(∑' m : {m : ℤ //
          m ∈ Complex.logarithmicPhasePoissonActiveModes t a b},
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m) +
        (∑' m : {m : ℤ //
          m ∉ Complex.logarithmicPhasePoissonActiveModes t a b},
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m)‖ :=
      congrArg norm hsplit
    _ ≤
      ‖∑' m : {m : ℤ //
          m ∈ Complex.logarithmicPhasePoissonActiveModes t a b},
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ +
        ‖∑' m : {m : ℤ //
          m ∉ Complex.logarithmicPhasePoissonActiveModes t a b},
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ :=
      norm_add_le _ _
    _ ≤
      (Complex.logarithmicPhaseQuantitativeActiveWindowBudget t a b radius +
        Complex.logarithmicPhaseQuantitativeCrossingBudget t a b radius) +
          Complex.logarithmicPhaseQuantitativeComplementTailBudget t a b :=
      add_le_add hactive hcomplement

theorem Complex.logarithmicPhaseQuantitativeIntegerBlock_norm_le_threeComponentBudget
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (htNonneg : 0 ≤ t)
    (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (radius : ℝ)
    (hradius : 0 < radius) :
    ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
              t (n : ℝ) : ℂ))‖ ≤
      Complex.logarithmicPhaseQuantitativeThreeComponentBudget
        t a b radius := by
  have hreconstruction :=
    Complex.logarithmicPhase_quantitativeBlock_poisson_packet_reconstruction
      t a b ha hab
  have hpacket :=
    Complex.norm_logarithmicPhaseQuantitativePacket_tsum_le_threeComponentBudget
      t ht htNonneg a b ha hab radius hradius
  exact le_trans (le_of_eq (congrArg norm hreconstruction)) hpacket

end
end LFunctions
end Boundary
