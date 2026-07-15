import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicFiniteInactiveWindowPartition

/-!
# Hybrid stationary/nonstationary finite inactive budget

Near-endpoint finite inactive modes use clipped balanced stationary windows.
Far modes use monotone reciprocal endpoint gaps.  This owner proves the
quantitative packet bounds for all four classes and recombines them into an
exact finite inactive budget.
-/

namespace Boundary
namespace LFunctions

noncomputable section

private theorem hybrid_two_add_two_eq_four :
    (2 : ℝ) + 2 = 4 := by
  have hcast : ((2 : ℕ) : ℝ) + ((2 : ℕ) : ℝ) = ((4 : ℕ) : ℝ) :=
    Eq.trans (Nat.cast_add 2 2).symm
      (congrArg (fun n : ℕ => (n : ℝ)) rfl)
  exact Eq.trans
    (congrArg₂ (fun left right : ℝ => left + right)
      (Nat.cast_eq_ofNat (n := 2)).symm
      (Nat.cast_eq_ofNat (n := 2)).symm)
    (Eq.trans hcast (Nat.cast_eq_ofNat (n := 4)))

def Complex.logarithmicPhaseFiniteLeftNearBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑ m ∈ Complex.logarithmicPhaseFiniteLeftNearEndpointModes t a b,
    Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget t a b m

def Complex.logarithmicPhaseFiniteRightNearBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑ m ∈ Complex.logarithmicPhaseFiniteRightNearEndpointModes t a b,
    Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget t a b m

def Complex.logarithmicPhaseFiniteLeftFarBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑ m ∈ Complex.logarithmicPhaseFiniteLeftFarModes t a b,
    Complex.logarithmicPhaseFiniteLeftPrincipalEndpointPacketBudget t a m

def Complex.logarithmicPhaseFiniteRightFarBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑ m ∈ Complex.logarithmicPhaseFiniteRightFarModes t a b,
    Complex.logarithmicPhaseFiniteRightPrincipalEndpointPacketBudget t b m

def Complex.logarithmicPhaseFiniteInactiveHybridBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  Complex.logarithmicPhaseFiniteLeftNearBudget t a b +
    Complex.logarithmicPhaseFiniteRightNearBudget t a b +
      Complex.logarithmicPhaseFiniteLeftFarBudget t a b +
        Complex.logarithmicPhaseFiniteRightFarBudget t a b

theorem Complex.norm_logarithmicPhaseQuantitativeFiniteLeftNearPacket_at_norm_le_universalBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    (a b m : ℤ) (ha : 1 ≤ a) (hab : a ≤ b)
    (hm : m ∈ Complex.logarithmicPhaseFiniteLeftNearEndpointModes ‖t‖ a b) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m‖ ≤
      Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget ‖t‖ a b m := by
  have hnormNonneg : 0 ≤ ‖t‖ := norm_nonneg t
  have hnormNorm : ‖‖t‖‖ = ‖t‖ :=
    Real.norm_of_nonneg hnormNonneg
  have htNorm : 1 ≤ ‖‖t‖‖ :=
    Eq.subst (motive := fun parameterNorm : ℝ => 1 ≤ parameterNorm)
      hnormNorm.symm ht
  have hbase :=
    (Complex.mem_logarithmicPhaseFiniteLeftNearEndpointModes_iff
      ‖t‖ a b m).mp hm
  have hmNeg :=
    ((Complex.mem_logarithmicPhasePoissonLeftInactiveModes_iff
      ‖t‖ a b m).mp hbase.1).2.1
  have horder :=
    Complex.logarithmicPhaseFiniteLeftNear_clippedWindow_order
      ‖t‖ htNorm a b hab hm
  have hprincipal :=
    Complex.norm_logarithmicPhaseBProcessUniversalPrincipal_le
      ‖t‖ htNorm hnormNonneg a b m ha hab hmNeg horder
  unfold Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget
  have hbound :=
    Complex.norm_logarithmicPhaseQuantitativePacket_le_crossings_add_principal
      ‖t‖ a b m ha hab hprincipal
  have hconstant : (2 / 3 : ℝ) ≤ 4 / 3 :=
    div_le_div_of_nonneg_right
      (show (2 : ℝ) ≤ 4 from
        le_trans (le_add_of_nonneg_right (Nat.cast_nonneg 2))
          (le_of_eq hybrid_two_add_two_eq_four))
      (Nat.cast_nonneg 3)
  have hraise := add_le_add_right hconstant
    (Complex.logarithmicPhaseBProcessClippedLeftTailBudget ‖t‖ a m +
        2 * Complex.logarithmicPhaseBProcessRadius ‖t‖ m +
      Complex.logarithmicPhaseBProcessClippedRightTailBudget ‖t‖ b m)
  have hraised := le_trans hbound hraise
  have hreassociate :
      (4 / 3 : ℝ) +
          ((Complex.logarithmicPhaseBProcessClippedLeftTailBudget
                ‖t‖ a m +
              2 * Complex.logarithmicPhaseBProcessRadius ‖t‖ m) +
            Complex.logarithmicPhaseBProcessClippedRightTailBudget
              ‖t‖ b m) =
        ((4 / 3 +
              Complex.logarithmicPhaseBProcessClippedLeftTailBudget
                ‖t‖ a m) +
            2 * Complex.logarithmicPhaseBProcessRadius ‖t‖ m) +
          Complex.logarithmicPhaseBProcessClippedRightTailBudget
            ‖t‖ b m :=
    Real.add_reassociate_four_left _ _ _ _
  exact le_trans hraised (le_of_eq hreassociate)

theorem Complex.norm_logarithmicPhaseQuantitativeFiniteLeftNearPacket_le_universalBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b m : ℤ) (ha : 1 ≤ a) (hab : a ≤ b)
    (hm : m ∈ Complex.logarithmicPhaseFiniteLeftNearEndpointModes t a b) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget t a b m := by
  have hnorm : ‖t‖ = t :=
    Real.norm_of_nonneg ht_nonneg
  have hmAtNorm :
      m ∈ Complex.logarithmicPhaseFiniteLeftNearEndpointModes ‖t‖ a b :=
    Eq.subst
      (motive := fun parameter : ℝ =>
        m ∈ Complex.logarithmicPhaseFiniteLeftNearEndpointModes parameter a b)
      hnorm.symm hm
  have hcanonical :=
    Complex.norm_logarithmicPhaseQuantitativeFiniteLeftNearPacket_at_norm_le_universalBudget
      t ht a b m ha hab hmAtNorm
  exact Eq.subst
    (motive := fun parameter : ℝ =>
      ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket
          parameter a b m‖ ≤
        Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget
          parameter a b m)
    hnorm hcanonical

theorem Complex.norm_logarithmicPhaseQuantitativeFiniteRightNearPacket_at_norm_le_universalBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    (a b m : ℤ) (ha : 1 ≤ a) (hab : a ≤ b)
    (hm : m ∈ Complex.logarithmicPhaseFiniteRightNearEndpointModes ‖t‖ a b) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m‖ ≤
      Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget ‖t‖ a b m := by
  have hnormNonneg : 0 ≤ ‖t‖ := norm_nonneg t
  have hnormNorm : ‖‖t‖‖ = ‖t‖ :=
    Real.norm_of_nonneg hnormNonneg
  have htNorm : 1 ≤ ‖‖t‖‖ :=
    Eq.subst (motive := fun parameterNorm : ℝ => 1 ≤ parameterNorm)
      hnormNorm.symm ht
  have hbase :=
    (Complex.mem_logarithmicPhaseFiniteRightNearEndpointModes_iff
      ‖t‖ a b m).mp hm
  have hmNeg :=
    ((Complex.mem_logarithmicPhasePoissonRightInactiveModes_iff
      ‖t‖ a b m).mp hbase.1).2.1
  have horder :=
    Complex.logarithmicPhaseFiniteRightNear_clippedWindow_order
      ‖t‖ htNorm a b hab hm
  have hprincipal :=
    Complex.norm_logarithmicPhaseBProcessUniversalPrincipal_le
      ‖t‖ htNorm hnormNonneg a b m ha hab hmNeg horder
  unfold Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget
  have hbound :=
    Complex.norm_logarithmicPhaseQuantitativePacket_le_crossings_add_principal
      ‖t‖ a b m ha hab hprincipal
  have hconstant : (2 / 3 : ℝ) ≤ 4 / 3 :=
    div_le_div_of_nonneg_right
      (show (2 : ℝ) ≤ 4 from
        le_trans (le_add_of_nonneg_right (Nat.cast_nonneg 2))
          (le_of_eq hybrid_two_add_two_eq_four))
      (Nat.cast_nonneg 3)
  have hraise := add_le_add_right hconstant
    (Complex.logarithmicPhaseBProcessClippedLeftTailBudget ‖t‖ a m +
        2 * Complex.logarithmicPhaseBProcessRadius ‖t‖ m +
      Complex.logarithmicPhaseBProcessClippedRightTailBudget ‖t‖ b m)
  have hraised := le_trans hbound hraise
  have hreassociate :
      (4 / 3 : ℝ) +
          ((Complex.logarithmicPhaseBProcessClippedLeftTailBudget
                ‖t‖ a m +
              2 * Complex.logarithmicPhaseBProcessRadius ‖t‖ m) +
            Complex.logarithmicPhaseBProcessClippedRightTailBudget
              ‖t‖ b m) =
        ((4 / 3 +
              Complex.logarithmicPhaseBProcessClippedLeftTailBudget
                ‖t‖ a m) +
            2 * Complex.logarithmicPhaseBProcessRadius ‖t‖ m) +
          Complex.logarithmicPhaseBProcessClippedRightTailBudget
            ‖t‖ b m :=
    Real.add_reassociate_four_left _ _ _ _
  exact le_trans hraised (le_of_eq hreassociate)

theorem Complex.norm_logarithmicPhaseQuantitativeFiniteRightNearPacket_le_universalBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b m : ℤ) (ha : 1 ≤ a) (hab : a ≤ b)
    (hm : m ∈ Complex.logarithmicPhaseFiniteRightNearEndpointModes t a b) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget t a b m := by
  have hnorm : ‖t‖ = t :=
    Real.norm_of_nonneg ht_nonneg
  have hmAtNorm :
      m ∈ Complex.logarithmicPhaseFiniteRightNearEndpointModes ‖t‖ a b :=
    Eq.subst
      (motive := fun parameter : ℝ =>
        m ∈ Complex.logarithmicPhaseFiniteRightNearEndpointModes parameter a b)
      hnorm.symm hm
  have hcanonical :=
    Complex.norm_logarithmicPhaseQuantitativeFiniteRightNearPacket_at_norm_le_universalBudget
      t ht a b m ha hab hmAtNorm
  exact Eq.subst
    (motive := fun parameter : ℝ =>
      ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket
          parameter a b m‖ ≤
        Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget
          parameter a b m)
    hnorm hcanonical

theorem Complex.norm_logarithmicPhaseQuantitativeFiniteLeftFarPacket_at_norm_le_endpointBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    (a b m : ℤ) (ha : 1 ≤ a) (hab : a ≤ b)
    (hm : m ∈ Complex.logarithmicPhaseFiniteLeftFarModes ‖t‖ a b) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m‖ ≤
      Complex.logarithmicPhaseFiniteLeftPrincipalEndpointPacketBudget ‖t‖ a m := by
  have hbase :=
    (Complex.mem_logarithmicPhaseFiniteLeftFarModes_iff ‖t‖ a b m).mp hm
  exact
    Complex.norm_logarithmicPhaseQuantitativeFiniteLeftInactivePacket_at_norm_le_principalEndpointBudget
      t ht a b m ha hab hbase.1

theorem Complex.norm_logarithmicPhaseQuantitativeFiniteLeftFarPacket_le_endpointBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b m : ℤ) (ha : 1 ≤ a) (hab : a ≤ b)
    (hm : m ∈ Complex.logarithmicPhaseFiniteLeftFarModes t a b) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      Complex.logarithmicPhaseFiniteLeftPrincipalEndpointPacketBudget t a m := by
  have hnorm : ‖t‖ = t :=
    Real.norm_of_nonneg ht_nonneg
  have hmAtNorm :
      m ∈ Complex.logarithmicPhaseFiniteLeftFarModes ‖t‖ a b :=
    Eq.subst
      (motive := fun parameter : ℝ =>
        m ∈ Complex.logarithmicPhaseFiniteLeftFarModes parameter a b)
      hnorm.symm hm
  have hcanonical :=
    Complex.norm_logarithmicPhaseQuantitativeFiniteLeftFarPacket_at_norm_le_endpointBudget
      t ht a b m ha hab hmAtNorm
  exact Eq.subst
    (motive := fun parameter : ℝ =>
      ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket
          parameter a b m‖ ≤
        Complex.logarithmicPhaseFiniteLeftPrincipalEndpointPacketBudget
          parameter a m)
    hnorm hcanonical

theorem Complex.norm_logarithmicPhaseQuantitativeFiniteRightFarPacket_at_norm_le_endpointBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    (a b m : ℤ) (ha : 1 ≤ a) (hab : a ≤ b)
    (hm : m ∈ Complex.logarithmicPhaseFiniteRightFarModes ‖t‖ a b) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m‖ ≤
      Complex.logarithmicPhaseFiniteRightPrincipalEndpointPacketBudget ‖t‖ b m := by
  have hbase :=
    (Complex.mem_logarithmicPhaseFiniteRightFarModes_iff ‖t‖ a b m).mp hm
  exact
    Complex.norm_logarithmicPhaseQuantitativeFiniteRightInactivePacket_at_norm_le_principalEndpointBudget
      t ht a b m ha hab hbase.1

theorem Complex.norm_logarithmicPhaseQuantitativeFiniteRightFarPacket_le_endpointBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b m : ℤ) (ha : 1 ≤ a) (hab : a ≤ b)
    (hm : m ∈ Complex.logarithmicPhaseFiniteRightFarModes t a b) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      Complex.logarithmicPhaseFiniteRightPrincipalEndpointPacketBudget t b m := by
  have hnorm : ‖t‖ = t :=
    Real.norm_of_nonneg ht_nonneg
  have hmAtNorm :
      m ∈ Complex.logarithmicPhaseFiniteRightFarModes ‖t‖ a b :=
    Eq.subst
      (motive := fun parameter : ℝ =>
        m ∈ Complex.logarithmicPhaseFiniteRightFarModes parameter a b)
      hnorm.symm hm
  have hcanonical :=
    Complex.norm_logarithmicPhaseQuantitativeFiniteRightFarPacket_at_norm_le_endpointBudget
      t ht a b m ha hab hmAtNorm
  exact Eq.subst
    (motive := fun parameter : ℝ =>
      ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket
          parameter a b m‖ ≤
        Complex.logarithmicPhaseFiniteRightPrincipalEndpointPacketBudget
          parameter b m)
    hnorm hcanonical

theorem Complex.logarithmicPhaseFiniteLeftNearBudget_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    0 ≤ Complex.logarithmicPhaseFiniteLeftNearBudget t a b := by
  unfold Complex.logarithmicPhaseFiniteLeftNearBudget
  exact Finset.sum_nonneg (fun m hm =>
    le_trans (norm_nonneg _)
      (Complex.norm_logarithmicPhaseQuantitativeFiniteLeftNearPacket_le_universalBudget
        t ht ht_nonneg a b m ha hab hm))

theorem Complex.logarithmicPhaseFiniteRightNearBudget_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    0 ≤ Complex.logarithmicPhaseFiniteRightNearBudget t a b := by
  unfold Complex.logarithmicPhaseFiniteRightNearBudget
  exact Finset.sum_nonneg (fun m hm =>
    le_trans (norm_nonneg _)
      (Complex.norm_logarithmicPhaseQuantitativeFiniteRightNearPacket_le_universalBudget
        t ht ht_nonneg a b m ha hab hm))

theorem Complex.logarithmicPhaseFiniteLeftFarBudget_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) :
    0 ≤ Complex.logarithmicPhaseFiniteLeftFarBudget t a b := by
  unfold Complex.logarithmicPhaseFiniteLeftFarBudget
  exact Finset.sum_nonneg (fun m hm =>
    Complex.logarithmicPhaseFiniteLeftPrincipalEndpointPacketBudget_nonneg
      t ht a b m ha
      ((Complex.mem_logarithmicPhaseFiniteLeftFarModes_iff t a b m).mp hm).1)

theorem Complex.logarithmicPhaseFiniteRightFarBudget_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    0 ≤ Complex.logarithmicPhaseFiniteRightFarBudget t a b := by
  unfold Complex.logarithmicPhaseFiniteRightFarBudget
  exact Finset.sum_nonneg (fun m hm =>
    Complex.logarithmicPhaseFiniteRightPrincipalEndpointPacketBudget_nonneg
      t ht a b m ha hab
      ((Complex.mem_logarithmicPhaseFiniteRightFarModes_iff t a b m).mp hm).1)

theorem Complex.logarithmicPhaseFiniteInactiveHybridBudget_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    0 ≤ Complex.logarithmicPhaseFiniteInactiveHybridBudget t a b := by
  unfold Complex.logarithmicPhaseFiniteInactiveHybridBudget
  exact add_nonneg
    (add_nonneg
      (add_nonneg
        (Complex.logarithmicPhaseFiniteLeftNearBudget_nonneg
          t ht ht_nonneg a b ha hab)
        (Complex.logarithmicPhaseFiniteRightNearBudget_nonneg
          t ht ht_nonneg a b ha hab))
      (Complex.logarithmicPhaseFiniteLeftFarBudget_nonneg
        t ht a b ha))
    (Complex.logarithmicPhaseFiniteRightFarBudget_nonneg
      t ht a b ha hab)

theorem Complex.logarithmicPhaseBProcessQuantitativeLeftInactiveBudget_at_norm_le_hybridParts
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    Complex.logarithmicPhaseBProcessQuantitativeLeftInactiveBudget ‖t‖ a b ≤
      Complex.logarithmicPhaseFiniteLeftNearBudget ‖t‖ a b +
        Complex.logarithmicPhaseFiniteLeftFarBudget ‖t‖ a b := by
  let near := Complex.logarithmicPhaseFiniteLeftNearEndpointModes ‖t‖ a b
  let far := Complex.logarithmicPhaseFiniteLeftFarModes ‖t‖ a b
  let packetNorm : ℤ → ℝ := fun m =>
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m‖
  have hunion := Complex.logarithmicPhaseFiniteLeftNear_union_far ‖t‖ a b
  have hnearFar : Disjoint near far := by
    exact Finset.disjoint_left.mpr (fun m hnear hfar =>
      have hn := (Complex.mem_logarithmicPhaseFiniteLeftNearEndpointModes_iff
        ‖t‖ a b m).mp hnear
      have hf := (Complex.mem_logarithmicPhaseFiniteLeftFarModes_iff
        ‖t‖ a b m).mp hfar
      (not_lt_of_ge hn.2) hf.2)
  have hsplit :
      (∑ m ∈ near ∪ far, packetNorm m) =
        (∑ m ∈ near, packetNorm m) + ∑ m ∈ far, packetNorm m :=
    Finset.sum_union hnearFar
  have hnear := Finset.sum_le_sum (fun m hm =>
    Complex.norm_logarithmicPhaseQuantitativeFiniteLeftNearPacket_at_norm_le_universalBudget
      t ht a b m ha hab hm)
  have hfar := Finset.sum_le_sum (fun m hm =>
    Complex.norm_logarithmicPhaseQuantitativeFiniteLeftFarPacket_at_norm_le_endpointBudget
      t ht a b m ha hab hm)
  have hsumIdentity :
      (∑ m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes ‖t‖ a b,
          packetNorm m) =
        (∑ m ∈ near, packetNorm m) + ∑ m ∈ far, packetNorm m :=
    Eq.trans
      (congrArg
        (fun modes : Finset ℤ => ∑ m ∈ modes, packetNorm m)
        hunion.symm)
      hsplit
  have hparts := add_le_add hnear hfar
  unfold Complex.logarithmicPhaseBProcessQuantitativeLeftInactiveBudget
  unfold Complex.logarithmicPhaseFiniteLeftNearBudget
  unfold Complex.logarithmicPhaseFiniteLeftFarBudget
  exact Eq.subst
    (motive := fun value : ℝ => value ≤ _)
    hsumIdentity.symm hparts

theorem Complex.logarithmicPhaseBProcessQuantitativeLeftInactiveBudget_le_hybridParts
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    Complex.logarithmicPhaseBProcessQuantitativeLeftInactiveBudget t a b ≤
      Complex.logarithmicPhaseFiniteLeftNearBudget t a b +
        Complex.logarithmicPhaseFiniteLeftFarBudget t a b := by
  have hnorm : ‖t‖ = t :=
    Real.norm_of_nonneg ht_nonneg
  have hcanonical :=
    Complex.logarithmicPhaseBProcessQuantitativeLeftInactiveBudget_at_norm_le_hybridParts
      t ht a b ha hab
  exact Eq.subst
    (motive := fun parameter : ℝ =>
      Complex.logarithmicPhaseBProcessQuantitativeLeftInactiveBudget
          parameter a b ≤
        Complex.logarithmicPhaseFiniteLeftNearBudget parameter a b +
          Complex.logarithmicPhaseFiniteLeftFarBudget parameter a b)
    hnorm hcanonical

theorem Complex.logarithmicPhaseBProcessQuantitativeRightInactiveBudget_at_norm_le_hybridParts
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    Complex.logarithmicPhaseBProcessQuantitativeRightInactiveBudget ‖t‖ a b ≤
      Complex.logarithmicPhaseFiniteRightNearBudget ‖t‖ a b +
        Complex.logarithmicPhaseFiniteRightFarBudget ‖t‖ a b := by
  let near := Complex.logarithmicPhaseFiniteRightNearEndpointModes ‖t‖ a b
  let far := Complex.logarithmicPhaseFiniteRightFarModes ‖t‖ a b
  let packetNorm : ℤ → ℝ := fun m =>
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m‖
  have hunion := Complex.logarithmicPhaseFiniteRightNear_union_far ‖t‖ a b
  have hnearFar : Disjoint near far := by
    exact Finset.disjoint_left.mpr (fun m hnear hfar =>
      have hn := (Complex.mem_logarithmicPhaseFiniteRightNearEndpointModes_iff
        ‖t‖ a b m).mp hnear
      have hf := (Complex.mem_logarithmicPhaseFiniteRightFarModes_iff
        ‖t‖ a b m).mp hfar
      (not_lt_of_ge hn.2) hf.2)
  have hsplit :
      (∑ m ∈ near ∪ far, packetNorm m) =
        (∑ m ∈ near, packetNorm m) + ∑ m ∈ far, packetNorm m :=
    Finset.sum_union hnearFar
  have hnear := Finset.sum_le_sum (fun m hm =>
    Complex.norm_logarithmicPhaseQuantitativeFiniteRightNearPacket_at_norm_le_universalBudget
      t ht a b m ha hab hm)
  have hfar := Finset.sum_le_sum (fun m hm =>
    Complex.norm_logarithmicPhaseQuantitativeFiniteRightFarPacket_at_norm_le_endpointBudget
      t ht a b m ha hab hm)
  have hsumIdentity :
      (∑ m ∈ Complex.logarithmicPhasePoissonRightInactiveModes ‖t‖ a b,
          packetNorm m) =
        (∑ m ∈ near, packetNorm m) + ∑ m ∈ far, packetNorm m :=
    Eq.trans
      (congrArg
        (fun modes : Finset ℤ => ∑ m ∈ modes, packetNorm m)
        hunion.symm)
      hsplit
  have hparts := add_le_add hnear hfar
  unfold Complex.logarithmicPhaseBProcessQuantitativeRightInactiveBudget
  unfold Complex.logarithmicPhaseFiniteRightNearBudget
  unfold Complex.logarithmicPhaseFiniteRightFarBudget
  exact Eq.subst
    (motive := fun value : ℝ => value ≤ _)
    hsumIdentity.symm hparts

theorem Complex.logarithmicPhaseBProcessQuantitativeRightInactiveBudget_le_hybridParts
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    Complex.logarithmicPhaseBProcessQuantitativeRightInactiveBudget t a b ≤
      Complex.logarithmicPhaseFiniteRightNearBudget t a b +
        Complex.logarithmicPhaseFiniteRightFarBudget t a b := by
  have hnorm : ‖t‖ = t :=
    Real.norm_of_nonneg ht_nonneg
  have hcanonical :=
    Complex.logarithmicPhaseBProcessQuantitativeRightInactiveBudget_at_norm_le_hybridParts
      t ht a b ha hab
  exact Eq.subst
    (motive := fun parameter : ℝ =>
      Complex.logarithmicPhaseBProcessQuantitativeRightInactiveBudget
          parameter a b ≤
        Complex.logarithmicPhaseFiniteRightNearBudget parameter a b +
          Complex.logarithmicPhaseFiniteRightFarBudget parameter a b)
    hnorm hcanonical

theorem Complex.logarithmicPhaseFiniteInactivePacketBudgets_at_norm_le_hybridBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    Complex.logarithmicPhaseBProcessQuantitativeLeftInactiveBudget ‖t‖ a b +
        Complex.logarithmicPhaseBProcessQuantitativeRightInactiveBudget ‖t‖ a b ≤
      Complex.logarithmicPhaseFiniteInactiveHybridBudget ‖t‖ a b := by
  have hleft :=
    Complex.logarithmicPhaseBProcessQuantitativeLeftInactiveBudget_at_norm_le_hybridParts
      t ht a b ha hab
  have hright :=
    Complex.logarithmicPhaseBProcessQuantitativeRightInactiveBudget_at_norm_le_hybridParts
      t ht a b ha hab
  unfold Complex.logarithmicPhaseFiniteInactiveHybridBudget
  have hadd := add_le_add hleft hright
  have hreassociate :
      (Complex.logarithmicPhaseFiniteLeftNearBudget ‖t‖ a b +
          Complex.logarithmicPhaseFiniteLeftFarBudget ‖t‖ a b) +
        (Complex.logarithmicPhaseFiniteRightNearBudget ‖t‖ a b +
          Complex.logarithmicPhaseFiniteRightFarBudget ‖t‖ a b) =
        Complex.logarithmicPhaseFiniteLeftNearBudget ‖t‖ a b +
            Complex.logarithmicPhaseFiniteRightNearBudget ‖t‖ a b +
          Complex.logarithmicPhaseFiniteLeftFarBudget ‖t‖ a b +
        Complex.logarithmicPhaseFiniteRightFarBudget ‖t‖ a b :=
    Eq.trans
      (add_add_add_comm
        (Complex.logarithmicPhaseFiniteLeftNearBudget ‖t‖ a b)
        (Complex.logarithmicPhaseFiniteLeftFarBudget ‖t‖ a b)
        (Complex.logarithmicPhaseFiniteRightNearBudget ‖t‖ a b)
        (Complex.logarithmicPhaseFiniteRightFarBudget ‖t‖ a b))
      (add_assoc
        (Complex.logarithmicPhaseFiniteLeftNearBudget ‖t‖ a b +
          Complex.logarithmicPhaseFiniteRightNearBudget ‖t‖ a b)
        (Complex.logarithmicPhaseFiniteLeftFarBudget ‖t‖ a b)
        (Complex.logarithmicPhaseFiniteRightFarBudget ‖t‖ a b)).symm
  exact le_trans hadd
    (le_of_eq hreassociate)

theorem Complex.logarithmicPhaseFiniteInactivePacketBudgets_le_hybridBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    Complex.logarithmicPhaseBProcessQuantitativeLeftInactiveBudget t a b +
        Complex.logarithmicPhaseBProcessQuantitativeRightInactiveBudget t a b ≤
      Complex.logarithmicPhaseFiniteInactiveHybridBudget t a b := by
  have hnorm : ‖t‖ = t :=
    Real.norm_of_nonneg ht_nonneg
  have hcanonical :=
    Complex.logarithmicPhaseFiniteInactivePacketBudgets_at_norm_le_hybridBudget
      t ht a b ha hab
  exact Eq.subst
    (motive := fun parameter : ℝ =>
      Complex.logarithmicPhaseBProcessQuantitativeLeftInactiveBudget
          parameter a b +
          Complex.logarithmicPhaseBProcessQuantitativeRightInactiveBudget
            parameter a b ≤
        Complex.logarithmicPhaseFiniteInactiveHybridBudget parameter a b)
    hnorm hcanonical

end

end LFunctions
end Boundary
