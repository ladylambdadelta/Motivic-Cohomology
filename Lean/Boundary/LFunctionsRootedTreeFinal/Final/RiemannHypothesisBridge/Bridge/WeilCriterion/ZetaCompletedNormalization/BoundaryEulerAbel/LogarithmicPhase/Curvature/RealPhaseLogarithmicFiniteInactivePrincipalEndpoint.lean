import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicZeroModeArithmetic
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.BProcessOutsideEndpointPackets

/-!
# Principal-endpoint estimates for finite inactive packets

Finite inactive centers lie beyond the full cutoff support and hence beyond the
principal interval.  Their principal oscillatory integrals are controlled by
twice the reciprocal derivative gap at `a` or `b`.  The quantitative cutoff
then contributes only its proved `2/3` crossing term.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseFiniteLeftPrincipalEndpointPacketBudget
    (t : ℝ) (a m : ℤ) : ℝ :=
  2 / 3 +
    Complex.logarithmicPhaseRightReciprocalGap t m (a : ℝ) +
      Complex.logarithmicPhaseRightReciprocalGap t m (a : ℝ)

def Complex.logarithmicPhaseFiniteRightPrincipalEndpointPacketBudget
    (t : ℝ) (b m : ℤ) : ℝ :=
  2 / 3 +
    Complex.logarithmicPhaseLeftReciprocalGap t m (b : ℝ) +
      Complex.logarithmicPhaseLeftReciprocalGap t m (b : ℝ)

def Complex.logarithmicPhaseFiniteLeftPrincipalEndpointBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑ m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b,
    Complex.logarithmicPhaseFiniteLeftPrincipalEndpointPacketBudget t a m

def Complex.logarithmicPhaseFiniteRightPrincipalEndpointBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑ m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b,
    Complex.logarithmicPhaseFiniteRightPrincipalEndpointPacketBudget t b m

def Complex.logarithmicPhaseFiniteInactivePrincipalEndpointBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  Complex.logarithmicPhaseFiniteLeftPrincipalEndpointBudget t a b +
    Complex.logarithmicPhaseFiniteRightPrincipalEndpointBudget t a b

theorem Complex.norm_logarithmicPhaseFiniteLeftInactivePrincipal_at_norm_le_endpointBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    (a b m : ℤ) (ha : 1 ≤ a) (hab : a ≤ b)
    (hm : m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes ‖t‖ a b) :
    ‖∫ x in (a : ℝ)..(b : ℝ),
        Complex.realPhaseOscillation
          (Complex.realPhaseFrequencyTwist
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase ‖t‖)
            m) x‖ ≤
      Complex.logarithmicPhaseRightReciprocalGap ‖t‖ m (a : ℝ) +
        Complex.logarithmicPhaseRightReciprocalGap ‖t‖ m (a : ℝ) := by
  have hnormNonneg : 0 ≤ ‖t‖ := norm_nonneg t
  have hnormNorm : ‖‖t‖‖ = ‖t‖ :=
    Real.norm_of_nonneg hnormNonneg
  have htNorm : 1 ≤ ‖‖t‖‖ :=
    Eq.subst (motive := fun parameterNorm : ℝ => 1 ≤ parameterNorm)
      hnormNorm.symm ht
  have hdata :=
    (Complex.mem_logarithmicPhasePoissonLeftInactiveModes_iff
      ‖t‖ a b m).mp hm
  have hmNeg := hdata.2.1
  have hcenter := hdata.2.2
  have haPos : 0 < (a : ℝ) :=
    Int.cast_pos.mpr (lt_of_lt_of_le Int.zero_lt_one ha)
  have habReal : (a : ℝ) ≤ (b : ℝ) := Int.cast_le.mpr hab
  exact
    Complex.norm_intervalIntegral_logarithmicPhase_rightOfStationary_le_twice_reciprocalGap
      ‖t‖ htNorm hnormNonneg m hmNeg (a : ℝ) (b : ℝ)
      haPos habReal hcenter

theorem Complex.norm_logarithmicPhaseFiniteLeftInactivePrincipal_le_endpointBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b m : ℤ) (ha : 1 ≤ a) (hab : a ≤ b)
    (hm : m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b) :
    ‖∫ x in (a : ℝ)..(b : ℝ),
        Complex.realPhaseOscillation
          (Complex.realPhaseFrequencyTwist
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            m) x‖ ≤
      Complex.logarithmicPhaseRightReciprocalGap t m (a : ℝ) +
        Complex.logarithmicPhaseRightReciprocalGap t m (a : ℝ) := by
  have hnorm : ‖t‖ = t :=
    Real.norm_of_nonneg ht_nonneg
  have hmAtNorm :
      m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes ‖t‖ a b :=
    Eq.subst
      (motive := fun parameter : ℝ =>
        m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes parameter a b)
      hnorm.symm hm
  have hcanonical :=
    Complex.norm_logarithmicPhaseFiniteLeftInactivePrincipal_at_norm_le_endpointBudget
      t ht a b m ha hab hmAtNorm
  exact Eq.subst
    (motive := fun parameter : ℝ =>
      ‖∫ x in (a : ℝ)..(b : ℝ),
          Complex.realPhaseOscillation
            (Complex.realPhaseFrequencyTwist
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                parameter)
              m) x‖ ≤
        Complex.logarithmicPhaseRightReciprocalGap parameter m (a : ℝ) +
          Complex.logarithmicPhaseRightReciprocalGap parameter m (a : ℝ))
    hnorm hcanonical

theorem Complex.norm_logarithmicPhaseFiniteRightInactivePrincipal_at_norm_le_endpointBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    (a b m : ℤ) (ha : 1 ≤ a) (hab : a ≤ b)
    (hm : m ∈ Complex.logarithmicPhasePoissonRightInactiveModes ‖t‖ a b) :
    ‖∫ x in (a : ℝ)..(b : ℝ),
        Complex.realPhaseOscillation
          (Complex.realPhaseFrequencyTwist
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase ‖t‖)
            m) x‖ ≤
      Complex.logarithmicPhaseLeftReciprocalGap ‖t‖ m (b : ℝ) +
        Complex.logarithmicPhaseLeftReciprocalGap ‖t‖ m (b : ℝ) := by
  have hnormNonneg : 0 ≤ ‖t‖ := norm_nonneg t
  have hnormNorm : ‖‖t‖‖ = ‖t‖ :=
    Real.norm_of_nonneg hnormNonneg
  have htNorm : 1 ≤ ‖‖t‖‖ :=
    Eq.subst (motive := fun parameterNorm : ℝ => 1 ≤ parameterNorm)
      hnormNorm.symm ht
  have hdata :=
    (Complex.mem_logarithmicPhasePoissonRightInactiveModes_iff
      ‖t‖ a b m).mp hm
  have hmNeg := hdata.2.1
  have hcenter := hdata.2.2
  have haPos : 0 < (a : ℝ) :=
    Int.cast_pos.mpr (lt_of_lt_of_le Int.zero_lt_one ha)
  have habReal : (a : ℝ) ≤ (b : ℝ) := Int.cast_le.mpr hab
  exact
    Complex.norm_intervalIntegral_logarithmicPhase_leftOfStationary_le_twice_reciprocalGap
      ‖t‖ htNorm hnormNonneg m hmNeg (a : ℝ) (b : ℝ)
      haPos habReal hcenter

theorem Complex.norm_logarithmicPhaseFiniteRightInactivePrincipal_le_endpointBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b m : ℤ) (ha : 1 ≤ a) (hab : a ≤ b)
    (hm : m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b) :
    ‖∫ x in (a : ℝ)..(b : ℝ),
        Complex.realPhaseOscillation
          (Complex.realPhaseFrequencyTwist
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            m) x‖ ≤
      Complex.logarithmicPhaseLeftReciprocalGap t m (b : ℝ) +
        Complex.logarithmicPhaseLeftReciprocalGap t m (b : ℝ) := by
  have hnorm : ‖t‖ = t :=
    Real.norm_of_nonneg ht_nonneg
  have hmAtNorm :
      m ∈ Complex.logarithmicPhasePoissonRightInactiveModes ‖t‖ a b :=
    Eq.subst
      (motive := fun parameter : ℝ =>
        m ∈ Complex.logarithmicPhasePoissonRightInactiveModes parameter a b)
      hnorm.symm hm
  have hcanonical :=
    Complex.norm_logarithmicPhaseFiniteRightInactivePrincipal_at_norm_le_endpointBudget
      t ht a b m ha hab hmAtNorm
  exact Eq.subst
    (motive := fun parameter : ℝ =>
      ‖∫ x in (a : ℝ)..(b : ℝ),
          Complex.realPhaseOscillation
            (Complex.realPhaseFrequencyTwist
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                parameter)
              m) x‖ ≤
        Complex.logarithmicPhaseLeftReciprocalGap parameter m (b : ℝ) +
          Complex.logarithmicPhaseLeftReciprocalGap parameter m (b : ℝ))
    hnorm hcanonical

theorem Complex.norm_logarithmicPhaseQuantitativeFiniteLeftInactivePacket_at_norm_le_principalEndpointBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    (a b m : ℤ) (ha : 1 ≤ a) (hab : a ≤ b)
    (hm : m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes ‖t‖ a b) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m‖ ≤
      Complex.logarithmicPhaseFiniteLeftPrincipalEndpointPacketBudget ‖t‖ a m := by
  have hprincipal :=
    Complex.norm_logarithmicPhaseFiniteLeftInactivePrincipal_at_norm_le_endpointBudget
      t ht a b m ha hab hm
  unfold Complex.logarithmicPhaseFiniteLeftPrincipalEndpointPacketBudget
  have hbound :=
    Complex.norm_logarithmicPhaseQuantitativePacket_le_crossings_add_principal
      ‖t‖ a b m ha hab hprincipal
  have hreassociate :
      (2 / 3 : ℝ) +
          (Complex.logarithmicPhaseRightReciprocalGap ‖t‖ m (a : ℝ) +
            Complex.logarithmicPhaseRightReciprocalGap ‖t‖ m (a : ℝ)) =
        2 / 3 +
            Complex.logarithmicPhaseRightReciprocalGap ‖t‖ m (a : ℝ) +
          Complex.logarithmicPhaseRightReciprocalGap ‖t‖ m (a : ℝ) :=
    (add_assoc _ _ _).symm
  exact Eq.subst
    (motive := fun value : ℝ =>
      ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket
          ‖t‖ a b m‖ ≤ value)
    hreassociate hbound

theorem Complex.norm_logarithmicPhaseQuantitativeFiniteLeftInactivePacket_le_principalEndpointBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b m : ℤ) (ha : 1 ≤ a) (hab : a ≤ b)
    (hm : m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      Complex.logarithmicPhaseFiniteLeftPrincipalEndpointPacketBudget t a m := by
  have hnorm : ‖t‖ = t :=
    Real.norm_of_nonneg ht_nonneg
  have hmAtNorm :
      m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes ‖t‖ a b :=
    Eq.subst
      (motive := fun parameter : ℝ =>
        m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes parameter a b)
      hnorm.symm hm
  have hcanonical :=
    Complex.norm_logarithmicPhaseQuantitativeFiniteLeftInactivePacket_at_norm_le_principalEndpointBudget
      t ht a b m ha hab hmAtNorm
  exact Eq.subst
    (motive := fun parameter : ℝ =>
      ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket
          parameter a b m‖ ≤
        Complex.logarithmicPhaseFiniteLeftPrincipalEndpointPacketBudget
          parameter a m)
    hnorm hcanonical

theorem Complex.norm_logarithmicPhaseQuantitativeFiniteRightInactivePacket_at_norm_le_principalEndpointBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    (a b m : ℤ) (ha : 1 ≤ a) (hab : a ≤ b)
    (hm : m ∈ Complex.logarithmicPhasePoissonRightInactiveModes ‖t‖ a b) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m‖ ≤
      Complex.logarithmicPhaseFiniteRightPrincipalEndpointPacketBudget ‖t‖ b m := by
  have hprincipal :=
    Complex.norm_logarithmicPhaseFiniteRightInactivePrincipal_at_norm_le_endpointBudget
      t ht a b m ha hab hm
  unfold Complex.logarithmicPhaseFiniteRightPrincipalEndpointPacketBudget
  have hbound :=
    Complex.norm_logarithmicPhaseQuantitativePacket_le_crossings_add_principal
      ‖t‖ a b m ha hab hprincipal
  have hreassociate :
      (2 / 3 : ℝ) +
          (Complex.logarithmicPhaseLeftReciprocalGap ‖t‖ m (b : ℝ) +
            Complex.logarithmicPhaseLeftReciprocalGap ‖t‖ m (b : ℝ)) =
        2 / 3 +
            Complex.logarithmicPhaseLeftReciprocalGap ‖t‖ m (b : ℝ) +
          Complex.logarithmicPhaseLeftReciprocalGap ‖t‖ m (b : ℝ) :=
    (add_assoc _ _ _).symm
  exact Eq.subst
    (motive := fun value : ℝ =>
      ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket
          ‖t‖ a b m‖ ≤ value)
    hreassociate hbound

theorem Complex.norm_logarithmicPhaseQuantitativeFiniteRightInactivePacket_le_principalEndpointBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b m : ℤ) (ha : 1 ≤ a) (hab : a ≤ b)
    (hm : m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      Complex.logarithmicPhaseFiniteRightPrincipalEndpointPacketBudget t b m := by
  have hnorm : ‖t‖ = t :=
    Real.norm_of_nonneg ht_nonneg
  have hmAtNorm :
      m ∈ Complex.logarithmicPhasePoissonRightInactiveModes ‖t‖ a b :=
    Eq.subst
      (motive := fun parameter : ℝ =>
        m ∈ Complex.logarithmicPhasePoissonRightInactiveModes parameter a b)
      hnorm.symm hm
  have hcanonical :=
    Complex.norm_logarithmicPhaseQuantitativeFiniteRightInactivePacket_at_norm_le_principalEndpointBudget
      t ht a b m ha hab hmAtNorm
  exact Eq.subst
    (motive := fun parameter : ℝ =>
      ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket
          parameter a b m‖ ≤
        Complex.logarithmicPhaseFiniteRightPrincipalEndpointPacketBudget
          parameter b m)
    hnorm hcanonical

theorem Complex.logarithmicPhaseFiniteLeftPrincipalEndpointPacketBudget_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b m : ℤ)
    (ha : 1 ≤ a)
    (hm : m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b) :
    0 ≤ Complex.logarithmicPhaseFiniteLeftPrincipalEndpointPacketBudget t a m := by
  have hdata :=
    (Complex.mem_logarithmicPhasePoissonLeftInactiveModes_iff
      t a b m).mp hm
  have hmNeg := hdata.2.1
  have hcenter := hdata.2.2
  have haPos : 0 < (a : ℝ) :=
    Int.cast_pos.mpr (lt_of_lt_of_le Int.zero_lt_one ha)
  have hgap := Complex.logarithmicPhaseRightReciprocalGap_eq_coefficientNorm
    t ht m hmNeg haPos hcenter
  have hgapNonneg :
      0 ≤ Complex.logarithmicPhaseRightReciprocalGap t m (a : ℝ) :=
    Eq.subst (motive := fun value : ℝ => 0 ≤ value)
      hgap.symm (norm_nonneg _)
  unfold Complex.logarithmicPhaseFiniteLeftPrincipalEndpointPacketBudget
  exact add_nonneg
    (add_nonneg
      (div_nonneg (Nat.cast_nonneg 2) (Nat.cast_nonneg 3))
      hgapNonneg)
    hgapNonneg

theorem Complex.logarithmicPhaseFiniteRightPrincipalEndpointPacketBudget_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b m : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (hm : m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b) :
    0 ≤ Complex.logarithmicPhaseFiniteRightPrincipalEndpointPacketBudget t b m := by
  have hdata :=
    (Complex.mem_logarithmicPhasePoissonRightInactiveModes_iff
      t a b m).mp hm
  have hmNeg := hdata.2.1
  have hcenter := hdata.2.2
  have hb : 1 ≤ b := le_trans ha hab
  have hbPos : 0 < (b : ℝ) :=
    Int.cast_pos.mpr (lt_of_lt_of_le Int.zero_lt_one hb)
  have hgap := Complex.logarithmicPhaseLeftReciprocalGap_eq_coefficientNorm
    t ht m hmNeg hbPos hcenter
  have hgapNonneg :
      0 ≤ Complex.logarithmicPhaseLeftReciprocalGap t m (b : ℝ) :=
    Eq.subst (motive := fun value : ℝ => 0 ≤ value)
      hgap.symm (norm_nonneg _)
  unfold Complex.logarithmicPhaseFiniteRightPrincipalEndpointPacketBudget
  exact add_nonneg
    (add_nonneg
      (div_nonneg (Nat.cast_nonneg 2) (Nat.cast_nonneg 3))
      hgapNonneg)
    hgapNonneg

theorem Complex.logarithmicPhaseFiniteInactivePrincipalEndpointBudget_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    0 ≤ Complex.logarithmicPhaseFiniteInactivePrincipalEndpointBudget t a b := by
  unfold Complex.logarithmicPhaseFiniteInactivePrincipalEndpointBudget
  unfold Complex.logarithmicPhaseFiniteLeftPrincipalEndpointBudget
  unfold Complex.logarithmicPhaseFiniteRightPrincipalEndpointBudget
  exact add_nonneg
    (Finset.sum_nonneg (fun m hm =>
      Complex.logarithmicPhaseFiniteLeftPrincipalEndpointPacketBudget_nonneg
        t ht a b m ha hm))
    (Finset.sum_nonneg (fun m hm =>
      Complex.logarithmicPhaseFiniteRightPrincipalEndpointPacketBudget_nonneg
        t ht a b m ha hab hm))

theorem Complex.logarithmicPhaseBProcessQuantitativeLeftInactiveBudget_at_norm_le_principalEndpointBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    Complex.logarithmicPhaseBProcessQuantitativeLeftInactiveBudget ‖t‖ a b ≤
      Complex.logarithmicPhaseFiniteLeftPrincipalEndpointBudget ‖t‖ a b := by
  unfold Complex.logarithmicPhaseBProcessQuantitativeLeftInactiveBudget
  unfold Complex.logarithmicPhaseFiniteLeftPrincipalEndpointBudget
  exact Finset.sum_le_sum (fun m hm =>
    Complex.norm_logarithmicPhaseQuantitativeFiniteLeftInactivePacket_at_norm_le_principalEndpointBudget
      t ht a b m ha hab hm)

theorem Complex.logarithmicPhaseBProcessQuantitativeLeftInactiveBudget_le_principalEndpointBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    Complex.logarithmicPhaseBProcessQuantitativeLeftInactiveBudget t a b ≤
      Complex.logarithmicPhaseFiniteLeftPrincipalEndpointBudget t a b := by
  have hnorm : ‖t‖ = t :=
    Real.norm_of_nonneg ht_nonneg
  have hcanonical :=
    Complex.logarithmicPhaseBProcessQuantitativeLeftInactiveBudget_at_norm_le_principalEndpointBudget
      t ht a b ha hab
  exact Eq.subst
    (motive := fun parameter : ℝ =>
      Complex.logarithmicPhaseBProcessQuantitativeLeftInactiveBudget
          parameter a b ≤
        Complex.logarithmicPhaseFiniteLeftPrincipalEndpointBudget
          parameter a b)
    hnorm hcanonical

theorem Complex.logarithmicPhaseBProcessQuantitativeRightInactiveBudget_at_norm_le_principalEndpointBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    Complex.logarithmicPhaseBProcessQuantitativeRightInactiveBudget ‖t‖ a b ≤
      Complex.logarithmicPhaseFiniteRightPrincipalEndpointBudget ‖t‖ a b := by
  unfold Complex.logarithmicPhaseBProcessQuantitativeRightInactiveBudget
  unfold Complex.logarithmicPhaseFiniteRightPrincipalEndpointBudget
  exact Finset.sum_le_sum (fun m hm =>
    Complex.norm_logarithmicPhaseQuantitativeFiniteRightInactivePacket_at_norm_le_principalEndpointBudget
      t ht a b m ha hab hm)

theorem Complex.logarithmicPhaseBProcessQuantitativeRightInactiveBudget_le_principalEndpointBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    Complex.logarithmicPhaseBProcessQuantitativeRightInactiveBudget t a b ≤
      Complex.logarithmicPhaseFiniteRightPrincipalEndpointBudget t a b := by
  have hnorm : ‖t‖ = t :=
    Real.norm_of_nonneg ht_nonneg
  have hcanonical :=
    Complex.logarithmicPhaseBProcessQuantitativeRightInactiveBudget_at_norm_le_principalEndpointBudget
      t ht a b ha hab
  exact Eq.subst
    (motive := fun parameter : ℝ =>
      Complex.logarithmicPhaseBProcessQuantitativeRightInactiveBudget
          parameter a b ≤
        Complex.logarithmicPhaseFiniteRightPrincipalEndpointBudget
          parameter a b)
    hnorm hcanonical

theorem Complex.logarithmicPhaseFiniteInactivePacketBudgets_at_norm_le_principalEndpointBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    Complex.logarithmicPhaseBProcessQuantitativeLeftInactiveBudget ‖t‖ a b +
        Complex.logarithmicPhaseBProcessQuantitativeRightInactiveBudget ‖t‖ a b ≤
      Complex.logarithmicPhaseFiniteInactivePrincipalEndpointBudget ‖t‖ a b := by
  unfold Complex.logarithmicPhaseFiniteInactivePrincipalEndpointBudget
  exact add_le_add
    (Complex.logarithmicPhaseBProcessQuantitativeLeftInactiveBudget_at_norm_le_principalEndpointBudget
      t ht a b ha hab)
    (Complex.logarithmicPhaseBProcessQuantitativeRightInactiveBudget_at_norm_le_principalEndpointBudget
      t ht a b ha hab)

theorem Complex.logarithmicPhaseFiniteInactivePacketBudgets_le_principalEndpointBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    Complex.logarithmicPhaseBProcessQuantitativeLeftInactiveBudget t a b +
        Complex.logarithmicPhaseBProcessQuantitativeRightInactiveBudget t a b ≤
      Complex.logarithmicPhaseFiniteInactivePrincipalEndpointBudget t a b := by
  have hnorm : ‖t‖ = t :=
    Real.norm_of_nonneg ht_nonneg
  have hcanonical :=
    Complex.logarithmicPhaseFiniteInactivePacketBudgets_at_norm_le_principalEndpointBudget
      t ht a b ha hab
  exact Eq.subst
    (motive := fun parameter : ℝ =>
      Complex.logarithmicPhaseBProcessQuantitativeLeftInactiveBudget
          parameter a b +
          Complex.logarithmicPhaseBProcessQuantitativeRightInactiveBudget
            parameter a b ≤
        Complex.logarithmicPhaseFiniteInactivePrincipalEndpointBudget
          parameter a b)
    hnorm hcanonical

end

end LFunctions
end Boundary
