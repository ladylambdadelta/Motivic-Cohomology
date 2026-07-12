import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.NonstationaryPhase
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.FiniteSumNorm

/-!
# Finite frequency-packet reconstruction

This file owns the finite combinatorial part of the B-process.  Analytic
estimates for individual twisted packets are deliberately separate: here we
only construct the packets, prove their disjointness and coverage, and
reconstruct the original exponential sum using the correctly normalized
`2πm` Fourier twists.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The samples assigned to Fourier mode `m` by a finite mode assignment. -/
def Complex.frequencyPacket
    (a b : ℕ)
    (modeOf : ℕ → ℤ)
    (m : ℤ) : Finset ℕ :=
  (Finset.Icc a b).filter (fun n : ℕ => modeOf n = m)

/-- The finite family of packets indexed by a chosen mode set. -/
def Complex.frequencyPacketFamilyUnion
    (a b : ℕ)
    (modeOf : ℕ → ℤ)
    (modes : Finset ℤ) : Finset ℕ :=
  modes.biUnion (fun m : ℤ => Complex.frequencyPacket a b modeOf m)

/-- Complement of a selected frequency-packet family inside its ambient
integer block. -/
def Complex.frequencyPacketFamilyComplement
    (a b : ℕ)
    (modeOf : ℕ → ℤ)
    (modes : Finset ℤ) : Finset ℕ :=
  (Finset.Icc a b).filter
    (fun n : ℕ => n ∉ Complex.frequencyPacketFamilyUnion a b modeOf modes)

/-- Gap label of a complement sample: the number of selected modes strictly
below its assigned mode. -/
def Complex.frequencyPacketComplementGapIndex
    (modeOf : ℕ → ℤ)
    (modes : Finset ℤ)
    (n : ℕ) : ℕ :=
  (modes.filter (fun m : ℤ => m < modeOf n)).card

/-- One labeled gap in the complement of a selected packet family. -/
def Complex.frequencyPacketComplementGap
    (a b : ℕ)
    (modeOf : ℕ → ℤ)
    (modes : Finset ℤ)
    (r : ℕ) : Finset ℕ :=
  (Complex.frequencyPacketFamilyComplement a b modeOf modes).filter
    (fun n : ℕ =>
      Complex.frequencyPacketComplementGapIndex modeOf modes n = r)

/-- Canonical finite range of complement-gap labels. -/
def Complex.frequencyPacketComplementGapRange
    (modes : Finset ℤ) : Finset ℕ :=
  Finset.range (modes.card + 1)

/-- Union of the canonical complement-gap family. -/
def Complex.frequencyPacketComplementGapFamilyUnion
    (a b : ℕ)
    (modeOf : ℕ → ℤ)
    (modes : Finset ℤ) : Finset ℕ :=
  (Complex.frequencyPacketComplementGapRange modes).biUnion
    (fun r : ℕ =>
      Complex.frequencyPacketComplementGap a b modeOf modes r)

/-- Canonical integer Fourier mode assigned to an integer sample by the
derivative of a real phase. -/
def Complex.realPhaseDerivativeFrequencyMode
    (φ : ℝ → ℝ)
    (n : ℕ) : ℤ :=
  Int.floor (deriv φ n / (2 * Real.pi))

/-- The finite set of canonical derivative-frequency modes met by a block. -/
def Complex.realPhaseDerivativeFrequencyModes
    (φ : ℝ → ℝ)
    (a b : ℕ) : Finset ℤ :=
  (Finset.Icc a b).image (Complex.realPhaseDerivativeFrequencyMode φ)

/-- Every block sample's canonical derivative-frequency mode belongs to the
finite mode image. -/
theorem Complex.realPhaseDerivativeFrequencyMode_mem_modes
    (φ : ℝ → ℝ)
    {a b n : ℕ}
    (hn : n ∈ Finset.Icc a b) :
    Complex.realPhaseDerivativeFrequencyMode φ n ∈
      Complex.realPhaseDerivativeFrequencyModes φ a b := by
  exact Finset.mem_image.mpr
    (Exists.intro n (And.intro hn rfl))

/-- The canonical derivative-frequency assignment covers the whole block. -/
theorem Complex.realPhaseDerivativeFrequencyMode_block_cover
    (φ : ℝ → ℝ)
    (a b : ℕ) :
    ∀ n : ℕ,
      n ∈ Finset.Icc a b →
        Complex.realPhaseDerivativeFrequencyMode φ n ∈
          Complex.realPhaseDerivativeFrequencyModes φ a b := by
  intro n hn
  exact Complex.realPhaseDerivativeFrequencyMode_mem_modes φ hn

/-- The number of active derivative-frequency centers is at most the number of
samples in the block. -/
theorem Complex.realPhaseDerivativeFrequencyModes_card_le_block_card
    (φ : ℝ → ℝ)
    (a b : ℕ) :
    (Complex.realPhaseDerivativeFrequencyModes φ a b).card ≤
      (Finset.Icc a b).card := by
  exact Finset.card_image_le

/-- A packet is exactly the block membership together with the mode equation. -/
theorem Complex.mem_frequencyPacket_iff
    (a b : ℕ)
    (modeOf : ℕ → ℤ)
    (m : ℤ)
    (n : ℕ) :
    n ∈ Complex.frequencyPacket a b modeOf m ↔
      n ∈ Finset.Icc a b ∧ modeOf n = m := by
  exact Finset.mem_filter

/-- Different mode labels give disjoint packets. -/
theorem Complex.frequencyPacket_pairwiseDisjoint
    (a b : ℕ)
    (modeOf : ℕ → ℤ) :
    ∀ m₁ m₂ : ℤ,
      m₁ ≠ m₂ →
        Disjoint
          (Complex.frequencyPacket a b modeOf m₁)
          (Complex.frequencyPacket a b modeOf m₂) := by
  intro m₁ m₂ hne
  exact Finset.disjoint_left.mpr
    (fun n hn₁ hn₂ => by
      have hmode₁ : modeOf n = m₁ :=
        (Complex.mem_frequencyPacket_iff a b modeOf m₁ n).mp hn₁ |>.2
      have hmode₂ : modeOf n = m₂ :=
        (Complex.mem_frequencyPacket_iff a b modeOf m₂ n).mp hn₂ |>.2
      exact hne (hmode₁.symm.trans hmode₂))

/-- Strictly ordered mode labels force every sample of the lower packet to
precede every sample of the upper packet under a monotone assignment. -/
theorem Complex.frequencyPacket_ordered_of_monotoneOn
    (a b : ℕ)
    (modeOf : ℕ → ℤ)
    (hmono :
      ∀ {i j : ℕ},
        i ∈ Finset.Icc a b →
          j ∈ Finset.Icc a b →
            i ≤ j → modeOf i ≤ modeOf j)
    {m₁ m₂ : ℤ}
    (hmodes : m₁ < m₂) :
    ∀ i ∈ Complex.frequencyPacket a b modeOf m₁,
      ∀ j ∈ Complex.frequencyPacket a b modeOf m₂,
        i < j := by
  intro i hi j hj
  have hi_data :=
    (Complex.mem_frequencyPacket_iff a b modeOf m₁ i).mp hi
  have hj_data :=
    (Complex.mem_frequencyPacket_iff a b modeOf m₂ j).mp hj
  match lt_or_ge i j with
  | Or.inl hij => exact hij
  | Or.inr hji =>
      have hmode_order : modeOf j ≤ modeOf i :=
        hmono hj_data.1 hi_data.1 hji
      have hm₂_le_m₁ : m₂ ≤ m₁ :=
        Eq.subst
          (motive := fun lower : ℤ => lower ≤ m₁)
          hj_data.2
          (Eq.subst
            (motive := fun upper : ℤ => modeOf j ≤ upper)
            hi_data.2
            hmode_order)
      exact False.elim ((not_le_of_gt hmodes) hm₂_le_m₁)

/-- A frequency packet of a monotone integer mode assignment is interval
connected inside its ambient block. -/
theorem Complex.frequencyPacket_intervalConnected_of_monotoneOn
    (a b : ℕ)
    (modeOf : ℕ → ℤ)
    (m : ℤ)
    (hmono :
      ∀ {i j : ℕ},
        i ∈ Finset.Icc a b →
          j ∈ Finset.Icc a b →
            i ≤ j → modeOf i ≤ modeOf j) :
    ∀ i j k : ℕ,
      i ∈ Complex.frequencyPacket a b modeOf m →
        k ∈ Complex.frequencyPacket a b modeOf m →
          j ∈ Finset.Icc a b →
            i ≤ j → j ≤ k →
              j ∈ Complex.frequencyPacket a b modeOf m := by
  intro i j k hi hk hj hij hjk
  have hi_data :=
    (Complex.mem_frequencyPacket_iff a b modeOf m i).mp hi
  have hk_data :=
    (Complex.mem_frequencyPacket_iff a b modeOf m k).mp hk
  have hmode_left : modeOf i ≤ modeOf j :=
    hmono hi_data.1 hj hij
  have hmode_right : modeOf j ≤ modeOf k :=
    hmono hj hk_data.1 hjk
  have hm_le : m ≤ modeOf j :=
    Eq.subst
      (motive := fun value : ℤ => value ≤ modeOf j)
      hi_data.2
      hmode_left
  have hle_m : modeOf j ≤ m :=
    Eq.subst
      (motive := fun value : ℤ => modeOf j ≤ value)
      hk_data.2
      hmode_right
  have hmode_j : modeOf j = m :=
    le_antisymm hle_m hm_le
  exact
    (Complex.mem_frequencyPacket_iff a b modeOf m j).mpr
      (And.intro hj hmode_j)

/-- A finite interval-connected subset of a half-open natural interval is a
half-open interval with controlled endpoints. -/
theorem Finset.exists_eq_Ico_of_subset_Ico_intervalConnected
    {S : Finset ℕ}
    {a b : ℕ}
    (hab : a ≤ b)
    (hS_block : S ⊆ Finset.Ico a b)
    (hconnected :
      ∀ i j k : ℕ,
        i ∈ S →
          k ∈ S →
            j ∈ Finset.Ico a b →
              i ≤ j → j ≤ k → j ∈ S) :
    ∃ c d : ℕ,
      a ≤ c ∧ c ≤ d ∧ d ≤ b ∧ S = Finset.Ico c d := by
  match S.eq_empty_or_nonempty with
  | Or.inl hS_empty =>
      have hIco_empty : Finset.Ico a a = (∅ : Finset ℕ) :=
        Finset.eq_empty_iff_forall_not_mem.mpr
          (fun n hn =>
            have hn_bounds := Finset.mem_Ico.mp hn
            not_lt_of_ge hn_bounds.1 hn_bounds.2)
      exact
        Exists.intro a
          (Exists.intro a
            (And.intro le_rfl
              (And.intro le_rfl
                (And.intro hab (Eq.trans hS_empty hIco_empty.symm)))))
  | Or.inr hS_nonempty =>
      let c : ℕ := S.min' hS_nonempty
      let r : ℕ := S.max' hS_nonempty
      let d : ℕ := r + 1
      have hc_mem : c ∈ S := Finset.min'_mem S hS_nonempty
      have hr_mem : r ∈ S := Finset.max'_mem S hS_nonempty
      have hc_block := Finset.mem_Ico.mp (hS_block hc_mem)
      have hr_block := Finset.mem_Ico.mp (hS_block hr_mem)
      have hc_le_r : c ≤ r := Finset.min'_le S r hr_mem
      have hc_le_d : c ≤ d :=
        le_trans hc_le_r (Nat.le_succ r)
      have hd_le_b : d ≤ b :=
        Nat.succ_le_of_lt hr_block.2
      have hS_eq : S = Finset.Ico c d :=
        Finset.ext
          (fun n =>
            Iff.intro
              (fun hn =>
                Finset.mem_Ico.mpr
                  (And.intro
                    (Finset.min'_le S n hn)
                    (Nat.lt_succ_of_le (Finset.le_max' S n hn))))
              (fun hn =>
                have hn_bounds := Finset.mem_Ico.mp hn
                have hn_le_r : n ≤ r :=
                  Nat.le_of_lt_succ hn_bounds.2
                have hn_block : n ∈ Finset.Ico a b :=
                  Finset.mem_Ico.mpr
                    (And.intro
                      (le_trans hc_block.1 hn_bounds.1)
                      (lt_of_le_of_lt hn_le_r hr_block.2))
                hconnected c n r hc_mem hr_mem hn_block
                  hn_bounds.1 hn_le_r))
      exact
        Exists.intro c
          (Exists.intro d
            (And.intro hc_block.1
              (And.intro hc_le_d (And.intro hd_le_b hS_eq))))

/-- Every packet of a monotone mode assignment on a nonempty ordered block has
canonical half-open interval shape. -/
theorem Complex.frequencyPacket_exists_eq_Ico_of_monotoneOn
    {a b : ℕ}
    (hab : a ≤ b)
    (modeOf : ℕ → ℤ)
    (m : ℤ)
    (hmono :
      ∀ {i j : ℕ},
        i ∈ Finset.Icc a b →
          j ∈ Finset.Icc a b →
            i ≤ j → modeOf i ≤ modeOf j) :
    ∃ c d : ℕ,
      a ≤ c ∧ c ≤ d ∧ d ≤ b + 1 ∧
        Complex.frequencyPacket a b modeOf m = Finset.Ico c d := by
  have hsubset :
      Complex.frequencyPacket a b modeOf m ⊆ Finset.Ico a (b + 1) := by
    intro n hn
    have hn_block :=
      (Complex.mem_frequencyPacket_iff a b modeOf m n).mp hn |>.1
    have hn_bounds := Finset.mem_Icc.mp hn_block
    exact Finset.mem_Ico.mpr
      (And.intro hn_bounds.1 (Nat.lt_succ_of_le hn_bounds.2))
  have hconnected :
      ∀ i j k : ℕ,
        i ∈ Complex.frequencyPacket a b modeOf m →
          k ∈ Complex.frequencyPacket a b modeOf m →
            j ∈ Finset.Ico a (b + 1) →
              i ≤ j → j ≤ k →
                j ∈ Complex.frequencyPacket a b modeOf m := by
    intro i j k hi hk hj hij hjk
    have hj_bounds := Finset.mem_Ico.mp hj
    have hj_Icc : j ∈ Finset.Icc a b :=
      Finset.mem_Icc.mpr
        (And.intro hj_bounds.1 (Nat.le_of_lt_succ hj_bounds.2))
    exact
      Complex.frequencyPacket_intervalConnected_of_monotoneOn
        a b modeOf m hmono i j k hi hk hj_Icc hij hjk
  exact
    Finset.exists_eq_Ico_of_subset_Ico_intervalConnected
      (le_trans hab (Nat.le_succ b)) hsubset hconnected

/-- Cardinality of a packet from its canonical half-open interval endpoints. -/
theorem Complex.frequencyPacket_card_eq_endpointLength_of_eq_Ico
    (a b : ℕ)
    (modeOf : ℕ → ℤ)
    (m : ℤ)
    {c d : ℕ}
    (hpacket : Complex.frequencyPacket a b modeOf m = Finset.Ico c d) :
    (Complex.frequencyPacket a b modeOf m).card = d - c := by
  exact
    Eq.trans
      (congrArg Finset.card hpacket)
      (Nat.card_Ico c d)

/-- A real endpoint-spread bound supplies the corresponding packet-cardinality
bound. -/
theorem Complex.frequencyPacket_card_real_le_of_endpointLength
    (a b : ℕ)
    (modeOf : ℕ → ℤ)
    (m : ℤ)
    {c d : ℕ}
    {W : ℝ}
    (hpacket : Complex.frequencyPacket a b modeOf m = Finset.Ico c d)
    (hlength : ((d - c : ℕ) : ℝ) ≤ W) :
    ((Complex.frequencyPacket a b modeOf m).card : ℝ) ≤ W := by
  have hcard :=
    Complex.frequencyPacket_card_eq_endpointLength_of_eq_Ico
      a b modeOf m hpacket
  exact
    Eq.subst
      (motive := fun length : ℕ => (length : ℝ) ≤ W)
      hcard.symm
      hlength

/-- Canonical packet endpoints have spread at most the ambient half-open
block length. -/
theorem Complex.frequencyPacket_endpointLength_le_blockLength
    {a b c d : ℕ}
    (hac : a ≤ c)
    (hd : d ≤ b + 1) :
    d - c ≤ (b + 1) - a := by
  exact le_trans
    (Nat.sub_le_sub_right hd c)
    (Nat.sub_le_sub_left hac (b + 1))

/-- The real-valued form of the canonical endpoint-spread bound. -/
theorem Complex.frequencyPacket_endpointLength_real_le_blockLength
    {a b c d : ℕ}
    (hac : a ≤ c)
    (hd : d ≤ b + 1) :
    ((d - c : ℕ) : ℝ) ≤ (((b + 1) - a : ℕ) : ℝ) := by
  exact Nat.cast_le.mpr
    (Complex.frequencyPacket_endpointLength_le_blockLength hac hd)

/-- If every sample in the block receives a selected mode, the packet family
covers the whole block. -/
theorem Complex.frequencyPacketFamilyUnion_eq_block
    (a b : ℕ)
    (modeOf : ℕ → ℤ)
    (modes : Finset ℤ)
    (hcover : ∀ n : ℕ, n ∈ Finset.Icc a b → modeOf n ∈ modes) :
    Complex.frequencyPacketFamilyUnion a b modeOf modes = Finset.Icc a b := by
  exact Finset.Subset.antisymm
    (fun n hn => by
    have hexists :
        ∃ m : ℤ,
          m ∈ modes ∧ n ∈ Complex.frequencyPacket a b modeOf m :=
      Finset.mem_biUnion.mp hn
    exact
      (Complex.mem_frequencyPacket_iff a b modeOf hexists.choose n).mp
        hexists.choose_spec.2 |>.1)
    (fun n hn =>
      have hm : modeOf n ∈ modes := hcover n hn
      Finset.mem_biUnion.mpr
        (Exists.intro (modeOf n)
          (And.intro hm
            ((Complex.mem_frequencyPacket_iff a b modeOf (modeOf n) n).mpr
              (And.intro hn rfl)))))

/-- Exact membership criterion for the complement of a selected packet
family. -/
theorem Complex.mem_frequencyPacketFamilyComplement_iff
    (a b : ℕ)
    (modeOf : ℕ → ℤ)
    (modes : Finset ℤ)
    (n : ℕ) :
    n ∈ Complex.frequencyPacketFamilyComplement a b modeOf modes ↔
      n ∈ Finset.Icc a b ∧
        n ∉ Complex.frequencyPacketFamilyUnion a b modeOf modes := by
  exact Finset.mem_filter

/-- Exact membership criterion for one labeled complement gap. -/
theorem Complex.mem_frequencyPacketComplementGap_iff
    (a b : ℕ)
    (modeOf : ℕ → ℤ)
    (modes : Finset ℤ)
    (r n : ℕ) :
    n ∈ Complex.frequencyPacketComplementGap a b modeOf modes r ↔
      n ∈ Complex.frequencyPacketFamilyComplement a b modeOf modes ∧
        Complex.frequencyPacketComplementGapIndex modeOf modes n = r := by
  exact Finset.mem_filter

/-- Every complement-sample gap label lies in the canonical label range. -/
theorem Complex.frequencyPacketComplementGapIndex_mem_range
    (modeOf : ℕ → ℤ)
    (modes : Finset ℤ)
    (n : ℕ) :
    Complex.frequencyPacketComplementGapIndex modeOf modes n ∈
      Complex.frequencyPacketComplementGapRange modes := by
  have hcard :
      (modes.filter (fun m : ℤ => m < modeOf n)).card ≤ modes.card :=
    Finset.card_le_card (Finset.filter_subset _ modes)
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le hcard)

/-- The canonical labeled gap family covers the full packet complement. -/
theorem Complex.frequencyPacketComplementGapFamilyUnion_eq_complement
    (a b : ℕ)
    (modeOf : ℕ → ℤ)
    (modes : Finset ℤ) :
    Complex.frequencyPacketComplementGapFamilyUnion a b modeOf modes =
      Complex.frequencyPacketFamilyComplement a b modeOf modes := by
  exact Finset.Subset.antisymm
    (fun n hn => by
    have hexists := Finset.mem_biUnion.mp hn
    exact
      (Complex.mem_frequencyPacketComplementGap_iff
        a b modeOf modes hexists.choose n).mp hexists.choose_spec.2 |>.1)
    (fun n hn => by
      let r : ℕ :=
        Complex.frequencyPacketComplementGapIndex modeOf modes n
      have hr : r ∈ Complex.frequencyPacketComplementGapRange modes :=
        Complex.frequencyPacketComplementGapIndex_mem_range modeOf modes n
      exact
        Finset.mem_biUnion.mpr
          (Exists.intro r
            (And.intro hr
              ((Complex.mem_frequencyPacketComplementGap_iff
                a b modeOf modes r n).mpr (And.intro hn rfl)))))

/-- Distinct complement-gap labels give disjoint gap fibers. -/
theorem Complex.frequencyPacketComplementGap_pairwiseDisjoint
    (a b : ℕ)
    (modeOf : ℕ → ℤ)
    (modes : Finset ℤ) :
    ∀ r₁ r₂ : ℕ,
      r₁ ≠ r₂ →
        Disjoint
          (Complex.frequencyPacketComplementGap a b modeOf modes r₁)
          (Complex.frequencyPacketComplementGap a b modeOf modes r₂) := by
  intro r₁ r₂ hne
  exact
    Finset.disjoint_left.mpr
      (fun n hn₁ hn₂ =>
        have hindex₁ :=
          (Complex.mem_frequencyPacketComplementGap_iff
            a b modeOf modes r₁ n).mp hn₁ |>.2
        have hindex₂ :=
          (Complex.mem_frequencyPacketComplementGap_iff
            a b modeOf modes r₂ n).mp hn₂ |>.2
        hne (hindex₁.symm.trans hindex₂))

/-- Gap labels are monotone with the assigned integer frequency mode. -/
theorem Complex.frequencyPacketComplementGapIndex_mono
    (modeOf : ℕ → ℤ)
    (modes : Finset ℤ)
    {i j : ℕ}
    (hmode : modeOf i ≤ modeOf j) :
    Complex.frequencyPacketComplementGapIndex modeOf modes i ≤
      Complex.frequencyPacketComplementGapIndex modeOf modes j := by
  exact Finset.card_le_card
    (fun m hm =>
      have hm_data := Finset.mem_filter.mp hm
      Finset.mem_filter.mpr
        (And.intro hm_data.1 (lt_of_lt_of_le hm_data.2 hmode)))

/-- Every labeled complement gap is interval connected when the mode
assignment is monotone on the ambient block. -/
theorem Complex.frequencyPacketComplementGap_intervalConnected_of_monotoneOn
    (a b : ℕ)
    (modeOf : ℕ → ℤ)
    (modes : Finset ℤ)
    (r : ℕ)
    (hmono :
      ∀ {i j : ℕ},
        i ∈ Finset.Icc a b →
          j ∈ Finset.Icc a b →
            i ≤ j → modeOf i ≤ modeOf j) :
    ∀ i j k : ℕ,
      i ∈ Complex.frequencyPacketComplementGap a b modeOf modes r →
        k ∈ Complex.frequencyPacketComplementGap a b modeOf modes r →
          j ∈ Complex.frequencyPacketFamilyComplement a b modeOf modes →
            i ≤ j → j ≤ k →
              j ∈ Complex.frequencyPacketComplementGap a b modeOf modes r := by
  intro i j k hi hk hj hij hjk
  have hi_data :=
    (Complex.mem_frequencyPacketComplementGap_iff
      a b modeOf modes r i).mp hi
  have hk_data :=
    (Complex.mem_frequencyPacketComplementGap_iff
      a b modeOf modes r k).mp hk
  have hi_block :=
    (Complex.mem_frequencyPacketFamilyComplement_iff
      a b modeOf modes i).mp hi_data.1 |>.1
  have hj_block :=
    (Complex.mem_frequencyPacketFamilyComplement_iff
      a b modeOf modes j).mp hj |>.1
  have hk_block :=
    (Complex.mem_frequencyPacketFamilyComplement_iff
      a b modeOf modes k).mp hk_data.1 |>.1
  have hindex_left :
      Complex.frequencyPacketComplementGapIndex modeOf modes i ≤
        Complex.frequencyPacketComplementGapIndex modeOf modes j :=
    Complex.frequencyPacketComplementGapIndex_mono modeOf modes
      (hmono hi_block hj_block hij)
  have hindex_right :
      Complex.frequencyPacketComplementGapIndex modeOf modes j ≤
        Complex.frequencyPacketComplementGapIndex modeOf modes k :=
    Complex.frequencyPacketComplementGapIndex_mono modeOf modes
      (hmono hj_block hk_block hjk)
  have hr_le :
      r ≤ Complex.frequencyPacketComplementGapIndex modeOf modes j :=
    Eq.subst
      (motive := fun value : ℕ => value ≤
        Complex.frequencyPacketComplementGapIndex modeOf modes j)
      hi_data.2
      hindex_left
  have hle_r :
      Complex.frequencyPacketComplementGapIndex modeOf modes j ≤ r :=
    Eq.subst
      (motive := fun value : ℕ =>
        Complex.frequencyPacketComplementGapIndex modeOf modes j ≤ value)
      hk_data.2
      hindex_right
  exact
    (Complex.mem_frequencyPacketComplementGap_iff
      a b modeOf modes r j).mpr
        (And.intro hj (le_antisymm hle_r hr_le))

/-- The canonical complement-gap label range has exactly one more element than
the selected mode family. -/
theorem Complex.frequencyPacketComplementGapRange_card_eq
    (modes : Finset ℤ) :
    (Complex.frequencyPacketComplementGapRange modes).card =
      modes.card + 1 := by
  exact Finset.card_range (modes.card + 1)

/-- A selected packet family together with its complement covers the ambient
block. -/
theorem Complex.frequencyPacketFamilyUnion_union_complement_eq_block
    (a b : ℕ)
    (modeOf : ℕ → ℤ)
    (modes : Finset ℤ) :
    Complex.frequencyPacketFamilyUnion a b modeOf modes ∪
        Complex.frequencyPacketFamilyComplement a b modeOf modes =
      Finset.Icc a b := by
  exact Finset.Subset.antisymm
    (fun n hn => by
    match Finset.mem_union.mp hn with
    | Or.inl hunion =>
        have hexists := Finset.mem_biUnion.mp hunion
        exact
          (Complex.mem_frequencyPacket_iff
            a b modeOf hexists.choose n).mp hexists.choose_spec.2 |>.1
    | Or.inr hcomplement =>
        exact
          (Complex.mem_frequencyPacketFamilyComplement_iff
            a b modeOf modes n).mp hcomplement |>.1)
    (fun n hn =>
      match Classical.em
          (n ∈ Complex.frequencyPacketFamilyUnion a b modeOf modes) with
      | Or.inl hunion =>
          Finset.mem_union_left _ hunion
      | Or.inr hunion =>
          Finset.mem_union_right _
            ((Complex.mem_frequencyPacketFamilyComplement_iff
              a b modeOf modes n).mpr (And.intro hn hunion)))

/-- A selected packet family is disjoint from its complement. -/
theorem Complex.frequencyPacketFamilyUnion_disjoint_complement
    (a b : ℕ)
    (modeOf : ℕ → ℤ)
    (modes : Finset ℤ) :
    Disjoint
      (Complex.frequencyPacketFamilyUnion a b modeOf modes)
      (Complex.frequencyPacketFamilyComplement a b modeOf modes) := by
  exact
    Finset.disjoint_left.mpr
      (fun n hunion hcomplement =>
        (Complex.mem_frequencyPacketFamilyComplement_iff
          a b modeOf modes n).mp hcomplement |>.2 hunion)

/-- Additive trivial estimate for the complement of a selected packet family. -/
theorem Complex.norm_frequencyPacketFamilyComplement_sum_le_card
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (modeOf : ℕ → ℤ)
    (modes : Finset ℤ) :
    ‖∑ n ∈ Complex.frequencyPacketFamilyComplement a b modeOf modes,
        Complex.realPhaseOscillation φ n‖ ≤
      ((Complex.frequencyPacketFamilyComplement a b modeOf modes).card : ℝ) := by
  exact
    Complex.finite_sum_norm_le_card_of_norm_le_one
      (Complex.frequencyPacketFamilyComplement a b modeOf modes)
      (fun n : ℕ => Complex.realPhaseOscillation φ n)
      (fun n _hn =>
        le_of_eq (Complex.norm_realPhaseOscillation φ n))

/-- Exact additive decomposition of the packet complement into its canonical
labeled gap family. -/
theorem Complex.frequencyPacketComplement_sum_eq_sum_gaps
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (modeOf : ℕ → ℤ)
    (modes : Finset ℤ) :
    (∑ n ∈ Complex.frequencyPacketFamilyComplement a b modeOf modes,
        Complex.realPhaseOscillation φ n) =
      ∑ r ∈ Complex.frequencyPacketComplementGapRange modes,
        ∑ n ∈ Complex.frequencyPacketComplementGap a b modeOf modes r,
          Complex.realPhaseOscillation φ n := by
  have hfamily :=
    Complex.frequencyPacketComplementGapFamilyUnion_eq_complement
      a b modeOf modes
  have hdisjoint :
      ∀ r₁ ∈ Complex.frequencyPacketComplementGapRange modes,
        ∀ r₂ ∈ Complex.frequencyPacketComplementGapRange modes,
          r₁ ≠ r₂ →
            Disjoint
              (Complex.frequencyPacketComplementGap a b modeOf modes r₁)
              (Complex.frequencyPacketComplementGap a b modeOf modes r₂) := by
    intro r₁ _hr₁ r₂ _hr₂ hne
    exact
      Complex.frequencyPacketComplementGap_pairwiseDisjoint
        a b modeOf modes r₁ r₂ hne
  have hsum :
      (∑ n ∈ Complex.frequencyPacketComplementGapFamilyUnion
          a b modeOf modes,
        Complex.realPhaseOscillation φ n) =
        ∑ r ∈ Complex.frequencyPacketComplementGapRange modes,
          ∑ n ∈ Complex.frequencyPacketComplementGap a b modeOf modes r,
            Complex.realPhaseOscillation φ n :=
    Finset.sum_biUnion hdisjoint
  exact
    Eq.subst
      (motive := fun family : Finset ℕ =>
        (∑ n ∈ family, Complex.realPhaseOscillation φ n) =
          ∑ r ∈ Complex.frequencyPacketComplementGapRange modes,
            ∑ n ∈ Complex.frequencyPacketComplementGap a b modeOf modes r,
              Complex.realPhaseOscillation φ n)
      hfamily
      hsum

/-- Additive complement estimate by the sum of the individual canonical gap
norms. -/
theorem Complex.norm_frequencyPacketFamilyComplement_sum_le_sum_gap_norms
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (modeOf : ℕ → ℤ)
    (modes : Finset ℤ) :
    ‖∑ n ∈ Complex.frequencyPacketFamilyComplement a b modeOf modes,
        Complex.realPhaseOscillation φ n‖ ≤
      ∑ r ∈ Complex.frequencyPacketComplementGapRange modes,
        ‖∑ n ∈ Complex.frequencyPacketComplementGap a b modeOf modes r,
          Complex.realPhaseOscillation φ n‖ := by
  have hreconstruction :=
    Complex.frequencyPacketComplement_sum_eq_sum_gaps
      φ a b modeOf modes
  have htriangle :
      ‖∑ r ∈ Complex.frequencyPacketComplementGapRange modes,
        ∑ n ∈ Complex.frequencyPacketComplementGap a b modeOf modes r,
          Complex.realPhaseOscillation φ n‖ ≤
        ∑ r ∈ Complex.frequencyPacketComplementGapRange modes,
          ‖∑ n ∈ Complex.frequencyPacketComplementGap a b modeOf modes r,
            Complex.realPhaseOscillation φ n‖ :=
    norm_sum_le
      (Complex.frequencyPacketComplementGapRange modes)
      (fun r : ℕ =>
        ∑ n ∈ Complex.frequencyPacketComplementGap a b modeOf modes r,
          Complex.realPhaseOscillation φ n)
  exact
    Eq.subst
      (motive := fun value : ℂ =>
        ‖value‖ ≤
          ∑ r ∈ Complex.frequencyPacketComplementGapRange modes,
            ‖∑ n ∈ Complex.frequencyPacketComplementGap a b modeOf modes r,
              Complex.realPhaseOscillation φ n‖)
      hreconstruction.symm
      htriangle

/-- Exact cardinality accounting for a covered frequency packet family. -/
theorem Complex.frequencyPacketFamilyUnion_card_eq_sum_packet_cards
    (a b : ℕ)
    (modeOf : ℕ → ℤ)
    (modes : Finset ℤ) :
    (Complex.frequencyPacketFamilyUnion a b modeOf modes).card =
      ∑ m ∈ modes,
        (Complex.frequencyPacket a b modeOf m).card := by
  have hdisjoint :
      ∀ m₁ ∈ modes,
        ∀ m₂ ∈ modes,
          m₁ ≠ m₂ →
            Disjoint
              (Complex.frequencyPacket a b modeOf m₁)
              (Complex.frequencyPacket a b modeOf m₂) := by
    intro m₁ _ m₂ _ hne
    exact Complex.frequencyPacket_pairwiseDisjoint a b modeOf m₁ m₂ hne
  exact Finset.card_biUnion hdisjoint

/-- Every finite frequency-packet family lies inside its ambient block. -/
theorem Complex.frequencyPacketFamilyUnion_card_le_block_card
    (a b : ℕ)
    (modeOf : ℕ → ℤ)
    (modes : Finset ℤ) :
    (Complex.frequencyPacketFamilyUnion a b modeOf modes).card ≤
      (Finset.Icc a b).card := by
  exact Finset.card_le_card
    (fun n hn =>
      have hexists :
          ∃ m : ℤ,
            m ∈ modes ∧ n ∈ Complex.frequencyPacket a b modeOf m :=
        Finset.mem_biUnion.mp hn
      (Complex.mem_frequencyPacket_iff a b modeOf hexists.choose n).mp
        hexists.choose_spec.2 |>.1)

/-- The twisted packet sum attached to a mode. -/
def Complex.frequencyPacketTwistedSum
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (modeOf : ℕ → ℤ)
    (m : ℤ) : ℂ :=
  ∑ n ∈ Complex.frequencyPacket a b modeOf m,
    Complex.exp
      (Complex.I *
        (Complex.realPhaseFrequencyTwist φ m n : ℂ))

/-- A single frequency packet is bounded by its number of integer samples.
This is the canonical active-window estimate before any stationary-phase
improvement: it uses only the unit modulus of every twisted sample. -/
theorem Complex.norm_frequencyPacketTwistedSum_le_card
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (modeOf : ℕ → ℤ)
    (m : ℤ) :
    ‖Complex.frequencyPacketTwistedSum φ a b modeOf m‖ ≤
      ((Complex.frequencyPacket a b modeOf m).card : ℝ) := by
  exact
    Complex.finite_sum_norm_le_card_of_norm_le_one
      (Complex.frequencyPacket a b modeOf m)
      (fun n : ℕ =>
        Complex.exp
          (Complex.I *
            (Complex.realPhaseFrequencyTwist φ m n : ℂ)))
      (fun n _hn => by
        have hexponent :
            Complex.I *
                (Complex.realPhaseFrequencyTwist φ m n : ℂ) =
              (Complex.realPhaseFrequencyTwist φ m n : ℂ) *
                Complex.I :=
          mul_comm Complex.I
            (Complex.realPhaseFrequencyTwist φ m n : ℂ)
        have hnorm :
            ‖Complex.exp
                (Complex.I *
                  (Complex.realPhaseFrequencyTwist φ m n : ℂ))‖ = 1 := by
          exact
            Eq.subst
              (motive := fun exponent : ℂ =>
                ‖Complex.exp exponent‖ = 1)
              hexponent.symm
              (Complex.norm_exp_ofReal_mul_I
                (Complex.realPhaseFrequencyTwist φ m n))
        exact le_of_eq hnorm)

/-- Endpoint spread controls a twisted active packet.  The packet geometry
and the analytic unit-modulus estimate are kept as separate named cuts. -/
theorem Complex.norm_frequencyPacketTwistedSum_le_endpointSpread
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (modeOf : ℕ → ℤ)
    (m : ℤ)
    {c d : ℕ}
    {W : ℝ}
    (hpacket : Complex.frequencyPacket a b modeOf m = Finset.Ico c d)
    (hspread : ((d - c : ℕ) : ℝ) ≤ W) :
    ‖Complex.frequencyPacketTwistedSum φ a b modeOf m‖ ≤ W := by
  have hcard :
      ((Complex.frequencyPacket a b modeOf m).card : ℝ) ≤ W :=
    Complex.frequencyPacket_card_real_le_of_endpointLength
      a b modeOf m hpacket hspread
  exact
    le_trans
      (Complex.norm_frequencyPacketTwistedSum_le_card
        φ a b modeOf m)
      hcard

/-- Canonical active-window estimate for a monotone frequency assignment.
The witness endpoints simultaneously record interval shape, endpoint order,
and the explicit ambient-spread bound for the twisted packet sum. -/
theorem Complex.exists_frequencyPacket_Ico_and_norm_le_blockLength_of_monotoneOn
    {φ : ℝ → ℝ}
    {a b : ℕ}
    (hab : a ≤ b)
    (modeOf : ℕ → ℤ)
    (m : ℤ)
    (hmono :
      ∀ {i j : ℕ},
        i ∈ Finset.Icc a b →
          j ∈ Finset.Icc a b →
            i ≤ j → modeOf i ≤ modeOf j) :
    ∃ c d : ℕ,
      a ≤ c ∧ c ≤ d ∧ d ≤ b + 1 ∧
        Complex.frequencyPacket a b modeOf m = Finset.Ico c d ∧
        ‖Complex.frequencyPacketTwistedSum φ a b modeOf m‖ ≤
          (((b + 1) - a : ℕ) : ℝ) := by
  match Complex.frequencyPacket_exists_eq_Ico_of_monotoneOn
      hab modeOf m hmono with
  | ⟨c, d, hac, hcd, hdb, hpacket⟩ =>
      have hspread :
          ((d - c : ℕ) : ℝ) ≤ (((b + 1) - a : ℕ) : ℝ) :=
        Complex.frequencyPacket_endpointLength_real_le_blockLength hac hdb
      have hnorm :
          ‖Complex.frequencyPacketTwistedSum φ a b modeOf m‖ ≤
            (((b + 1) - a : ℕ) : ℝ) :=
        Complex.norm_frequencyPacketTwistedSum_le_endpointSpread
          φ a b modeOf m hpacket hspread
      exact
        ⟨c, d, hac, hcd, hdb, hpacket, hnorm⟩

/-- On a packet whose assigned mode is `m`, the twisted and original sample
terms agree. -/
theorem Complex.frequencyPacketTwistedTerm_eq_original
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (modeOf : ℕ → ℤ)
    (m : ℤ)
    {n : ℕ}
    (hn : n ∈ Complex.frequencyPacket a b modeOf m) :
    Complex.exp
        (Complex.I *
          (Complex.realPhaseFrequencyTwist φ m n : ℂ)) =
      Complex.exp (Complex.I * (φ n : ℂ)) := by
  exact Complex.exp_I_realPhaseFrequencyTwist_nat_eq φ m n

/-- Each packet's twisted sum is its original sample sum. -/
theorem Complex.frequencyPacketTwistedSum_eq_original
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (modeOf : ℕ → ℤ)
    (m : ℤ) :
    Complex.frequencyPacketTwistedSum φ a b modeOf m =
      ∑ n ∈ Complex.frequencyPacket a b modeOf m,
        Complex.exp (Complex.I * (φ n : ℂ)) := by
  exact Finset.sum_congr rfl
    (fun n hn =>
      Complex.frequencyPacketTwistedTerm_eq_original φ a b modeOf m hn)

/-- Exact selected-family B-process reconstruction: selected twisted packets
plus their complement recover the ambient block. -/
theorem Complex.frequencyPacket_selected_add_complement_reconstruction
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (modeOf : ℕ → ℤ)
    (modes : Finset ℤ) :
    (∑ n ∈ Finset.Icc a b,
      Complex.exp (Complex.I * (φ n : ℂ))) =
      (∑ m ∈ modes,
        Complex.frequencyPacketTwistedSum φ a b modeOf m) +
      ∑ n ∈ Complex.frequencyPacketFamilyComplement a b modeOf modes,
        Complex.exp (Complex.I * (φ n : ℂ)) := by
  let packetUnion : Finset ℕ :=
    Complex.frequencyPacketFamilyUnion a b modeOf modes
  let packetComplement : Finset ℕ :=
    Complex.frequencyPacketFamilyComplement a b modeOf modes
  have hpartition : packetUnion ∪ packetComplement = Finset.Icc a b :=
    Complex.frequencyPacketFamilyUnion_union_complement_eq_block
      a b modeOf modes
  have hdisjoint : Disjoint packetUnion packetComplement :=
    Complex.frequencyPacketFamilyUnion_disjoint_complement
      a b modeOf modes
  have hunion_sum :
      (∑ n ∈ packetUnion ∪ packetComplement,
        Complex.exp (Complex.I * (φ n : ℂ))) =
        (∑ n ∈ packetUnion,
          Complex.exp (Complex.I * (φ n : ℂ))) +
        ∑ n ∈ packetComplement,
          Complex.exp (Complex.I * (φ n : ℂ)) :=
    Finset.sum_union hdisjoint
  have hpacket_disjoint :
      ∀ m₁ ∈ modes,
        ∀ m₂ ∈ modes,
          m₁ ≠ m₂ →
            Disjoint
              (Complex.frequencyPacket a b modeOf m₁)
              (Complex.frequencyPacket a b modeOf m₂) := by
    intro m₁ _hm₁ m₂ _hm₂ hne
    exact Complex.frequencyPacket_pairwiseDisjoint a b modeOf m₁ m₂ hne
  have hpacket_sum :
      (∑ n ∈ packetUnion,
        Complex.exp (Complex.I * (φ n : ℂ))) =
        ∑ m ∈ modes,
          Complex.frequencyPacketTwistedSum φ a b modeOf m := by
    have hraw :
        (∑ n ∈ packetUnion,
          Complex.exp (Complex.I * (φ n : ℂ))) =
          ∑ m ∈ modes,
            ∑ n ∈ Complex.frequencyPacket a b modeOf m,
              Complex.exp (Complex.I * (φ n : ℂ)) :=
      Finset.sum_biUnion hpacket_disjoint
    have htwisted :
        (∑ m ∈ modes,
          ∑ n ∈ Complex.frequencyPacket a b modeOf m,
            Complex.exp (Complex.I * (φ n : ℂ))) =
          ∑ m ∈ modes,
            Complex.frequencyPacketTwistedSum φ a b modeOf m := by
      exact Finset.sum_congr rfl
        (fun m _hm =>
        (Complex.frequencyPacketTwistedSum_eq_original
          φ a b modeOf m).symm)
    exact hraw.trans htwisted
  have hblock_sum :
      (∑ n ∈ Finset.Icc a b,
        Complex.exp (Complex.I * (φ n : ℂ))) =
        (∑ n ∈ packetUnion,
          Complex.exp (Complex.I * (φ n : ℂ))) +
        ∑ n ∈ packetComplement,
          Complex.exp (Complex.I * (φ n : ℂ)) :=
    Eq.trans
      (congrArg
        (fun samples : Finset ℕ =>
          ∑ n ∈ samples, Complex.exp (Complex.I * (φ n : ℂ)))
        hpartition.symm)
      hunion_sum
  exact
    Eq.trans hblock_sum
      (congrArg
        (fun active : ℂ =>
          active +
            ∑ n ∈ packetComplement,
              Complex.exp (Complex.I * (φ n : ℂ)))
        hpacket_sum)

/-- Active packet and complement estimates assemble additively into a direct
finite B-process block bound. -/
theorem Complex.norm_frequencyPacket_block_le_active_add_complement
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (modeOf : ℕ → ℤ)
    (modes : Finset ℤ)
    (activeBound complementBound : ℝ)
    (hactive :
      ‖∑ m ∈ modes,
        Complex.frequencyPacketTwistedSum φ a b modeOf m‖ ≤ activeBound)
    (hcomplement :
      ‖∑ n ∈ Complex.frequencyPacketFamilyComplement a b modeOf modes,
        Complex.exp (Complex.I * (φ n : ℂ))‖ ≤ complementBound) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
      activeBound + complementBound := by
  have hreconstruction :=
    Complex.frequencyPacket_selected_add_complement_reconstruction
      φ a b modeOf modes
  have htriangle :
      ‖(∑ m ∈ modes,
          Complex.frequencyPacketTwistedSum φ a b modeOf m) +
        ∑ n ∈ Complex.frequencyPacketFamilyComplement a b modeOf modes,
          Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
        ‖∑ m ∈ modes,
          Complex.frequencyPacketTwistedSum φ a b modeOf m‖ +
        ‖∑ n ∈ Complex.frequencyPacketFamilyComplement a b modeOf modes,
          Complex.exp (Complex.I * (φ n : ℂ))‖ :=
    norm_add_le _ _
  exact
    Eq.subst
      (motive := fun value : ℂ =>
        ‖value‖ ≤ activeBound + complementBound)
      hreconstruction.symm
      (le_trans htriangle (add_le_add hactive hcomplement))

/-- Exact finite B-process reconstruction for a covered mode partition. -/
theorem Complex.frequencyPacketFamily_sum_eq_twistedPacketSums
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (modeOf : ℕ → ℤ)
    (modes : Finset ℤ)
    (hcover : ∀ n : ℕ, n ∈ Finset.Icc a b → modeOf n ∈ modes) :
    (∑ n ∈ Finset.Icc a b,
      Complex.exp (Complex.I * (φ n : ℂ))) =
      ∑ m ∈ modes,
        Complex.frequencyPacketTwistedSum φ a b modeOf m := by
  have hunion :
      Complex.frequencyPacketFamilyUnion a b modeOf modes = Finset.Icc a b :=
    Complex.frequencyPacketFamilyUnion_eq_block a b modeOf modes hcover
  have hdisjoint :
      ∀ m₁ ∈ modes,
        ∀ m₂ ∈ modes,
          m₁ ≠ m₂ →
            Disjoint
              (Complex.frequencyPacket a b modeOf m₁)
              (Complex.frequencyPacket a b modeOf m₂) := by
    intro m₁ _ m₂ _ hne
    exact Complex.frequencyPacket_pairwiseDisjoint a b modeOf m₁ m₂ hne
  have hsum_original :
      (∑ n ∈ Complex.frequencyPacketFamilyUnion a b modeOf modes,
        Complex.exp (Complex.I * (φ n : ℂ))) =
        ∑ m ∈ modes,
          ∑ n ∈ Complex.frequencyPacket a b modeOf m,
            Complex.exp (Complex.I * (φ n : ℂ)) :=
    Finset.sum_biUnion hdisjoint
  have hsum_twisted :
      (∑ m ∈ modes,
          ∑ n ∈ Complex.frequencyPacket a b modeOf m,
            Complex.exp (Complex.I * (φ n : ℂ))) =
        ∑ m ∈ modes,
          Complex.frequencyPacketTwistedSum φ a b modeOf m := by
    exact Finset.sum_congr rfl
      (fun m _hm =>
        (Complex.frequencyPacketTwistedSum_eq_original φ a b modeOf m).symm)
  have hblock :
      (∑ n ∈ Finset.Icc a b,
        Complex.exp (Complex.I * (φ n : ℂ))) =
        ∑ m ∈ modes,
          ∑ n ∈ Complex.frequencyPacket a b modeOf m,
            Complex.exp (Complex.I * (φ n : ℂ)) :=
    (congrArg
      (fun samples : Finset ℕ =>
        ∑ n ∈ samples, Complex.exp (Complex.I * (φ n : ℂ)))
      hunion).symm.trans hsum_original
  exact hblock.trans hsum_twisted

/-- Exact canonical finite B-process reconstruction using the derivative-mode
image of the block. -/
theorem Complex.realPhaseDerivativeFrequencyMode_block_sum_eq_twistedPacketSums
    (φ : ℝ → ℝ)
    (a b : ℕ) :
    (∑ n ∈ Finset.Icc a b,
      Complex.exp (Complex.I * (φ n : ℂ))) =
      ∑ m ∈ Complex.realPhaseDerivativeFrequencyModes φ a b,
        Complex.frequencyPacketTwistedSum φ a b
          (Complex.realPhaseDerivativeFrequencyMode φ) m := by
  exact
    Complex.frequencyPacketFamily_sum_eq_twistedPacketSums
      φ a b
      (Complex.realPhaseDerivativeFrequencyMode φ)
      (Complex.realPhaseDerivativeFrequencyModes φ a b)
      (Complex.realPhaseDerivativeFrequencyMode_block_cover φ a b)

/-- Packetwise norm bounds assemble into a finite B-process bound. -/
theorem Complex.norm_frequencyPacketFamily_sum_le_sum_packetBounds
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (modeOf : ℕ → ℤ)
    (modes : Finset ℤ)
    (hcover : ∀ n : ℕ, n ∈ Finset.Icc a b → modeOf n ∈ modes)
    (bound : ℤ → ℝ)
    (hbound_nonneg : ∀ m : ℤ, m ∈ modes → 0 ≤ bound m)
    (hbound : ∀ m : ℤ, m ∈ modes →
      ‖Complex.frequencyPacketTwistedSum φ a b modeOf m‖ ≤ bound m) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
      ∑ m ∈ modes, bound m := by
  have hreconstruction :=
    Complex.frequencyPacketFamily_sum_eq_twistedPacketSums
      φ a b modeOf modes hcover
  have htriangle :
      ‖∑ m ∈ modes,
        Complex.frequencyPacketTwistedSum φ a b modeOf m‖ ≤
        ∑ m ∈ modes,
          ‖Complex.frequencyPacketTwistedSum φ a b modeOf m‖ :=
    norm_sum_le modes
      (fun m : ℤ => Complex.frequencyPacketTwistedSum φ a b modeOf m)
  have hbound_sum :
      (∑ m ∈ modes,
          ‖Complex.frequencyPacketTwistedSum φ a b modeOf m‖) ≤
        ∑ m ∈ modes, bound m := by
    exact Finset.sum_le_sum
      (fun m hm => hbound m hm)
  exact
    Eq.subst
      (motive := fun value : ℂ =>
        ‖value‖ ≤ ∑ m ∈ modes, bound m)
      hreconstruction.symm
      (le_trans htriangle hbound_sum)

/-- Packetwise estimates for an arbitrary selected active mode family assemble
additively, without requiring that family to cover the ambient block. -/
theorem Complex.norm_selectedFrequencyPacketSums_le_sum_packetBounds
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (modeOf : ℕ → ℤ)
    (modes : Finset ℤ)
    (bound : ℤ → ℝ)
    (hbound :
      ∀ m : ℤ,
        m ∈ modes →
          ‖Complex.frequencyPacketTwistedSum φ a b modeOf m‖ ≤ bound m) :
    ‖∑ m ∈ modes,
        Complex.frequencyPacketTwistedSum φ a b modeOf m‖ ≤
      ∑ m ∈ modes, bound m := by
  have htriangle :
      ‖∑ m ∈ modes,
        Complex.frequencyPacketTwistedSum φ a b modeOf m‖ ≤
        ∑ m ∈ modes,
          ‖Complex.frequencyPacketTwistedSum φ a b modeOf m‖ :=
    norm_sum_le modes
      (fun m : ℤ => Complex.frequencyPacketTwistedSum φ a b modeOf m)
  have hsum :
      (∑ m ∈ modes,
        ‖Complex.frequencyPacketTwistedSum φ a b modeOf m‖) ≤
          ∑ m ∈ modes, bound m :=
    Finset.sum_le_sum (fun m hm => hbound m hm)
  exact le_trans htriangle hsum

/-- A uniform active-window estimate sums using only the finite selected-center
cardinality. -/
theorem Complex.norm_selectedFrequencyPacketSums_le_card_mul
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (modeOf : ℕ → ℤ)
    (modes : Finset ℤ)
    (windowBound : ℝ)
    (hwindow_nonneg : 0 ≤ windowBound)
    (hbound :
      ∀ m : ℤ,
        m ∈ modes →
          ‖Complex.frequencyPacketTwistedSum φ a b modeOf m‖ ≤ windowBound) :
    ‖∑ m ∈ modes,
        Complex.frequencyPacketTwistedSum φ a b modeOf m‖ ≤
      (modes.card : ℝ) * windowBound := by
  exact
    Complex.finite_sum_norm_le_card_mul_of_norm_le
      modes
      (fun m : ℤ => Complex.frequencyPacketTwistedSum φ a b modeOf m)
      hwindow_nonneg hbound

/-- Direct selected-center B-process estimate from a uniform active-window
bound and additive complement-gap bounds. -/
theorem Complex.norm_frequencyPacket_block_le_card_mul_window_add_sum_gaps
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (modeOf : ℕ → ℤ)
    (modes : Finset ℤ)
    (windowBound : ℝ)
    (gapBound : ℕ → ℝ)
    (hwindow_nonneg : 0 ≤ windowBound)
    (hactive :
      ∀ m : ℤ,
        m ∈ modes →
          ‖Complex.frequencyPacketTwistedSum φ a b modeOf m‖ ≤ windowBound)
    (hgap :
      ∀ r : ℕ,
        r ∈ Complex.frequencyPacketComplementGapRange modes →
          ‖∑ n ∈ Complex.frequencyPacketComplementGap a b modeOf modes r,
            Complex.realPhaseOscillation φ n‖ ≤ gapBound r) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
      (modes.card : ℝ) * windowBound +
        ∑ r ∈ Complex.frequencyPacketComplementGapRange modes, gapBound r := by
  have hactive_total :=
    Complex.norm_selectedFrequencyPacketSums_le_card_mul
      φ a b modeOf modes windowBound hwindow_nonneg hactive
  have hcomplement_triangle :=
    Complex.norm_frequencyPacketFamilyComplement_sum_le_sum_gap_norms
      φ a b modeOf modes
  have hgap_sum :
      (∑ r ∈ Complex.frequencyPacketComplementGapRange modes,
        ‖∑ n ∈ Complex.frequencyPacketComplementGap a b modeOf modes r,
          Complex.realPhaseOscillation φ n‖) ≤
        ∑ r ∈ Complex.frequencyPacketComplementGapRange modes, gapBound r := by
    exact Finset.sum_le_sum (fun r hr => hgap r hr)
  have hcomplement_total :
      ‖∑ n ∈ Complex.frequencyPacketFamilyComplement a b modeOf modes,
        Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
        ∑ r ∈ Complex.frequencyPacketComplementGapRange modes, gapBound r := by
    have hoscillation_total :
        ‖∑ n ∈ Complex.frequencyPacketFamilyComplement a b modeOf modes,
          Complex.realPhaseOscillation φ n‖ ≤
          ∑ r ∈ Complex.frequencyPacketComplementGapRange modes, gapBound r :=
      le_trans hcomplement_triangle hgap_sum
    have hsum_eq :
        (∑ n ∈ Complex.frequencyPacketFamilyComplement a b modeOf modes,
          Complex.exp (Complex.I * (φ n : ℂ))) =
        ∑ n ∈ Complex.frequencyPacketFamilyComplement a b modeOf modes,
          Complex.realPhaseOscillation φ n :=
      Finset.sum_congr rfl (fun n _hn => rfl)
    exact
      Eq.subst
        (motive := fun value : ℂ =>
          ‖value‖ ≤
            ∑ r ∈ Complex.frequencyPacketComplementGapRange modes,
              gapBound r)
        hsum_eq.symm
        hoscillation_total
  exact
    Complex.norm_frequencyPacket_block_le_active_add_complement
      φ a b modeOf modes
      ((modes.card : ℝ) * windowBound)
      (∑ r ∈ Complex.frequencyPacketComplementGapRange modes, gapBound r)
      hactive_total hcomplement_total

/-- Canonical derivative-mode packetwise bounds assemble into a block bound. -/
theorem Complex.norm_realPhaseDerivativeFrequencyMode_block_le_sum_packetBounds
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (bound : ℤ → ℝ)
    (hbound_nonneg :
      ∀ m : ℤ,
        m ∈ Complex.realPhaseDerivativeFrequencyModes φ a b →
          0 ≤ bound m)
    (hbound :
      ∀ m : ℤ,
        m ∈ Complex.realPhaseDerivativeFrequencyModes φ a b →
          ‖Complex.frequencyPacketTwistedSum φ a b
              (Complex.realPhaseDerivativeFrequencyMode φ) m‖ ≤ bound m) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
      ∑ m ∈ Complex.realPhaseDerivativeFrequencyModes φ a b, bound m := by
  exact
    Complex.norm_frequencyPacketFamily_sum_le_sum_packetBounds
      φ a b
      (Complex.realPhaseDerivativeFrequencyMode φ)
      (Complex.realPhaseDerivativeFrequencyModes φ a b)
      (Complex.realPhaseDerivativeFrequencyMode_block_cover φ a b)
      bound hbound_nonneg hbound

end

end LFunctions
end Boundary
