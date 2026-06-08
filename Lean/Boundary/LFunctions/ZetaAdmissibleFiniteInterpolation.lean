import Boundary.LFunctions.ZetaAdmissibleBump

/-!
# Boundary admissible finite interpolation

This file packages the finite interpolation output of the admissible bump
library into a finite-type form that is easier to consume later on the
spectral/separation side.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped CompactlySupported

namespace ZetaAdmissibleFunction

/-- Finite interpolation on a finite type of real sampling points. -/
theorem exists_admissible_eval_fintype {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (hx : Function.Injective x) (a : ι → ℂ) :
    ∃ f : ZetaAdmissibleFunction, ∀ i, f (x i) = a i := by
  classical
  let s : Finset ℝ := Finset.univ.image x
  have hs : ∀ y ∈ s, ∃ i, x i = y := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨i, hi, rfl⟩
    exact ⟨i, rfl⟩
  let a' : ℝ → ℂ := fun y =>
    if hy : y ∈ s then
      let i := Classical.choose (hs y hy)
      a i
    else 0
  rcases exists_admissible_eval_finset (s := s) a' with ⟨f, hf⟩
  refine ⟨f, ?_⟩
  intro i
  have hmem : x i ∈ s := by
    exact Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩
  have hchoose : ∃ j, x j = x i := by
    exact hs (x i) hmem
  have hfx : f (x i) = a (Classical.choose hchoose) := by
    simpa [a', hmem] using hf (x i) hmem
  have hxi : x (Classical.choose hchoose) = x i := by
    exact Classical.choose_spec hchoose
  have hji : Classical.choose hchoose = i := hx hxi
  subst hji
  simpa using hfx

/-- A finite set admits an admissible Kronecker-delta function at any chosen point. -/
theorem exists_admissible_delta_finset {s : Finset ℝ} {x : ℝ} (hx : x ∈ s) :
    ∃ f : ZetaAdmissibleFunction, f x = (1 : ℂ) ∧ ∀ y ∈ s, y ≠ x → f y = 0 := by
  classical
  let a : ℝ → ℂ := fun y => if hy : y = x then 1 else 0
  rcases exists_admissible_eval_finset (s := s) a with ⟨f, hf⟩
  refine ⟨f, ?_⟩
  constructor
  · simpa [a] using hf x hx
  · intro y hy hyx
    have hy' : y ≠ x := hyx
    simpa [a, hy'] using hf y hy

/-- A finite set admits an admissible Kronecker delta at a chosen point, with compact support
contained in an explicit closed ball. -/
theorem exists_admissible_delta_finset_with_support_subset {s : Finset ℝ} {x : ℝ} (hx : x ∈ s) :
    ∃ f : ZetaAdmissibleFunction,
      f x = (1 : ℂ) ∧
      (∀ y ∈ s, y ≠ x → f y = 0) ∧
      ∃ rOut : ℝ, 0 < rOut ∧
        Function.support f ⊆ Metric.closedBall x rOut := by
  classical
  have hsep : ∃ rOut : ℝ, 0 < rOut ∧ ∀ y ∈ s.erase x, rOut ≤ dist y x := by
    exact exists_radius_separating_finset (s := s.erase x) (x := x) (by
      simp [Finset.mem_erase])
  rcases hsep with ⟨rOut, hrOut, hsep⟩
  let f : ZetaAdmissibleFunction :=
    admissibleBump (c := x) (rOut / 2) rOut (by linarith) (by
      have : rOut / 2 < rOut := by linarith
      exact this)
  refine ⟨f, ?_, ?_, rOut, hrOut, ?_⟩
  · simp [f, admissibleBump_apply_center]
  · intro y hy hyx
    have hyerase : y ∈ s.erase x := by
      simpa [Finset.mem_erase, hyx] using hy
    have hdist : rOut ≤ dist y x := hsep y hyerase
    exact admissibleBump_zero_of_le_dist (c := x) (rIn := rOut / 2) (rOut := rOut)
      (by linarith) (by linarith) (by linarith)
  · intro y hy
    by_contra hyc
    exact hy (by
      simpa [Function.mem_support] using
        admissibleBump_eq_zero_of_not_mem_closedBall (c := x) (rIn := rOut / 2) (rOut := rOut)
          (by linarith) (by linarith) hyc)

/-- A finite set admits an admissible Kronecker delta at a chosen point, with compact support. -/
theorem exists_admissible_delta_finset_with_support {s : Finset ℝ} {x : ℝ} (hx : x ∈ s) :
    ∃ f : ZetaAdmissibleFunction,
      f x = (1 : ℂ) ∧
      (∀ y ∈ s, y ≠ x → f y = 0) ∧
      HasCompactSupport f := by
  classical
  have hsep : ∃ rOut : ℝ, 0 < rOut ∧ ∀ y ∈ s.erase x, rOut ≤ dist y x := by
    exact exists_radius_separating_finset (s := s.erase x) (x := x) (by
      simp [Finset.mem_erase])
  rcases hsep with ⟨rOut, hrOut, hsep⟩
  let f : ZetaAdmissibleFunction :=
    admissibleBump (c := x) (rOut / 2) rOut (by linarith) (by
      have : rOut / 2 < rOut := by linarith
      exact this)
  refine ⟨f, ?_, ?_, ?_⟩
  · simp [f, admissibleBump_apply_center]
  · intro y hy hyx
    have hyerase : y ∈ s.erase x := by
      simpa [Finset.mem_erase, hyx] using hy
    have hdist : rOut ≤ dist y x := hsep y hyerase
    exact admissibleBump_zero_of_le_dist (c := x) (rIn := rOut / 2) (rOut := rOut)
      (by linarith) (by linarith) (by linarith)
  · simpa [f] using admissibleBump_hasCompactSupport (c := x) (rIn := rOut / 2) (rOut := rOut)
      (by linarith) (by linarith)

/-- A finite set admits a family of compactly supported admissible Kronecker deltas. -/
theorem exists_admissible_delta_family_with_support {s : Finset ℝ} :
    ∃ F : ∀ x ∈ s, ZetaAdmissibleFunction,
      (∀ x hx, F x hx x = (1 : ℂ)) ∧
      (∀ x hx y hy, y ≠ x → F x hx y = 0) ∧
      (∀ x hx, HasCompactSupport (F x hx)) := by
  classical
  refine ⟨fun x hx => Classical.choose (exists_admissible_delta_finset_with_support (s := s) (x := x) hx), ?_⟩
  constructor
  · intro x hx
    exact (Classical.choose_spec (exists_admissible_delta_finset_with_support (s := s) (x := x) hx)).1
  constructor
  · intro x hx y hy hxy
    exact (Classical.choose_spec (exists_admissible_delta_finset_with_support (s := s) (x := x) hx)).2.1 y hy hxy
  · intro x hx
    exact (Classical.choose_spec (exists_admissible_delta_finset_with_support (s := s) (x := x) hx)).2.2

/-- A finite type admits a family of compactly supported admissible Kronecker deltas. -/
theorem exists_admissible_delta_fintype_with_support {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (hx : Function.Injective x) :
    ∃ F : ∀ i, ZetaAdmissibleFunction,
      (∀ i, F i (x i) = (1 : ℂ)) ∧
      (∀ i j, j ≠ i → F i (x j) = 0) ∧
      (∀ i, HasCompactSupport (F i)) := by
  classical
  let s : Finset ℝ := Finset.univ.image x
  have hxmem : ∀ i, x i ∈ s := by
    intro i
    exact Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩
  rcases exists_admissible_delta_family_with_support (s := s) with ⟨F, hF1, hF0, hFc⟩
  refine ⟨fun i => F (x i) (hxmem i), ?_⟩
  constructor
  · intro i
    exact hF1 (x i) (hxmem i)
  constructor
  · intro i j hj
    apply hF0 (x i) (hxmem i) (x j) (hxmem j)
    intro h
    apply hj
    exact hx h
  · intro i
    exact hFc (x i) (hxmem i)

/-- A finite type admits a family of admissible Kronecker deltas with an explicit closed-ball
support bound at each point. -/
theorem exists_admissible_delta_fintype_with_support_subset {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (hx : Function.Injective x) :
    ∃ F : ∀ i, ZetaAdmissibleFunction,
      (∀ i, F i (x i) = (1 : ℂ)) ∧
      (∀ i j, j ≠ i → F i (x j) = 0) ∧
      (∀ i, ∃ rOut : ℝ, 0 < rOut ∧ Function.support (F i) ⊆ Metric.closedBall (x i) rOut) := by
  classical
  let s : Finset ℝ := Finset.univ.image x
  have hxmem : ∀ i, x i ∈ s := by
    intro i
    exact Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩
  refine ⟨fun i => Classical.choose (exists_admissible_delta_finset_with_support_subset
      (s := s) (x := x i) (hx := hxmem i)), ?_⟩
  constructor
  · intro i
    exact (Classical.choose_spec
      (exists_admissible_delta_finset_with_support_subset (s := s) (x := x i) (hx := hxmem i))).1
  constructor
  · intro i j hj
    have h := (Classical.choose_spec
      (exists_admissible_delta_finset_with_support_subset (s := s) (x := x i) (hx := hxmem i))).2.1
    exact h (x j) (hxmem j) hj
  · intro i
    rcases (Classical.choose_spec
      (exists_admissible_delta_finset_with_support_subset (s := s) (x := x i) (hx := hxmem i))).2.2
      with ⟨rOut, hrOut, hsupp⟩
    exact ⟨rOut, hrOut, hsupp⟩

/-- A finite type admits a compactly supported interpolation witness. -/
theorem exists_admissible_eval_fintype_with_support {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (hx : Function.Injective x) (a : ι → ℂ) :
    ∃ f : ZetaAdmissibleFunction, (∀ i, f (x i) = a i) ∧ HasCompactSupport f := by
  classical
  rcases exists_admissible_delta_fintype_with_support (x := x) hx with ⟨F, hF1, hF0, hFc⟩
  let f : ZetaAdmissibleFunction := Finset.sum Finset.univ fun i => (a i) • F i
  refine ⟨f, ?_, ?_⟩
  · intro i
    have hsum :
        f (x i) = ∑ j : ι, a j * F j (x i) := by
      simp [f, ZetaAdmissibleFunction.smul_apply, mul_comm, mul_left_comm, mul_assoc]
    rw [hsum]
    have hsingle :
        (∑ j : ι, a j * F j (x i)) = a i * F i (x i) := by
      refine Finset.sum_eq_single i ?_ ?_ ?_
      · intro j hj hji
        simp [hF0 j i hji]
      · intro hi
        exact False.elim (hi (Finset.mem_univ i))
      · simp [hF1 i]
    rw [hsingle, hF1 i]
  · simpa [f] using ZetaAdmissibleFunction.hasCompactSupport_sum Finset.univ fun i => (a i) • F i

/-- A finite type admits a compactly supported interpolant whose support is controlled by the
support of the chosen delta basis. -/
theorem exists_admissible_eval_fintype_with_support_and_basis_support {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (hx : Function.Injective x) (a : ι → ℂ) :
    ∃ F : ∀ i, ZetaAdmissibleFunction,
      (∀ i, F i (x i) = (1 : ℂ)) ∧
      (∀ i j, j ≠ i → F i (x j) = 0) ∧
      (∀ i, HasCompactSupport (F i)) ∧
      ∃ f : ZetaAdmissibleFunction,
        (∀ i, f (x i) = a i) ∧
        HasCompactSupport f ∧
        Function.support f ⊆ Finset.univ.biUnion fun i => Function.support (F i) := by
  classical
  rcases exists_admissible_delta_fintype_with_support (x := x) hx with ⟨F, hF1, hF0, hFc⟩
  let f : ZetaAdmissibleFunction := Finset.sum Finset.univ fun i => (a i) • F i
  refine ⟨F, hF1, hF0, hFc, f, ?_, ?_, ?_⟩
  · intro i
    have hsum :
        f (x i) = ∑ j : ι, a j * F j (x i) := by
      simp [f, ZetaAdmissibleFunction.smul_apply, mul_comm, mul_left_comm, mul_assoc]
    rw [hsum]
    have hsingle :
        (∑ j : ι, a j * F j (x i)) = a i * F i (x i) := by
      refine Finset.sum_eq_single i ?_ ?_ ?_
      · intro j hj hji
        simp [hF0 j i hji]
      · intro hi
        exact False.elim (hi (Finset.mem_univ i))
      · simp [hF1 i]
    rw [hsingle, hF1 i]
  · simpa [f] using ZetaAdmissibleFunction.hasCompactSupport_sum Finset.univ fun i => (a i) • F i
  · simpa [f] using
      ZetaAdmissibleFunction.support_sum_smul_subset (s := Finset.univ) (c := a) (f := F)

/-- A finite type admits a compactly supported interpolant together with a delta basis whose
supports are individually contained in closed balls. -/
theorem exists_admissible_eval_fintype_with_basis_closedBall_support {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (hx : Function.Injective x) (a : ι → ℂ) :
    ∃ F : ∀ i, ZetaAdmissibleFunction,
      (∀ i, F i (x i) = (1 : ℂ)) ∧
      (∀ i j, j ≠ i → F i (x j) = 0) ∧
      (∀ i, ∃ rOut : ℝ, 0 < rOut ∧ Function.support (F i) ⊆ Metric.closedBall (x i) rOut) ∧
      ∃ f : ZetaAdmissibleFunction,
        (∀ i, f (x i) = a i) ∧
        HasCompactSupport f ∧
        Function.support f ⊆ Finset.univ.biUnion fun i => Function.support (F i) := by
  classical
  rcases exists_admissible_delta_fintype_with_support_subset_fintype (x := x) hx with
    ⟨F, hF1, hF0, hFr⟩
  let f : ZetaAdmissibleFunction := Finset.sum Finset.univ fun i => (a i) • F i
  refine ⟨F, hF1, hF0, hFr, f, ?_, ?_, ?_⟩
  · intro i
    have hsum :
        f (x i) = ∑ j : ι, a j * F j (x i) := by
      simp [f, ZetaAdmissibleFunction.smul_apply, mul_comm, mul_left_comm, mul_assoc]
    rw [hsum]
    have hsingle :
        (∑ j : ι, a j * F j (x i)) = a i * F i (x i) := by
      refine Finset.sum_eq_single i ?_ ?_ ?_
      · intro j hj hji
        simp [hF0 j i hji]
      · intro hi
        exact False.elim (hi (Finset.mem_univ i))
      · simp [hF1 i]
    rw [hsingle, hF1 i]
  · simpa [f] using ZetaAdmissibleFunction.hasCompactSupport_sum Finset.univ fun i => (a i) • F i
  · simpa [f] using
      ZetaAdmissibleFunction.support_sum_smul_subset (s := Finset.univ) (c := a) (f := F)

/-- A finite type admits a compactly supported interpolant whose support is contained in a union
of explicit closed balls around the sample points. -/
theorem exists_admissible_eval_fintype_with_closedBall_support {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (hx : Function.Injective x) (a : ι → ℂ) :
    ∃ (F : ∀ i, ZetaAdmissibleFunction) (r : ι → ℝ),
      (∀ i, F i (x i) = (1 : ℂ)) ∧
      (∀ i j, j ≠ i → F i (x j) = 0) ∧
      (∀ i, 0 < r i ∧ Function.support (F i) ⊆ Metric.closedBall (x i) (r i)) ∧
      ∃ f : ZetaAdmissibleFunction,
        (∀ i, f (x i) = a i) ∧
        HasCompactSupport f ∧
        Function.support f ⊆ Finset.univ.biUnion fun i => Metric.closedBall (x i) (r i) := by
  classical
  rcases exists_admissible_eval_fintype_with_basis_closedBall_support (x := x) hx a with
    ⟨F, hF1, hF0, hFr, f, hf, hcomp, hsupp⟩
  choose r hrpos hsubset using hFr
  refine ⟨F, r, hF1, hF0, ?_, f, hf, hcomp, ?_⟩
  · intro i
    exact ⟨hrpos i, hsubset i⟩
  · intro y hy
    rcases Finset.mem_biUnion.mp hsupp hy with ⟨i, hi, hyi⟩
    exact Finset.mem_biUnion.2 ⟨i, hi, hsubset i hyi⟩

/-- A finite type admits a compactly supported interpolant together with a closed-ball basis and
the canonical surfaces. -/
theorem exists_admissible_eval_fintype_with_closedBall_support_and_surfaces {ι : Type*}
    [Fintype ι] (x : ι → ℝ) (hx : Function.Injective x) (a : ι → ℂ) :
    ∃ (F : ∀ i, ZetaAdmissibleFunction) (r : ι → ℝ),
      (∀ i, F i (x i) = (1 : ℂ)) ∧
      (∀ i j, j ≠ i → F i (x j) = 0) ∧
      (∀ i, 0 < r i ∧ Function.support (F i) ⊆ Metric.closedBall (x i) (r i)) ∧
      ∃ f : ZetaAdmissibleFunction,
        (∀ i, f (x i) = a i) ∧
        HasCompactSupport f ∧
        Function.support f ⊆ Finset.univ.biUnion fun i => Metric.closedBall (x i) (r i) ∧
        (spectralModel f = toZetaExplicitFormulaTransform f) ∧
        (interpolationSurface f = (spectralModel f, separatingProbe f)) ∧
        (packetTransportSurface f = (spectralModel f, separatingProbe f)) := by
  rcases exists_admissible_eval_fintype_with_closedBall_support (x := x) hx a with
    ⟨F, r, hF1, hF0, hr, f, hf, hcomp, hsupp⟩
  refine ⟨F, r, hF1, hF0, hr, f, hf, hcomp, hsupp, ZetaAdmissibleFunction.spectralModel_eq f, ?_,
    ?_⟩
  · rw [ZetaAdmissibleFunction.interpolationSurface_eq]
  · rw [ZetaAdmissibleFunction.packetTransportSurface_pair]

/-- A finite type admits a localized interpolant with the canonical surfaces, with the basis
existence hidden behind the theorem statement. -/
theorem exists_admissible_eval_fintype_with_closedBall_support_surfaces {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (hx : Function.Injective x) (a : ι → ℂ) :
    ∃ f : ZetaAdmissibleFunction,
      (∀ i, f (x i) = a i) ∧
      HasCompactSupport f ∧
      (spectralModel f = toZetaExplicitFormulaTransform f) ∧
      (interpolationSurface f = (spectralModel f, separatingProbe f)) ∧
      (packetTransportSurface f = (spectralModel f, separatingProbe f)) ∧
      ∃ (F : ∀ i, ZetaAdmissibleFunction) (r : ι → ℝ),
        (∀ i, F i (x i) = (1 : ℂ)) ∧
        (∀ i j, j ≠ i → F i (x j) = 0) ∧
        (∀ i, 0 < r i ∧ Function.support (F i) ⊆ Metric.closedBall (x i) (r i)) ∧
        Function.support f ⊆ Finset.univ.biUnion fun i => Metric.closedBall (x i) (r i) := by
  rcases exists_admissible_eval_fintype_with_closedBall_support_and_surfaces (x := x) hx a with
    ⟨F, r, hF1, hF0, hr, f, hf, hcomp, hsupp, hs, htp⟩
  refine ⟨f, hf, hcomp, hs, ?_, htp, F, r, hF1, hF0, hr, hsupp⟩
  rw [ZetaAdmissibleFunction.interpolationSurface_eq]

/-- Translating a localized finite interpolant localizes it at translated sample points. -/
theorem support_translate_eval_fintype_with_closedBall_support_surfaces {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (hx : Function.Injective x) (a : ι → ℂ) (c : ℝ) :
    ∃ f : ZetaAdmissibleFunction,
      (∀ i, f (x i + c) = a i) ∧
      HasCompactSupport f ∧
      (spectralModel f = toZetaExplicitFormulaTransform f) ∧
      (interpolationSurface f = (spectralModel f, separatingProbe f)) ∧
      (packetTransportSurface f = (spectralModel f, separatingProbe f)) ∧
      Function.support f =
        (fun y => y - c) ⁻¹' Function.support
          (Classical.choose (exists_admissible_eval_fintype_with_closedBall_support_surfaces
            (x := x) hx a).1) := by
  classical
  rcases exists_admissible_eval_fintype_with_closedBall_support_surfaces (x := x) hx a with
    ⟨f0, hf0, hcomp, hs, hinterp, htp, F, r, hF1, hF0, hr, hsupp⟩
  refine ⟨translate c f0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have h := hf0 i
    simpa [ZetaAdmissibleFunction.translate_apply] using h
  · exact hasCompactSupport_translate c f0
  · exact by
      simpa [ZetaAdmissibleFunction.translate] using hs
  · exact by
      simpa [ZetaAdmissibleFunction.translate] using hinterp
  · exact by
      simpa [ZetaAdmissibleFunction.translate] using htp
  · simpa [ZetaAdmissibleFunction.support_translate] using
      congrArg (Function.support) (rfl : translate c f0 = translate c f0)

/-- Translating a localized interpolant translates the explicit closed-ball support bound. -/
theorem support_translate_eval_fintype_with_closedBall_support {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (hx : Function.Injective x) (a : ι → ℂ) (c : ℝ) :
    ∃ (f : ZetaAdmissibleFunction) (F : ∀ i, ZetaAdmissibleFunction) (r : ι → ℝ),
      (∀ i, F i (x i) = (1 : ℂ)) ∧
      (∀ i j, j ≠ i → F i (x j) = 0) ∧
      (∀ i, 0 < r i ∧ Function.support (F i) ⊆ Metric.closedBall (x i) (r i)) ∧
      (∀ i, f (x i + c) = a i) ∧
      HasCompactSupport f ∧
      Function.support f ⊆
        (fun y => y - c) ⁻¹' Finset.univ.biUnion fun i => Metric.closedBall (x i) (r i) := by
  classical
  rcases exists_admissible_eval_fintype_with_closedBall_support_and_surfaces (x := x) hx a with
    ⟨F, r, hF1, hF0, hr, f0, hf0, hcomp0, hsupp0, hs0, htp0⟩
  refine ⟨translate c f0, F, r, hF1, hF0, hr, ?_, ?_, ?_⟩
  · intro i
    simpa [ZetaAdmissibleFunction.translate_apply] using hf0 i
  · exact hasCompactSupport_translate c f0
  · simpa [ZetaAdmissibleFunction.support_translate] using
      (show Function.support (translate c f0) ⊆ (fun y => y - c) ⁻¹'
        Finset.univ.biUnion fun i => Metric.closedBall (x i) (r i) from by
          intro y hy
          have hy' : y - c ∈ Function.support f0 := by
            simpa [ZetaAdmissibleFunction.support_translate] using hy
          have hset := hsupp0 hy'
          rcases Finset.mem_biUnion.mp hset with ⟨i, hi, hyi⟩
          exact by
            simp [Set.mem_preimage] at *
            exact Finset.mem_biUnion.2 ⟨i, hi, hyi⟩)

/-- Reflecting a localized finite interpolant localizes it at the reflected sample points. -/
theorem support_reflect_eval_fintype_with_closedBall_support_surfaces {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (hx : Function.Injective x) (a : ι → ℂ) :
    ∃ f : ZetaAdmissibleFunction,
      (∀ i, f (-x i) = a i) ∧
      HasCompactSupport f ∧
      (spectralModel f = toZetaExplicitFormulaTransform f) ∧
      (interpolationSurface f = (spectralModel f, separatingProbe f)) ∧
      (packetTransportSurface f = (spectralModel f, separatingProbe f)) ∧
      ∃ (F : ∀ i, ZetaAdmissibleFunction) (r : ι → ℝ),
        (∀ i, F i (x i) = (1 : ℂ)) ∧
        (∀ i j, j ≠ i → F i (x j) = 0) ∧
        (∀ i, 0 < r i ∧ Function.support (F i) ⊆ Metric.closedBall (x i) (r i)) ∧
        Function.support f ⊆
          (fun y => -y) ⁻¹' Finset.univ.biUnion fun i => Metric.closedBall (x i) (r i) := by
  classical
  rcases exists_admissible_eval_fintype_with_closedBall_support_and_surfaces (x := x) hx a with
    ⟨F, r, hF1, hF0, hr, f0, hf0, hcomp0, hsupp0, hs0, htp0⟩
  refine ⟨reflect f0, ?_, ?_, ?_, ?_, ?_, F, r, hF1, hF0, hr, ?_⟩
  · intro i
    simpa [ZetaAdmissibleFunction.reflect_apply] using hf0 i
  · exact hasCompactSupport_reflect f0
  · exact by simpa [ZetaAdmissibleFunction.reflect] using hs0
  · exact by simpa [ZetaAdmissibleFunction.reflect] using hs0
  · exact by simpa [ZetaAdmissibleFunction.reflect] using htp0
  · intro y hy
    have hy' : -y ∈ Function.support f0 := by
      simpa [ZetaAdmissibleFunction.support_reflect] using hy
    have hset := hsupp0 hy'
    rcases Finset.mem_biUnion.mp hset with ⟨i, hi, hyi⟩
    exact Finset.mem_biUnion.2 ⟨i, hi, hyi⟩

/-- The translated localized interpolant has support controlled by the translated support of the
untranslated localized witness. -/
theorem support_translate_eval_fintype_with_closedBall_support_surfaces_support {ι : Type*}
    [Fintype ι] (x : ι → ℝ) (hx : Function.Injective x) (a : ι → ℂ) (c : ℝ) :
    ∃ f : ZetaAdmissibleFunction,
      (∀ i, f (x i + c) = a i) ∧
      HasCompactSupport f ∧
      Function.support f =
        (fun y => y - c) ⁻¹'
          Function.support
            (Classical.choose
              (exists_admissible_eval_fintype_with_closedBall_support_surfaces (x := x) hx a).1) := by
  classical
  rcases support_translate_eval_fintype_with_closedBall_support_surfaces (x := x) hx a c with
    ⟨f, hf, hcomp, hs, hinterp, htp, hsupp⟩
  refine ⟨f, hf, hcomp, ?_⟩
  simpa [ZetaAdmissibleFunction.support_translate] using hsupp

/-- Scaling a localized finite interpolant localizes it at the scaled sample points. -/
theorem support_scale_eval_fintype_with_closedBall_support_surfaces {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (hx : Function.Injective x) (a : ι → ℂ) (t : ℝ) :
    ∃ f : ZetaAdmissibleFunction,
      (∀ i, f (t * x i) = a i) ∧
      HasCompactSupport f ∧
      (spectralModel f = toZetaExplicitFormulaTransform f) ∧
      (interpolationSurface f = (spectralModel f, separatingProbe f)) ∧
      (packetTransportSurface f = (spectralModel f, separatingProbe f)) ∧
      ∃ (F : ∀ i, ZetaAdmissibleFunction) (r : ι → ℝ),
        (∀ i, F i (x i) = (1 : ℂ)) ∧
        (∀ i j, j ≠ i → F i (x j) = 0) ∧
        (∀ i, 0 < r i ∧ Function.support (F i) ⊆ Metric.closedBall (x i) (r i)) ∧
        Function.support f ⊆
          (fun y => t * y) ⁻¹' Finset.univ.biUnion fun i => Metric.closedBall (x i) (r i) := by
  classical
  rcases exists_admissible_eval_fintype_with_closedBall_support_and_surfaces (x := x) hx a with
    ⟨F, r, hF1, hF0, hr, f0, hf0, hcomp0, hsupp0, hs0, htp0⟩
  refine ⟨scale t f0, ?_, ?_, ?_, ?_, ?_, F, r, hF1, hF0, hr, ?_⟩
  · intro i
    simpa [ZetaAdmissibleFunction.scale_apply] using hf0 i
  · exact hasCompactSupport_scale t f0
  · exact by simpa [ZetaAdmissibleFunction.scale] using hs0
  · exact by simpa [ZetaAdmissibleFunction.scale] using hs0
  · exact by simpa [ZetaAdmissibleFunction.scale] using htp0
  · intro y hy
    have hy' : t * y ∈ Function.support f0 := by
      simpa [ZetaAdmissibleFunction.support_scale] using hy
    have hset := hsupp0 hy'
    rcases Finset.mem_biUnion.mp hset with ⟨i, hi, hyi⟩
    exact Finset.mem_biUnion.2 ⟨i, hi, hyi⟩

/-- A finite affine transport theorem packages the affine localized interpolant with the basis
and explicit closed-ball support control. -/
theorem support_affine_eval_fintype_with_closedBall_support_surfaces {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (hx : Function.Injective x) (a : ι → ℂ) (t c : ℝ) (ht : t ≠ 0) :
    ∃ f : ZetaAdmissibleFunction,
      (∀ i, f (t * x i + c) = a i) ∧
      HasCompactSupport f ∧
      (spectralModel f = toZetaExplicitFormulaTransform f) ∧
      (interpolationSurface f = (spectralModel f, separatingProbe f)) ∧
      (packetTransportSurface f = (spectralModel f, separatingProbe f)) ∧
      ∃ (F : ∀ i, ZetaAdmissibleFunction) (r : ι → ℝ),
        (∀ i, F i (x i) = (1 : ℂ)) ∧
        (∀ i j, j ≠ i → F i (x j) = 0) ∧
        (∀ i, 0 < r i ∧ Function.support (F i) ⊆ Metric.closedBall (x i) (r i)) ∧
        Function.support f ⊆
          (fun y => y - c) ⁻¹' (fun y => t * y) ⁻¹'
            Finset.univ.biUnion fun i => Metric.closedBall (x i) (r i) := by
  classical
  rcases support_affine_eval_fintype_with_closedBall_support_surfaces (x := x) hx a t c ht with
    ⟨f, hf, hcomp, hs, hinterp, htp, F, r, hF1, hF0, hr, hsupp⟩
  refine ⟨f, hf, hcomp, hs, hinterp, htp, F, r, hF1, hF0, hr, hsupp⟩

/-- The affine transport of a localized finite interpolant is a localized affine interpolant. -/
theorem affineTransport_eval_fintype_with_closedBall_support_surfaces {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (hx : Function.Injective x) (a : ι → ℂ) (t c : ℝ) (ht : t ≠ 0) :
    ∃ f : ZetaAdmissibleFunction,
      (∀ i, f (t * x i + c) = a i) ∧
      HasCompactSupport f ∧
      (spectralModel f = toZetaExplicitFormulaTransform f) ∧
      (interpolationSurface f = (spectralModel f, separatingProbe f)) ∧
      (packetTransportSurface f = (spectralModel f, separatingProbe f)) := by
  rcases support_affine_eval_fintype_with_closedBall_support_surfaces (x := x) hx a t c ht with
    ⟨f, hf, hcomp, hs, hinterp, htp, F, r, hF1, hF0, hr, hsupp⟩
  refine ⟨affineTransport t c f, ?_, hasCompactSupport_affineTransport t c f, ?_, ?_, ?_⟩
  · intro i
    simpa [ZetaAdmissibleFunction.affineTransport_apply] using hf i
  · simpa [ZetaAdmissibleFunction.affineTransport] using hs
  · simpa [ZetaAdmissibleFunction.affineTransport] using hinterp
  · simpa [ZetaAdmissibleFunction.affineTransport] using htp

/-- The affine transport of a localized finite interpolant carries the same basis and radii
data. -/
theorem affineTransport_eval_fintype_with_closedBall_support_surfaces_support {ι : Type*}
    [Fintype ι] (x : ι → ℝ) (hx : Function.Injective x) (a : ι → ℂ) (t c : ℝ) (ht : t ≠ 0) :
    ∃ f : ZetaAdmissibleFunction,
      (∀ i, f (t * x i + c) = a i) ∧
      HasCompactSupport f ∧
      Function.support f =
        (fun y => y - c) ⁻¹' (fun y => t * y) ⁻¹'
          Function.support
            (Classical.choose
              (support_affine_eval_fintype_with_closedBall_support_surfaces
                (x := x) hx a t c ht).1) := by
  rcases support_affine_eval_fintype_with_closedBall_support_surfaces (x := x) hx a t c ht with
    ⟨f, hf, hcomp, hs, hinterp, htp, F, r, hF1, hF0, hr, hsupp⟩
  refine ⟨affineTransport t c f, ?_, hasCompactSupport_affineTransport t c f, ?_⟩
  · intro i
    simpa [ZetaAdmissibleFunction.affineTransport_apply] using hf i
  · simpa [ZetaAdmissibleFunction.affineTransport, ZetaAdmissibleFunction.support_translate_scale]
      using hsupp

/-- A finite-type interpolant can be chosen with compact support and transport-surface data. -/
theorem exists_admissible_eval_fintype_with_support_and_transportSurface {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (hx : Function.Injective x) (a : ι → ℂ) :
    ∃ f : ZetaAdmissibleFunction,
      (∀ i, f (x i) = a i) ∧
      HasCompactSupport f ∧
      (packetTransportSurface f = (spectralModel f, separatingProbe f)) := by
  rcases exists_admissible_eval_fintype_with_support (x := x) hx a with ⟨f, hf, hcomp⟩
  refine ⟨f, hf, hcomp, ?_⟩
  rw [ZetaAdmissibleFunction.packetTransportSurface_pair]

/-- A finite-type interpolant can be chosen with compact support and spectral-model data. -/
theorem exists_admissible_eval_fintype_with_support_and_spectralModel {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (hx : Function.Injective x) (a : ι → ℂ) :
    ∃ f : ZetaAdmissibleFunction,
      (∀ i, f (x i) = a i) ∧
      HasCompactSupport f ∧
      (spectralModel f = toZetaExplicitFormulaTransform f) := by
  rcases exists_admissible_eval_fintype_with_support (x := x) hx a with ⟨f, hf, hcomp⟩
  refine ⟨f, hf, hcomp, ZetaAdmissibleFunction.spectralModel_eq f⟩

/-- A finite-type interpolant can be chosen with compact support and the full canonical surfaces. -/
theorem exists_admissible_eval_fintype_with_support_and_surfaces {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (hx : Function.Injective x) (a : ι → ℂ) :
    ∃ f : ZetaAdmissibleFunction,
      (∀ i, f (x i) = a i) ∧
      HasCompactSupport f ∧
      (spectralModel f = toZetaExplicitFormulaTransform f) ∧
      (interpolationSurface f = (spectralModel f, separatingProbe f)) ∧
      (packetTransportSurface f = (spectralModel f, separatingProbe f)) := by
  rcases exists_admissible_eval_fintype_with_support_and_spectralModel (x := x) hx a with
    ⟨f, hf, hcomp, hs⟩
  refine ⟨f, hf, hcomp, hs, ?_, ?_⟩
  · rw [ZetaAdmissibleFunction.interpolationSurface_eq]
  · rw [ZetaAdmissibleFunction.packetTransportSurface_pair]

/-- A finite type admits a family of compactly supported admissible Kronecker deltas,
packaged directly as the finite basis theorem. -/
theorem exists_admissible_delta_family_with_support_fintype {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (hx : Function.Injective x) :
    ∃ F : ∀ i, ZetaAdmissibleFunction,
      (∀ i, F i (x i) = (1 : ℂ)) ∧
      (∀ i j, j ≠ i → F i (x j) = 0) ∧
      (∀ i, HasCompactSupport (F i)) := by
  simpa using exists_admissible_delta_fintype_with_support (x := x) hx

/-- A finite type admits a family of admissible Kronecker deltas with explicit closed-ball
support bounds. -/
theorem exists_admissible_delta_family_with_support_subset_fintype {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (hx : Function.Injective x) :
    ∃ F : ∀ i, ZetaAdmissibleFunction,
      (∀ i, F i (x i) = (1 : ℂ)) ∧
      (∀ i j, j ≠ i → F i (x j) = 0) ∧
      (∀ i, ∃ rOut : ℝ, 0 < rOut ∧ Function.support (F i) ⊆ Metric.closedBall (x i) rOut) := by
  classical
  rcases exists_admissible_delta_fintype_with_support_subset (x := x) hx with ⟨F, hF1, hF0, hFr⟩
  refine ⟨F, hF1, hF0, hFr⟩

/-- A finite type of real sampling points admits an admissible Kronecker delta at any index. -/
theorem exists_admissible_delta_fintype {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (hx : Function.Injective x) (i₀ : ι) :
    ∃ f : ZetaAdmissibleFunction, f (x i₀) = (1 : ℂ) ∧ ∀ j, j ≠ i₀ → f (x j) = 0 := by
  classical
  let s : Finset ℝ := Finset.univ.image x
  have hxmem : x i₀ ∈ s := by
    exact Finset.mem_image.2 ⟨i₀, Finset.mem_univ i₀, rfl⟩
  rcases exists_admissible_delta_finset (s := s) (x := x i₀) hxmem with ⟨f, hf1, hf0⟩
  refine ⟨f, hf1, ?_⟩
  intro j hj
  apply hf0
  · exact Finset.mem_image.2 ⟨j, Finset.mem_univ j, rfl⟩
  · intro h
    apply hj
    exact hx h

/-- A finite set of sampling points admits a Kronecker-delta family of admissible functions. -/
theorem exists_admissible_delta_family {s : Finset ℝ} :
    ∃ F : ∀ x ∈ s, ZetaAdmissibleFunction,
      (∀ x hx, F x hx x = (1 : ℂ)) ∧
      (∀ x hx y hy, y ≠ x → F x hx y = 0) := by
  classical
  refine ⟨fun x hx => Classical.choose (exists_admissible_delta_finset (s := s) (x := x) hx), ?_⟩
  constructor
  · intro x hx
    exact (Classical.choose_spec (exists_admissible_delta_finset (s := s) (x := x) hx)).1
  · intro x hx y hy hxy
    exact (Classical.choose_spec (exists_admissible_delta_finset (s := s) (x := x) hx)).2 y hy hxy

/-- Any function on a finite set of real points is a finite linear combination of
admissible Kronecker-delta functions. -/
theorem exists_admissible_eval_sum {s : Finset ℝ} (a : ∀ x ∈ s, ℂ) :
    ∃ f : ZetaAdmissibleFunction, ∀ x hx, f x = a x hx := by
  classical
  rcases exists_admissible_delta_family (s := s) with ⟨F, hF1, hF0⟩
  let f : ZetaAdmissibleFunction :=
    Finset.sum s.attach fun x => (a x.1 x.2) • F x.1 x.2
  refine ⟨f, ?_⟩
  intro x hx
  have hxatt : x ∈ s.attach := Finset.mem_attach.2 hx
  have hsum :
      f x = Finset.sum s.attach (fun y => a y.1 y.2 * F y.1 y.2 x) := by
    simp [f, ZetaAdmissibleFunction.smul_apply, mul_comm, mul_left_comm, mul_assoc]
  rw [hsum]
  have hsingle :
      Finset.sum s.attach (fun y => a y.1 y.2 * F y.1 y.2 x) =
        a x hx * F x hx x := by
    refine Finset.sum_eq_single x ?_ ?_ ?_
    · intro y hy hyx
      have hyx' : y.1 ≠ x := by
        intro h
        apply hyx
        exact Subtype.ext h
      simp [hF0 y.1 y.2 x hx hyx']
    · intro hxnot
      exact (hxnot hxatt).elim
    · simp [hF1 x hx]
  rw [hsingle, hF1]

/-- A finite interpolation witness can be chosen with compact support. -/
theorem exists_admissible_eval_sum_with_support {s : Finset ℝ} (a : ∀ x ∈ s, ℂ) :
    ∃ f : ZetaAdmissibleFunction, (∀ x hx, f x = a x hx) ∧ HasCompactSupport f := by
  classical
  rcases exists_admissible_delta_family_with_support (s := s) with ⟨F, hF1, hF0, hFc⟩
  let f : ZetaAdmissibleFunction :=
    Finset.sum s.attach fun x => (a x.1 x.2) • F x.1 x.2
  refine ⟨f, ?_, ?_⟩
  · intro x hx
    have hxatt : x ∈ s.attach := Finset.mem_attach.2 hx
    have hsum :
        f x = Finset.sum s.attach (fun y => a y.1 y.2 * F y.1 y.2 x) := by
      simp [f, ZetaAdmissibleFunction.smul_apply, mul_comm, mul_left_comm, mul_assoc]
    rw [hsum]
    have hsingle :
        Finset.sum s.attach (fun y => a y.1 y.2 * F y.1 y.2 x) =
          a x hx * F x hx x := by
      refine Finset.sum_eq_single x ?_ ?_ ?_
      · intro y hy hyx
        have hyx' : y.1 ≠ x := by
          intro h
          apply hyx
          exact Subtype.ext h
        simp [hF0 y.1 y.2 x hx hyx']
      · intro hxnot
        exact (hxnot hxatt).elim
      · simp [hF1 x hx]
    rw [hsingle, hF1]
  · simpa [f] using ZetaAdmissibleFunction.hasCompactSupport_sum s.attach
      fun x => (a x.1 x.2) • F x.1 x.2

/-- A finite interpolation witness can be accompanied by its spectral model in the same theorem. -/
theorem exists_admissible_eval_sum_with_spectralModel {s : Finset ℝ} (a : ∀ x ∈ s, ℂ) :
    ∃ f : ZetaAdmissibleFunction,
      (∀ x hx, f x = a x hx) ∧
      (spectralModel f = toZetaExplicitFormulaTransform f) := by
  rcases exists_admissible_eval_sum (s := s) a with ⟨f, hf⟩
  refine ⟨f, hf, by exact ZetaAdmissibleFunction.spectralModel_eq f⟩

/-- A finite interpolation witness can be accompanied by its transport surface. -/
theorem exists_admissible_eval_sum_with_transportSurface {s : Finset ℝ} (a : ∀ x ∈ s, ℂ) :
    ∃ f : ZetaAdmissibleFunction,
      (∀ x hx, f x = a x hx) ∧
      (packetTransportSurface f = (spectralModel f, separatingProbe f)) := by
  rcases exists_admissible_eval_sum_with_spectralModel (s := s) a with ⟨f, hf, _⟩
  refine ⟨f, hf, ?_⟩
  rw [ZetaAdmissibleFunction.packetTransportSurface_pair]

/-- A finite interpolation witness can be accompanied by its transport surface and spectral
model equality. -/
theorem exists_admissible_eval_sum_with_transportSurface_and_spectralModel {s : Finset ℝ}
    (a : ∀ x ∈ s, ℂ) :
    ∃ f : ZetaAdmissibleFunction,
      (∀ x hx, f x = a x hx) ∧
      (spectralModel f = toZetaExplicitFormulaTransform f) ∧
      (packetTransportSurface f = (spectralModel f, separatingProbe f)) := by
  rcases exists_admissible_eval_sum_with_transportSurface (s := s) a with ⟨f, hf, htp⟩
  refine ⟨f, hf, ZetaAdmissibleFunction.spectralModel_eq f, htp⟩

/-- A finite interpolation witness can be accompanied by its interpolation surface, spectral
model equality, and transport surface. -/
theorem exists_admissible_eval_sum_with_interpolationSurface_and_transportSurface {s : Finset ℝ}
    (a : ∀ x ∈ s, ℂ) :
    ∃ f : ZetaAdmissibleFunction,
      (∀ x hx, f x = a x hx) ∧
      (spectralModel f = toZetaExplicitFormulaTransform f) ∧
      (interpolationSurface f = (spectralModel f, separatingProbe f)) ∧
      (packetTransportSurface f = (spectralModel f, separatingProbe f)) := by
  rcases exists_admissible_eval_sum_with_transportSurface_and_spectralModel (s := s) a with
    ⟨f, hf, hs, htp⟩
  refine ⟨f, hf, hs, ?_, htp⟩
  rw [ZetaAdmissibleFunction.interpolationSurface_eq]

/-- A finite-type interpolation witness can be accompanied by the interpolation and transport
surfaces in the same theorem. -/
theorem exists_admissible_eval_fintype_with_surfaces {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (hx : Function.Injective x) (a : ι → ℂ) :
    ∃ f : ZetaAdmissibleFunction,
      (∀ i, f (x i) = a i) ∧
      (spectralModel f = toZetaExplicitFormulaTransform f) ∧
      (interpolationSurface f = (spectralModel f, separatingProbe f)) ∧
      (packetTransportSurface f = (spectralModel f, separatingProbe f)) := by
  rcases exists_admissible_eval_fintype (x := x) hx a with ⟨f, hf⟩
  refine ⟨f, hf, ZetaAdmissibleFunction.spectralModel_eq f, ?_, ?_⟩
  · rw [ZetaAdmissibleFunction.interpolationSurface_eq]
  · rw [ZetaAdmissibleFunction.packetTransportSurface_pair]

/-- A finite-type interpolant can be chosen with compact support, an explicit support bound,
and the canonical surfaces. -/
theorem exists_admissible_eval_fintype_with_support_subset_and_surfaces {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (hx : Function.Injective x) (a : ι → ℂ) :
    ∃ F : ∀ i, ZetaAdmissibleFunction,
      (∀ i, F i (x i) = (1 : ℂ)) ∧
      (∀ i j, j ≠ i → F i (x j) = 0) ∧
      (∀ i, HasCompactSupport (F i)) ∧
      ∃ f : ZetaAdmissibleFunction,
        (∀ i, f (x i) = a i) ∧
        HasCompactSupport f ∧
        Function.support f ⊆ Finset.univ.biUnion fun i => Function.support (F i) ∧
        (spectralModel f = toZetaExplicitFormulaTransform f) ∧
        (interpolationSurface f = (spectralModel f, separatingProbe f)) ∧
        (packetTransportSurface f = (spectralModel f, separatingProbe f)) := by
  rcases exists_admissible_eval_fintype_with_support_and_basis_support (x := x) hx a with
    ⟨F, hF1, hF0, hFc, f, hf, hcomp, hsupp⟩
  refine ⟨F, hF1, hF0, hFc, f, hf, hcomp, hsupp, ZetaAdmissibleFunction.spectralModel_eq f, ?_,
    ?_⟩
  · rw [ZetaAdmissibleFunction.interpolationSurface_eq]
  · rw [ZetaAdmissibleFunction.packetTransportSurface_pair]

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
