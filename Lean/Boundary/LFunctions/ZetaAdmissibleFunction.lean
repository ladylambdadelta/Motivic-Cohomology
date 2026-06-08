import Boundary.LFunctions.ZetaTestFunction
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Boundary admissible test functions

This file introduces the owner-level admissible carrier for the explicit-formula
route. The committed model is the Paley--Wiener style compactly supported smooth
class on the logarithmic line, bundled on top of the existing `ZetaTestFunction`
continuity layer.

The analytic transform and zero-separation theorems will consume this carrier.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped CompactlySupported

/-- The admissible test-function carrier for the explicit-formula route.

It packages a compactly supported continuous function on the logarithmic line
together with the smoothness data required by the Paley--Wiener model.
-/
structure ZetaAdmissibleFunction where
  toZetaTestFunction : ℝ →C_c ℂ
  smooth : ContDiff ℝ ⊤ (fun x => toZetaTestFunction x)

namespace ZetaAdmissibleFunction

instance : CoeFun ZetaAdmissibleFunction (fun _ => ℝ → ℂ) :=
  ⟨fun f => f.toZetaTestFunction⟩

@[ext]
theorem ext {f g : ZetaAdmissibleFunction} (h : ∀ x, f x = g x) : f = g := by
  cases f with
  | mk tf sf =>
    cases g with
    | mk tg sg =>
      have h' : tf = tg := by
        ext x
        exact h x
      cases h'
      rfl

/-- Forget the admissible structure and retain the underlying test function. -/
def toZetaTestFunction' (f : ZetaAdmissibleFunction) : ZetaTestFunction :=
  ⟨f.toZetaTestFunction, f.toZetaTestFunction.continuous⟩

theorem toZetaTestFunction'_apply (f : ZetaAdmissibleFunction) (x : ℝ) :
    f.toZetaTestFunction' x = f x := by
  rfl

/-- The underlying compactly supported continuous map. -/
theorem hasCompactSupport (f : ZetaAdmissibleFunction) :
    HasCompactSupport f := by
  exact f.toZetaTestFunction.hasCompactSupport

/-- The admissible carrier is smooth on the logarithmic line. -/
theorem contDiff (f : ZetaAdmissibleFunction) : ContDiff ℝ ⊤ f := by
  exact f.smooth

/-- The sum of two admissible functions has compact support. -/
theorem hasCompactSupport_add (f g : ZetaAdmissibleFunction) :
    HasCompactSupport (f + g) := by
  simpa [ZetaAdmissibleFunction.add] using
    f.toZetaTestFunction.hasCompactSupport.add g.toZetaTestFunction.hasCompactSupport

/-- Scalar multiples of admissible functions have compact support. -/
theorem hasCompactSupport_smul (a : ℂ) (f : ZetaAdmissibleFunction) :
    HasCompactSupport (a • f) := by
  simpa [ZetaAdmissibleFunction.smul] using
    f.toZetaTestFunction.hasCompactSupport.const_smul a

/-- A finite sum of admissible functions has compact support. -/
theorem hasCompactSupport_sum {α : Type*} (s : Finset α) (f : α → ZetaAdmissibleFunction) :
    HasCompactSupport (∑ a in s, f a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      simpa [Finset.sum_insert ha, ZetaAdmissibleFunction.add] using
        hasCompactSupport_add (f a) (∑ b in s, f b)

/-- The support of a finite sum is contained in the union of the supports. -/
theorem support_sum_subset {α : Type*} (s : Finset α) (f : α → ZetaAdmissibleFunction) :
    Function.support (∑ a in s, f a) ⊆ s.biUnion fun a => Function.support (f a) := by
  intro x hx
  simp only [Function.mem_support, ne_eq] at hx ⊢
  have hne : ∃ a ∈ s, f a x ≠ 0 := by
    simpa [Finset.sum_apply] using
      (Finset.exists_ne_zero_of_sum_ne_zero (s := s) (f := fun a => f a x) hx)
  rcases hne with ⟨a, ha, hax⟩
  exact Finset.mem_biUnion.2 ⟨a, ha, by simpa [Function.mem_support, ne_eq] using hax⟩

/-- The support of a sum is contained in the union of the summands' supports. -/
theorem support_add_subset (f g : ZetaAdmissibleFunction) :
    Function.support (f + g) ⊆ Function.support f ∪ Function.support g := by
  intro x hx
  simp only [Function.mem_support, ne_eq] at hx ⊢
  by_cases hfx : f x = 0
  · right
    intro hg
    exact hx (by simp [hfx, hg])
  · left
    exact hfx

/-- If two admissible functions have disjoint supports, the support of their sum is the union of
their supports. -/
theorem support_add_eq (f g : ZetaAdmissibleFunction)
    (hfg : Disjoint (Function.support f) (Function.support g)) :
    Function.support (f + g) = Function.support f ∪ Function.support g := by
  ext x
  constructor
  · exact support_add_subset f g
  · intro hx
    rcases Set.mem_union.1 hx with hx | hx
    · have hgx : g x = 0 := by
        by_contra hgx
        have : x ∈ Function.support g := by simpa [Function.mem_support] using hgx
        exact hfg.not_mem_left this hx
      simp [Function.mem_support, hx, hgx]
    · have hfx : f x = 0 := by
        by_contra hfx
        have : x ∈ Function.support f := by simpa [Function.mem_support] using hfx
        exact hfg.not_mem_right hx this
      simp [Function.mem_support, hfx, hx]

/-- Scalar multiplication does not enlarge support. -/
theorem support_smul_subset (a : ℂ) (f : ZetaAdmissibleFunction) :
    Function.support (a • f) ⊆ Function.support f := by
  intro x hx
  simp only [Function.mem_support, Pi.smul_apply, ne_eq] at hx ⊢
  by_cases ha : a = 0
  · have hfalse : False := by
      exact hx (by simp [ha])
    exact False.elim hfalse
  · exact by
      intro hfx
      exact hx (by simp [ha, hfx])

/-- Nonzero scalar multiplication preserves support exactly. -/
theorem support_smul (a : ℂ) (ha : a ≠ 0) (f : ZetaAdmissibleFunction) :
    Function.support (a • f) = Function.support f := by
  ext x
  simp only [Function.mem_support, Pi.smul_apply, ne_eq]
  constructor
  · intro hx
    intro hfx
    exact hx (by simp [hfx])
  · intro hx
    have hax : a * f x ≠ 0 := by simpa [ha] using hx
    exact hax

/-- Translation does not change support after nonzero scalar multiplication. -/
theorem support_translate_smul (c : ℝ) (a : ℂ) (ha : a ≠ 0) (f : ZetaAdmissibleFunction) :
    Function.support (translate c (a • f)) = Function.support (translate c f) := by
  rw [translate_smul, support_smul a ha]

/-- The support of a translated nonzero scalar multiple is the translated support of the
original function. -/
theorem support_translate_smul_eq (c : ℝ) (a : ℂ) (ha : a ≠ 0) (f : ZetaAdmissibleFunction) :
    Function.support (translate c (a • f)) =
      (fun x => x - c) ⁻¹' Function.support f := by
  rw [support_translate_smul c a ha, support_translate c f]

/-- Reflection does not change support after nonzero scalar multiplication. -/
theorem support_reflect_smul (a : ℂ) (ha : a ≠ 0) (f : ZetaAdmissibleFunction) :
    Function.support (reflect (a • f)) = Function.support (reflect f) := by
  rw [reflect_smul, support_smul a ha]

/-- The support of a reflected nonzero scalar multiple is the reflected support of the
original function. -/
theorem support_reflect_smul_eq (a : ℂ) (ha : a ≠ 0) (f : ZetaAdmissibleFunction) :
    Function.support (reflect (a • f)) = (fun x => -x) ⁻¹' Function.support f := by
  rw [support_reflect_smul a ha, support_reflect f]

/-- Scaling does not change support after nonzero scalar multiplication. -/
theorem support_scale_smul (t : ℝ) (a : ℂ) (ha : a ≠ 0) (f : ZetaAdmissibleFunction) :
    Function.support (scale t (a • f)) = Function.support (scale t f) := by
  rw [scale_smul, support_smul a ha]

/-- The support of a scaled nonzero scalar multiple is the scaled support of the original
function. -/
theorem support_scale_smul_eq (t : ℝ) (a : ℂ) (ha : a ≠ 0) (f : ZetaAdmissibleFunction) :
    Function.support (scale t (a • f)) = (fun x => t * x) ⁻¹' Function.support f := by
  rw [support_scale_smul t a ha, support_scale t f]

/-- The support of a finite linear combination is contained in the union of the supports. -/
theorem support_sum_smul_subset {α : Type*} (s : Finset α) (c : α → ℂ)
    (f : α → ZetaAdmissibleFunction) :
    Function.support (∑ a in s, c a • f a) ⊆ s.biUnion fun a => Function.support (f a) := by
  refine (support_sum_subset s fun a => c a • f a).trans ?_
  intro x hx
  rcases Finset.mem_biUnion.mp hx with ⟨a, ha, hax⟩
  exact Finset.mem_biUnion.2 ⟨a, ha, support_smul_subset (c a) (f a) hax⟩

/-- If the summands have pairwise disjoint supports, the support of a finite linear combination is
the union of the summands' supports. -/
theorem support_sum_smul_eq {α : Type*} (s : Finset α) (c : α → ℂ)
    (f : α → ZetaAdmissibleFunction)
    (hdisjoint : Pairwise (fun i j => Disjoint (Function.support (f i)) (Function.support (f j)))) :
    Function.support (∑ a in s, c a • f a) = s.biUnion fun a => Function.support (f a) := by
  classical
  refine le_antisymm (support_sum_smul_subset (s := s) (c := c) (f := f)) ?_
  intro x hx
  rcases Finset.mem_biUnion.mp hx with ⟨a, ha, hax⟩
  by_contra hx'
  have hzero : ∀ b ∈ s, b ≠ a → f b x = 0 := by
    intro b hb hba
    by_contra hfb
    have hxB : x ∈ Function.support (f b) := by simpa [Function.mem_support] using hfb
    have hdisj := hdisjoint (by simpa [ha, hb] using hba) 
    exact hdisj.not_mem_left hxB hax
  have hsumzero : (∑ b in s, c b • f b) x = 0 := by
    simp [Finset.sum_apply, hax, hzero]
  exact hx' (by simpa [Function.mem_support] using hsumzero)

/-- If the summands have pairwise disjoint supports, the support of their finite sum is the union
of the summand supports. -/
theorem support_sum_eq {α : Type*} (s : Finset α) (f : α → ZetaAdmissibleFunction)
    (hdisjoint : Pairwise (fun i j => Disjoint (Function.support (f i)) (Function.support (f j)))) :
    Function.support (∑ a in s, f a) = s.biUnion fun a => Function.support (f a) := by
  classical
  refine le_antisymm (support_sum_subset s f) ?_
  intro x hx
  rcases Finset.mem_biUnion.mp hx with ⟨a, ha, hax⟩
  by_contra hx'
  have hzero : ∀ b ∈ s, b ≠ a → f b x = 0 := by
    intro b hb hba
    by_contra hfb
    have hxB : x ∈ Function.support (f b) := by simpa [Function.mem_support] using hfb
    have hdisj := hdisjoint (by simpa [ha, hb] using hba)
    exact hdisj.not_mem_left hxB hax
  have hsumzero : (∑ b in s, f b) x = 0 := by
    simp [Finset.sum_apply, hax, hzero]
  exact hx' (by simpa [Function.mem_support] using hsumzero)

/-- If the summands have pairwise disjoint supports, the support of a finite linear combination is
the union of the supports of the scaled summands. -/
theorem support_sum_smul_eq' {α : Type*} (s : Finset α) (c : α → ℂ) (f : α → ZetaAdmissibleFunction)
    (hdisjoint : Pairwise (fun i j => Disjoint (Function.support (f i)) (Function.support (f j)))) :
    Function.support (∑ a in s, c a • f a) = s.biUnion fun a => Function.support (f a) := by
  classical
  refine le_antisymm (support_sum_smul_subset (s := s) (c := c) (f := f)) ?_
  intro x hx
  rcases Finset.mem_biUnion.mp hx with ⟨a, ha, hax⟩
  by_contra hx'
  have hzero : ∀ b ∈ s, b ≠ a → f b x = 0 := by
    intro b hb hba
    by_contra hfb
    have hxB : x ∈ Function.support (f b) := by simpa [Function.mem_support] using hfb
    have hdisj := hdisjoint (by simpa [ha, hb] using hba)
    exact hdisj.not_mem_left hxB hax
  have hsumzero : (∑ b in s, c b • f b) x = 0 := by
    simp [Finset.sum_apply, hax, hzero]
  exact hx' (by simpa [Function.mem_support] using hsumzero)

/-- If the summands have pairwise disjoint supports, the finite sum is pairwise disjoint from any
admissible function whose support is disjoint from each summand. -/
theorem disjoint_support_sum {α : Type*} (s : Finset α) (f : α → ZetaAdmissibleFunction)
    (g : ZetaAdmissibleFunction)
    (hdisjoint : ∀ a ∈ s, Disjoint (Function.support (f a)) (Function.support g)) :
    Disjoint (Function.support (∑ a in s, f a)) (Function.support g) := by
  intro x hx hgx
  have hsum : x ∈ s.biUnion fun a => Function.support (f a) := by
    exact support_sum_subset s f hx
  rcases Finset.mem_biUnion.mp hsum with ⟨a, ha, hax⟩
  exact (hdisjoint a ha).not_mem_left hax hgx

/-- If the summands have pairwise disjoint supports, the finite linear combination is pairwise
disjoint from any admissible function whose support is disjoint from each summand. -/
theorem disjoint_support_sum_smul {α : Type*} (s : Finset α) (c : α → ℂ)
    (f : α → ZetaAdmissibleFunction) (g : ZetaAdmissibleFunction)
    (hdisjoint : ∀ a ∈ s, Disjoint (Function.support (f a)) (Function.support g)) :
    Disjoint (Function.support (∑ a in s, c a • f a)) (Function.support g) := by
  intro x hx hgx
  have hsum : x ∈ s.biUnion fun a => Function.support (f a) := by
    exact support_sum_smul_subset (s := s) (c := c) (f := f) hx
  rcases Finset.mem_biUnion.mp hsum with ⟨a, ha, hax⟩
  exact (hdisjoint a ha).not_mem_left hax hgx

/-- If every summand in one finite family is disjoint from every summand in another finite family,
then the two finite sums are disjoint. -/
theorem disjoint_support_sum_sum {α β : Type*} (s : Finset α) (t : Finset β)
    (f : α → ZetaAdmissibleFunction) (g : β → ZetaAdmissibleFunction)
    (hdisjoint : ∀ a ∈ s, ∀ b ∈ t, Disjoint (Function.support (f a)) (Function.support (g b))) :
    Disjoint (Function.support (∑ a in s, f a)) (Function.support (∑ b in t, g b)) := by
  intro x hx hy
  have hs : x ∈ s.biUnion fun a => Function.support (f a) := by
    exact support_sum_subset (s := s) (f := f) hx
  have ht : x ∈ t.biUnion fun b => Function.support (g b) := by
    exact support_sum_subset (s := t) (f := g) hy
  rcases Finset.mem_biUnion.mp hs with ⟨a, ha, hax⟩
  rcases Finset.mem_biUnion.mp ht with ⟨b, hb, hbx⟩
  exact (hdisjoint a ha b hb).not_mem_left hax hbx

/-- If every summand in one finite family is disjoint from every summand in another finite family,
then the support of the sum of the two finite sums is the union of their supports. -/
theorem support_add_sum_sum {α β : Type*} (s : Finset α) (t : Finset β)
    (f : α → ZetaAdmissibleFunction) (g : β → ZetaAdmissibleFunction)
    (hdisjoint : ∀ a ∈ s, ∀ b ∈ t,
      Disjoint (Function.support (f a)) (Function.support (g b))) :
    Function.support ((∑ a in s, f a) + (∑ b in t, g b)) =
      Function.support (∑ a in s, f a) ∪ Function.support (∑ b in t, g b) := by
  have hsum : Disjoint (Function.support (∑ a in s, f a))
      (Function.support (∑ b in t, g b)) :=
    disjoint_support_sum_sum (s := s) (t := t) (f := f) (g := g) hdisjoint
  simpa [support_add_eq hsum]

/-- If every scaled summand in one finite family is disjoint from every scaled summand in another
finite family, then the support of the sum of the two finite linear combinations is the union of
the two support sets. -/
theorem support_add_sum_smul_sum_smul {α β : Type*} (s : Finset α) (t : Finset β)
    (c : α → ℂ) (d : β → ℂ) (f : α → ZetaAdmissibleFunction) (g : β → ZetaAdmissibleFunction)
    (hdisjoint : ∀ a ∈ s, ∀ b ∈ t,
      Disjoint (Function.support (c a • f a)) (Function.support (d b • g b))) :
    Function.support ((∑ a in s, c a • f a) + (∑ b in t, d b • g b)) =
      Function.support (∑ a in s, c a • f a) ∪ Function.support (∑ b in t, d b • g b) := by
  have hsum : Disjoint (Function.support (∑ a in s, c a • f a))
      (Function.support (∑ b in t, d b • g b)) :=
    disjoint_support_sum_smul_sum_smul (s := s) (t := t) (c := c) (d := d) (f := f) (g := g)
      hdisjoint
  simpa [support_add_eq hsum]

/-- If two finite families are internally pairwise disjoint and every summand in one family is
disjoint from every summand in the other family, then the support of the sum of the two finite
sums is the union of the supports of all summands. -/
theorem support_add_sum_sum_of_pairwise {α β : Type*} (s : Finset α) (t : Finset β)
    (f : α → ZetaAdmissibleFunction) (g : β → ZetaAdmissibleFunction)
    (hpair_f : Pairwise (fun i j => Disjoint (Function.support (f i)) (Function.support (f j))))
    (hpair_g : Pairwise (fun i j => Disjoint (Function.support (g i)) (Function.support (g j))))
    (hcross : ∀ a ∈ s, ∀ b ∈ t,
      Disjoint (Function.support (f a)) (Function.support (g b))) :
    Function.support ((∑ a in s, f a) + (∑ b in t, g b)) =
      (Function.support (∑ a in s, f a) ∪ Function.support (∑ b in t, g b)) := by
  have hsum : Disjoint (Function.support (∑ a in s, f a))
      (Function.support (∑ b in t, g b)) :=
    disjoint_support_sum_sum (s := s) (t := t) (f := f) (g := g) hcross
  simpa [support_add_eq hsum]

/-- If two finite families are internally pairwise disjoint and every scaled summand in one
family is disjoint from every scaled summand in the other family, then the support of the sum of
the two finite linear combinations is the union of the supports of all summands. -/
theorem support_add_sum_smul_sum_smul_of_pairwise {α β : Type*} (s : Finset α) (t : Finset β)
    (c : α → ℂ) (d : β → ℂ) (f : α → ZetaAdmissibleFunction) (g : β → ZetaAdmissibleFunction)
    (hpair_f : Pairwise (fun i j => Disjoint (Function.support (c i • f i))
      (Function.support (c j • f j))))
    (hpair_g : Pairwise (fun i j => Disjoint (Function.support (d i • g i))
      (Function.support (d j • g j))))
    (hcross : ∀ a ∈ s, ∀ b ∈ t,
      Disjoint (Function.support (c a • f a)) (Function.support (d b • g b))) :
    Function.support ((∑ a in s, c a • f a) + (∑ b in t, d b • g b)) =
      Function.support (∑ a in s, c a • f a) ∪ Function.support (∑ b in t, d b • g b) := by
  have hsum : Disjoint (Function.support (∑ a in s, c a • f a))
      (Function.support (∑ b in t, d b • g b)) :=
    disjoint_support_sum_smul_sum_smul (s := s) (t := t) (c := c) (d := d) (f := f) (g := g)
      hcross
  simpa [support_add_eq hsum]

/-- If two finite families are internally pairwise disjoint and every scaled summand in one
family is disjoint from every scaled summand in the other family, then the support of the sum of
the two finite linear combinations is exactly the union of the supports of all summands. -/
theorem support_add_sum_smul_sum_smul_of_pairwise_eq {α β : Type*} (s : Finset α) (t : Finset β)
    (c : α → ℂ) (d : β → ℂ) (f : α → ZetaAdmissibleFunction) (g : β → ZetaAdmissibleFunction)
    (hpair_f : Pairwise (fun i j => Disjoint (Function.support (c i • f i))
      (Function.support (c j • f j))))
    (hpair_g : Pairwise (fun i j => Disjoint (Function.support (d i • g i))
      (Function.support (d j • g j))))
    (hcross : ∀ a ∈ s, ∀ b ∈ t,
      Disjoint (Function.support (c a • f a)) (Function.support (d b • g b))) :
    Function.support ((∑ a in s, c a • f a) + (∑ b in t, d b • g b)) =
      (s.biUnion fun a => Function.support (c a • f a)) ∪
        (t.biUnion fun b => Function.support (d b • g b)) := by
  rw [support_add_sum_smul_sum_smul_of_pairwise (s := s) (t := t) (c := c) (d := d) (f := f)
    (g := g) hpair_f hpair_g hcross,
    support_sum_smul_eq' (s := s) (c := c) (f := f) hpair_f,
    support_sum_smul_eq' (s := t) (c := d) (f := g) hpair_g]

/-- If two finite families are internally pairwise disjoint and every summand in one family is
disjoint from every summand in the other family, then the support of the sum of the two finite
sums is exactly the union of the supports of all summands. -/
theorem support_add_sum_sum_of_pairwise_eq {α β : Type*} (s : Finset α) (t : Finset β)
    (f : α → ZetaAdmissibleFunction) (g : β → ZetaAdmissibleFunction)
    (hpair_f : Pairwise (fun i j => Disjoint (Function.support (f i))
      (Function.support (f j))))
    (hpair_g : Pairwise (fun i j => Disjoint (Function.support (g i))
      (Function.support (g j))))
    (hcross : ∀ a ∈ s, ∀ b ∈ t, Disjoint (Function.support (f a)) (Function.support (g b))) :
    Function.support ((∑ a in s, f a) + (∑ b in t, g b)) =
      (s.biUnion fun a => Function.support (f a)) ∪
        (t.biUnion fun b => Function.support (g b)) := by
  rw [support_add_sum_sum_of_pairwise (s := s) (t := t) (f := f) (g := g) hpair_f hpair_g hcross,
    support_sum_eq (s := s) (f := f) hpair_f,
    support_sum_eq (s := t) (f := g) hpair_g]

/-- If a finite family has pairwise disjoint supports, then the support of the sum of two disjoint
subfamilies is the union of the supports of the summands in those subfamilies. -/
theorem support_sum_add_sum_of_pairwise_eq {α : Type*} (s t : Finset α)
    (f : α → ZetaAdmissibleFunction)
    (hpair : Pairwise (fun i j => Disjoint (Function.support (f i)) (Function.support (f j))))
    (hst : Disjoint s t) :
    Function.support ((∑ a in s, f a) + (∑ b in t, f b)) =
      (s.biUnion fun a => Function.support (f a)) ∪
        (t.biUnion fun b => Function.support (f b)) := by
  rw [support_add_eq (disjoint_support_sum_sum_of_pairwise (s := s) (t := t) (f := f)
      hpair hst), support_sum_eq (s := s) (f := f) hpair,
    support_sum_eq (s := t) (f := f) hpair]

/-- If the summands in a finite sum are each disjoint from a fixed admissible function, then the
support of their sum with that function is the union of the support sets. -/
theorem support_sum_add_eq {α : Type*} (s : Finset α) (f : α → ZetaAdmissibleFunction)
    (g : ZetaAdmissibleFunction)
    (hdisjoint : ∀ a ∈ s, Disjoint (Function.support (f a)) (Function.support g)) :
    Function.support ((∑ a in s, f a) + g) =
      s.biUnion fun a => Function.support (f a) ∪ Function.support g := by
  have hsum : Disjoint (Function.support (∑ a in s, f a)) (Function.support g) :=
    disjoint_support_sum (s := s) (f := f) (g := g) hdisjoint
  rw [support_add_eq hsum, support_sum_eq (s := s) (f := f)]
  simp [biUnion_union_right]

/-- If a fixed admissible function is disjoint from each summand in a finite sum, then the
support of that function added to the sum is the union of the support sets. -/
theorem support_add_sum_eq {α : Type*} (g : ZetaAdmissibleFunction) (s : Finset α)
    (f : α → ZetaAdmissibleFunction)
    (hdisjoint : ∀ a ∈ s, Disjoint (Function.support g) (Function.support (f a))) :
    Function.support (g + ∑ a in s, f a) =
      Function.support g ∪ s.biUnion fun a => Function.support (f a) := by
  have hsum : Disjoint (Function.support g) (Function.support (∑ a in s, f a)) :=
    (disjoint_support_sum (s := s) (f := f) (g := g) (by
      intro a ha
      simpa [Disjoint.comm] using hdisjoint a ha)).symm
  rw [support_add_eq hsum, support_sum_eq (s := s) (f := f)]
  simp [union_comm, union_left_comm, union_assoc]

/-- If a fixed admissible function is disjoint from each scaled summand in a finite linear
combination, then the support of their sum is the union of the support sets. -/
theorem support_add_sum_smul_eq {α : Type*} (g : ZetaAdmissibleFunction) (s : Finset α)
    (c : α → ℂ) (f : α → ZetaAdmissibleFunction)
    (hdisjoint : ∀ a ∈ s, Disjoint (Function.support g) (Function.support (c a • f a))) :
    Function.support (g + ∑ a in s, c a • f a) =
      Function.support g ∪ s.biUnion fun a => Function.support (c a • f a) := by
  have hsum : Disjoint (Function.support g) (Function.support (∑ a in s, c a • f a)) :=
    (disjoint_support_sum_smul (s := s) (c := c) (f := f) (g := g) (by
      intro a ha
      simpa [Disjoint.comm] using hdisjoint a ha)).symm
  rw [support_add_eq hsum, support_sum_smul_eq' (s := s) (c := c) (f := f)]
  simp [union_comm, union_left_comm, union_assoc]

/-- If each scaled summand in a finite linear combination is disjoint from a fixed admissible
function, then the support of the sum is the union of the support sets. -/
theorem support_sum_smul_add_eq {α : Type*} (s : Finset α) (c : α → ℂ)
    (f : α → ZetaAdmissibleFunction) (g : ZetaAdmissibleFunction)
    (hdisjoint : ∀ a ∈ s, Disjoint (Function.support (c a • f a)) (Function.support g)) :
    Function.support ((∑ a in s, c a • f a) + g) =
      s.biUnion fun a => Function.support (c a • f a) ∪ Function.support g := by
  rw [add_comm, support_add_sum_smul_eq (g := g) (s := s) (c := c) (f := f)]

/-- If a finite sum and a finite linear combination are pairwise disjoint term-by-term, then the
support of their sum is the union of the supports of the two families. -/
theorem support_sum_add_sum_smul_eq {α β : Type*} (s : Finset α) (t : Finset β)
    (f : α → ZetaAdmissibleFunction) (c : β → ℂ) (g : β → ZetaAdmissibleFunction)
    (hdisjoint : ∀ a ∈ s, ∀ b ∈ t,
      Disjoint (Function.support (f a)) (Function.support (c b • g b))) :
    Function.support ((∑ a in s, f a) + (∑ b in t, c b • g b)) =
      (s.biUnion fun a => Function.support (f a)) ∪
        (t.biUnion fun b => Function.support (c b • g b)) := by
  have hsum : Disjoint (Function.support (∑ a in s, f a))
      (Function.support (∑ b in t, c b • g b)) :=
    disjoint_support_sum_smul_sum (s := t) (t := s) (c := c) (f := g) (g := f) (by
      intro b hb a ha
      simpa [Disjoint.comm] using hdisjoint a ha b hb)
  rw [support_add_eq hsum, support_sum_eq (s := s) (f := f),
    support_sum_smul_eq' (s := t) (c := c) (f := g)]
  simp [union_comm, union_left_comm, union_assoc]

/-- If a finite linear combination and a finite sum are pairwise disjoint term-by-term, then the
support of their sum is the union of the supports of the two families. -/
theorem support_sum_smul_add_sum_eq {α β : Type*} (s : Finset α) (t : Finset β)
    (c : α → ℂ) (f : α → ZetaAdmissibleFunction) (g : β → ZetaAdmissibleFunction)
    (hdisjoint : ∀ a ∈ s, ∀ b ∈ t,
      Disjoint (Function.support (c a • f a)) (Function.support (g b))) :
    Function.support ((∑ a in s, c a • f a) + (∑ b in t, g b)) =
      (s.biUnion fun a => Function.support (c a • f a)) ∪
        (t.biUnion fun b => Function.support (g b)) := by
  rw [add_comm, support_sum_add_sum_smul_eq (s := t) (t := s) (f := g) (c := c) (g := f)]
  · simp [union_comm, union_left_comm, union_assoc]
  · intro b hb a ha
    simpa [Disjoint.comm] using hdisjoint a ha b hb

/-- If a finite sum and a finite linear combination are internally pairwise disjoint and
term-by-term disjoint from one another, then the support of their sum is the union of the supports
of all summands. -/
theorem support_sum_add_sum_smul_of_pairwise_eq {α β : Type*} (s : Finset α) (t : Finset β)
    (f : α → ZetaAdmissibleFunction) (c : β → ℂ) (g : β → ZetaAdmissibleFunction)
    (hpair_f : Pairwise (fun i j => Disjoint (Function.support (f i))
      (Function.support (f j))))
    (hpair_g : Pairwise (fun i j => Disjoint (Function.support (c i • g i))
      (Function.support (c j • g j))))
    (hcross : ∀ a ∈ s, ∀ b ∈ t,
      Disjoint (Function.support (f a)) (Function.support (c b • g b))) :
    Function.support ((∑ a in s, f a) + (∑ b in t, c b • g b)) =
      (s.biUnion fun a => Function.support (f a)) ∪
        (t.biUnion fun b => Function.support (c b • g b)) := by
  rw [support_sum_add_sum_smul_eq (s := s) (t := t) (f := f) (c := c) (g := g) hcross,
    support_sum_eq (s := s) (f := f) hpair_f,
    support_sum_smul_eq' (s := t) (c := c) (f := g) hpair_g]

/-- If three admissible functions are pairwise disjoint, then the support of their sum is the
union of their supports. -/
theorem support_add_add_add_eq {f g h : ZetaAdmissibleFunction}
    (hfg : Disjoint (Function.support f) (Function.support g))
    (hfh : Disjoint (Function.support f) (Function.support h))
    (hgh : Disjoint (Function.support g) (Function.support h)) :
    Function.support (f + g + h) =
      Function.support f ∪ Function.support g ∪ Function.support h := by
  rw [add_assoc, support_add_eq hfg, support_add_eq]
  · simp [union_comm, union_left_comm, union_assoc]
  · exact hfh

/-- If four admissible functions are pairwise disjoint, then the support of their sum is the
union of their supports. -/
theorem support_add_add_add_add_eq {f g h k : ZetaAdmissibleFunction}
    (hfg : Disjoint (Function.support f) (Function.support g))
    (hfh : Disjoint (Function.support f) (Function.support h))
    (hfk : Disjoint (Function.support f) (Function.support k))
    (hgh : Disjoint (Function.support g) (Function.support h))
    (hgk : Disjoint (Function.support g) (Function.support k))
    (hhk : Disjoint (Function.support h) (Function.support k)) :
    Function.support (f + g + h + k) =
      Function.support f ∪ Function.support g ∪ Function.support h ∪ Function.support k := by
  have hsum : Disjoint (Function.support (f + g + h)) (Function.support k) := by
    intro x hx hkx
    have hxyz : x ∈ Function.support f ∪ Function.support g ∪ Function.support h := by
      simpa [support_add_add_add_eq (f := f) (g := g) (h := h) hfg hfh hgh] using hx
    rcases hxyz with hfx | hgx | hhx
    · exact hfk.not_mem_left hfx hkx
    · exact hgk.not_mem_left hgx hkx
    · exact hhk.not_mem_left hhx hkx
  rw [add_assoc, support_add_eq hsum, support_add_add_add_eq (f := f) (g := g) (h := h) hfg hfh hgh]
  simp [union_comm, union_left_comm, union_assoc]

/-- If five admissible functions are pairwise disjoint, then the support of their sum is the
union of their supports. -/
theorem support_add_add_add_add_add_eq {f g h k l : ZetaAdmissibleFunction}
    (hfg : Disjoint (Function.support f) (Function.support g))
    (hfh : Disjoint (Function.support f) (Function.support h))
    (hfk : Disjoint (Function.support f) (Function.support k))
    (hfl : Disjoint (Function.support f) (Function.support l))
    (hgh : Disjoint (Function.support g) (Function.support h))
    (hgk : Disjoint (Function.support g) (Function.support k))
    (hgl : Disjoint (Function.support g) (Function.support l))
    (hhk : Disjoint (Function.support h) (Function.support k))
    (hhl : Disjoint (Function.support h) (Function.support l))
    (hkl : Disjoint (Function.support k) (Function.support l)) :
    Function.support (f + g + h + k + l) =
      Function.support f ∪ Function.support g ∪ Function.support h ∪ Function.support k ∪
        Function.support l := by
  have hsum : Disjoint (Function.support (f + g + h + k)) (Function.support l) := by
    intro x hx hlx
    have hxyz : x ∈ Function.support f ∪ Function.support g ∪ Function.support h ∪
        Function.support k := by
      simpa [support_add_add_add_add_eq (f := f) (g := g) (h := h) (k := k) hfg hfh hfk hgh
        hgk hhk] using hx
    rcases hxyz with hfx | hgx | hhx | hkx
    · exact hfl.not_mem_left hfx hlx
    · exact hgl.not_mem_left hgx hlx
    · exact hhl.not_mem_left hhx hlx
    · exact hkl.not_mem_left hkx hlx
  rw [add_assoc, support_add_eq hsum,
    support_add_add_add_add_eq (f := f) (g := g) (h := h) (k := k) hfg hfh hfk hgh hgk hhk]
  simp [union_comm, union_left_comm, union_assoc]

/-- If six admissible functions are pairwise disjoint, then the support of their sum is the
union of their supports. -/
theorem support_add_add_add_add_add_add_eq {f g h k l m : ZetaAdmissibleFunction}
    (hfg : Disjoint (Function.support f) (Function.support g))
    (hfh : Disjoint (Function.support f) (Function.support h))
    (hfk : Disjoint (Function.support f) (Function.support k))
    (hfl : Disjoint (Function.support f) (Function.support l))
    (hfm : Disjoint (Function.support f) (Function.support m))
    (hgh : Disjoint (Function.support g) (Function.support h))
    (hgk : Disjoint (Function.support g) (Function.support k))
    (hgl : Disjoint (Function.support g) (Function.support l))
    (hgm : Disjoint (Function.support g) (Function.support m))
    (hhk : Disjoint (Function.support h) (Function.support k))
    (hhl : Disjoint (Function.support h) (Function.support l))
    (hhm : Disjoint (Function.support h) (Function.support m))
    (hkl : Disjoint (Function.support k) (Function.support l))
    (hkm : Disjoint (Function.support k) (Function.support m))
    (hlm : Disjoint (Function.support l) (Function.support m)) :
    Function.support (f + g + h + k + l + m) =
      Function.support f ∪ Function.support g ∪ Function.support h ∪ Function.support k ∪
        Function.support l ∪ Function.support m := by
  have hsum : Disjoint (Function.support (f + g + h + k + l)) (Function.support m) := by
    intro x hx hmx
    have hxyz : x ∈ Function.support f ∪ Function.support g ∪ Function.support h ∪
        Function.support k ∪ Function.support l := by
      simpa [support_add_add_add_add_add_eq (f := f) (g := g) (h := h) (k := k) (l := l)
        hfg hfh hfk hfl hgh hgk hgl hhk hhl hkl] using hx
    rcases hxyz with hfx | hgx | hhx | hkx | hlx
    · exact hfm.not_mem_left hfx hmx
    · exact hgm.not_mem_left hgx hmx
    · exact hhm.not_mem_left hhx hmx
    · exact hkm.not_mem_left hkx hmx
    · exact hlm.not_mem_left hlx hmx
  rw [add_assoc, support_add_eq hsum,
    support_add_add_add_add_add_eq (f := f) (g := g) (h := h) (k := k) (l := l) hfg hfh hfk hfl
      hgh hgk hgl hhk hhl hkl]
  simp [union_comm, union_left_comm, union_assoc]

/-- If seven admissible functions are pairwise disjoint, then the support of their sum is the
union of their supports. -/
theorem support_add_add_add_add_add_add_add_eq {f g h k l m n : ZetaAdmissibleFunction}
    (hfg : Disjoint (Function.support f) (Function.support g))
    (hfh : Disjoint (Function.support f) (Function.support h))
    (hfk : Disjoint (Function.support f) (Function.support k))
    (hfl : Disjoint (Function.support f) (Function.support l))
    (hfm : Disjoint (Function.support f) (Function.support m))
    (hfn : Disjoint (Function.support f) (Function.support n))
    (hgh : Disjoint (Function.support g) (Function.support h))
    (hgk : Disjoint (Function.support g) (Function.support k))
    (hgl : Disjoint (Function.support g) (Function.support l))
    (hgm : Disjoint (Function.support g) (Function.support m))
    (hgn : Disjoint (Function.support g) (Function.support n))
    (hhk : Disjoint (Function.support h) (Function.support k))
    (hhl : Disjoint (Function.support h) (Function.support l))
    (hhm : Disjoint (Function.support h) (Function.support m))
    (hhn : Disjoint (Function.support h) (Function.support n))
    (hkl : Disjoint (Function.support k) (Function.support l))
    (hkm : Disjoint (Function.support k) (Function.support m))
    (hkn : Disjoint (Function.support k) (Function.support n))
    (hlm : Disjoint (Function.support l) (Function.support m))
    (hln : Disjoint (Function.support l) (Function.support n))
    (hmn : Disjoint (Function.support m) (Function.support n)) :
    Function.support (f + g + h + k + l + m + n) =
      Function.support f ∪ Function.support g ∪ Function.support h ∪ Function.support k ∪
        Function.support l ∪ Function.support m ∪ Function.support n := by
  have hsum : Disjoint (Function.support (f + g + h + k + l + m)) (Function.support n) := by
    intro x hx hnx
    have hxyz : x ∈ Function.support f ∪ Function.support g ∪ Function.support h ∪
        Function.support k ∪ Function.support l ∪ Function.support m := by
      simpa [support_add_add_add_add_add_eq (f := f) (g := g) (h := h) (k := k) (l := l)
        hfg hfh hfk hfl hfm hgh hgk hgl hgm hhk hhl hhm hkl hkm hlm] using hx
    rcases hxyz with hfx | hgx | hhx | hkx | hlx | hmx
    · exact hfn.not_mem_left hfx hnx
    · exact hgn.not_mem_left hgx hnx
    · exact hhn.not_mem_left hhx hnx
    · exact hkn.not_mem_left hkx hnx
    · exact hln.not_mem_left hlx hnx
    · exact hmn.not_mem_left hmx hnx
  rw [add_assoc, support_add_eq hsum,
    support_add_add_add_add_add_eq (f := f) (g := g) (h := h) (k := k) (l := l) hfg hfh hfk hfl
      hfm hgh hgk hgl hgm hhk hhl hhm hkl hkm hlm]
  simp [union_comm, union_left_comm, union_assoc]

/-- If eight admissible functions are pairwise disjoint, then the support of their sum is the
union of their supports. -/
theorem support_add_add_add_add_add_add_add_add_eq {f g h k l m n o : ZetaAdmissibleFunction}
    (hfg : Disjoint (Function.support f) (Function.support g))
    (hfh : Disjoint (Function.support f) (Function.support h))
    (hfk : Disjoint (Function.support f) (Function.support k))
    (hfl : Disjoint (Function.support f) (Function.support l))
    (hfm : Disjoint (Function.support f) (Function.support m))
    (hfn : Disjoint (Function.support f) (Function.support n))
    (hfo : Disjoint (Function.support f) (Function.support o))
    (hgh : Disjoint (Function.support g) (Function.support h))
    (hgk : Disjoint (Function.support g) (Function.support k))
    (hgl : Disjoint (Function.support g) (Function.support l))
    (hgm : Disjoint (Function.support g) (Function.support m))
    (hgn : Disjoint (Function.support g) (Function.support n))
    (hgo : Disjoint (Function.support g) (Function.support o))
    (hhk : Disjoint (Function.support h) (Function.support k))
    (hhl : Disjoint (Function.support h) (Function.support l))
    (hhm : Disjoint (Function.support h) (Function.support m))
    (hhn : Disjoint (Function.support h) (Function.support n))
    (hho : Disjoint (Function.support h) (Function.support o))
    (hkl : Disjoint (Function.support k) (Function.support l))
    (hkm : Disjoint (Function.support k) (Function.support m))
    (hkn : Disjoint (Function.support k) (Function.support n))
    (hko : Disjoint (Function.support k) (Function.support o))
    (hlm : Disjoint (Function.support l) (Function.support m))
    (hln : Disjoint (Function.support l) (Function.support n))
    (hlo : Disjoint (Function.support l) (Function.support o))
    (hmn : Disjoint (Function.support m) (Function.support n))
    (hmo : Disjoint (Function.support m) (Function.support o))
    (hno : Disjoint (Function.support n) (Function.support o)) :
    Function.support (f + g + h + k + l + m + n + o) =
      Function.support f ∪ Function.support g ∪ Function.support h ∪ Function.support k ∪
        Function.support l ∪ Function.support m ∪ Function.support n ∪ Function.support o := by
  have hsum : Disjoint (Function.support (f + g + h + k + l + m + n)) (Function.support o) := by
    intro x hx hox
    have hxyz : x ∈ Function.support f ∪ Function.support g ∪ Function.support h ∪
        Function.support k ∪ Function.support l ∪ Function.support m ∪ Function.support n := by
      simpa [support_add_add_add_add_add_add_add_eq (f := f) (g := g) (h := h) (k := k)
        (l := l) (m := m) (n := n) hfg hfh hfk hfl hfm hfn hgh hgk hgl hgm hgn hhk hhl hhm
        hhn hkl hkm hkn hlm hln hmn] using hx
    rcases hxyz with hfx | hgx | hhx | hkx | hlx | hmx | hnx
    · exact hfo.not_mem_left hfx hox
    · exact hgo.not_mem_left hgx hox
    · exact hho.not_mem_left hhx hox
    · exact hko.not_mem_left hkx hox
    · exact hlo.not_mem_left hlx hox
    · exact hmo.not_mem_left hmx hox
    · exact hno.not_mem_left hnx hox
  rw [add_assoc, support_add_eq hsum,
    support_add_add_add_add_add_add_add_eq (f := f) (g := g) (h := h) (k := k) (l := l)
      (m := m) (n := n) hfg hfh hfk hfl hfm hfn hgh hgk hgl hgm hgn hhk hhl hhm hhn hkl hkm hkn
      hlm hln hmn]
  simp [union_comm, union_left_comm, union_assoc]

/-- If nine admissible functions are pairwise disjoint, then the support of their sum is the
union of their supports. -/
theorem support_add_add_add_add_add_add_add_add_add_eq
    {f g h k l m n o p : ZetaAdmissibleFunction}
    (hfg : Disjoint (Function.support f) (Function.support g))
    (hfh : Disjoint (Function.support f) (Function.support h))
    (hfk : Disjoint (Function.support f) (Function.support k))
    (hfl : Disjoint (Function.support f) (Function.support l))
    (hfm : Disjoint (Function.support f) (Function.support m))
    (hfn : Disjoint (Function.support f) (Function.support n))
    (hfo : Disjoint (Function.support f) (Function.support o))
    (hfp : Disjoint (Function.support f) (Function.support p))
    (hgh : Disjoint (Function.support g) (Function.support h))
    (hgk : Disjoint (Function.support g) (Function.support k))
    (hgl : Disjoint (Function.support g) (Function.support l))
    (hgm : Disjoint (Function.support g) (Function.support m))
    (hgn : Disjoint (Function.support g) (Function.support n))
    (hgo : Disjoint (Function.support g) (Function.support o))
    (hgp : Disjoint (Function.support g) (Function.support p))
    (hhk : Disjoint (Function.support h) (Function.support k))
    (hhl : Disjoint (Function.support h) (Function.support l))
    (hhm : Disjoint (Function.support h) (Function.support m))
    (hhn : Disjoint (Function.support h) (Function.support n))
    (hho : Disjoint (Function.support h) (Function.support o))
    (hhp : Disjoint (Function.support h) (Function.support p))
    (hkl : Disjoint (Function.support k) (Function.support l))
    (hkm : Disjoint (Function.support k) (Function.support m))
    (hkn : Disjoint (Function.support k) (Function.support n))
    (hko : Disjoint (Function.support k) (Function.support o))
    (hkp : Disjoint (Function.support k) (Function.support p))
    (hlm : Disjoint (Function.support l) (Function.support m))
    (hln : Disjoint (Function.support l) (Function.support n))
    (hlo : Disjoint (Function.support l) (Function.support o))
    (hlp : Disjoint (Function.support l) (Function.support p))
    (hmn : Disjoint (Function.support m) (Function.support n))
    (hmo : Disjoint (Function.support m) (Function.support o))
    (hmp : Disjoint (Function.support m) (Function.support p))
    (hno : Disjoint (Function.support n) (Function.support o))
    (hnp : Disjoint (Function.support n) (Function.support p))
    (hop : Disjoint (Function.support o) (Function.support p)) :
    Function.support (f + g + h + k + l + m + n + o + p) =
      Function.support f ∪ Function.support g ∪ Function.support h ∪ Function.support k ∪
        Function.support l ∪ Function.support m ∪ Function.support n ∪ Function.support o ∪
        Function.support p := by
  have hsum : Disjoint (Function.support (f + g + h + k + l + m + n + o)) (Function.support p) := by
    intro x hx hpx
    have hxyz : x ∈ Function.support f ∪ Function.support g ∪ Function.support h ∪
        Function.support k ∪ Function.support l ∪ Function.support m ∪ Function.support n ∪
        Function.support o := by
      simpa [support_add_add_add_add_add_add_add_add_eq (f := f) (g := g) (h := h) (k := k)
        (l := l) (m := m) (n := n) (o := o) hfg hfh hfk hfl hfm hfn hfo hgh hgk hgl hgm hgn
        hgo hgp hhk hhl hhm hhn hho hhp hkl hkm hkn hko hkp hlm hln hlo hlp hmn hmo hmp hno
        hnp hop] using hx
    rcases hxyz with hfx | hgx | hhx | hkx | hlx | hmx | hnx | hox
    · exact hfp.not_mem_left hfx hpx
    · exact hgp.not_mem_left hgx hpx
    · exact hhp.not_mem_left hhx hpx
    · exact hkp.not_mem_left hkx hpx
    · exact hlp.not_mem_left hlx hpx
    · exact hmp.not_mem_left hmx hpx
    · exact hnp.not_mem_left hnx hpx
    · exact hop.not_mem_left hox hpx
  rw [add_assoc, support_add_eq hsum,
    support_add_add_add_add_add_add_add_add_eq (f := f) (g := g) (h := h) (k := k) (l := l)
      (m := m) (n := n) (o := o) hfg hfh hfk hfl hfm hfn hfo hgh hgk hgl hgm hgn hgo hgp hhk
      hhl hhm hhn hho hhp hkl hkm hkn hko hkp hlm hln hlo hlp hmn hmo hmp hno hnp hop]
  simp [union_comm, union_left_comm, union_assoc]

/-- If a finite family has pairwise disjoint supports, then the finite sums over any two disjoint
subfamilies are disjoint. -/
theorem disjoint_support_sum_sum_of_pairwise {α : Type*} (s t : Finset α)
    (f : α → ZetaAdmissibleFunction)
    (hpair : Pairwise (fun i j => Disjoint (Function.support (f i)) (Function.support (f j))))
    (hst : Disjoint s t) :
    Disjoint (Function.support (∑ a in s, f a)) (Function.support (∑ b in t, f b)) := by
  intro x hx hy
  have hs : x ∈ s.biUnion fun a => Function.support (f a) := by
    exact support_sum_subset (s := s) (f := f) hx
  have ht : x ∈ t.biUnion fun b => Function.support (f b) := by
    exact support_sum_subset (s := t) (f := f) hy
  rcases Finset.mem_biUnion.mp hs with ⟨a, ha, hax⟩
  rcases Finset.mem_biUnion.mp ht with ⟨b, hb, hbx⟩
  have hab : a ≠ b := by
    intro hab
    exact hst.not_mem_left (by simpa [hab] using ha) (by simpa [hab] using hb)
  exact (hpair hab).not_mem_left hax hbx

/-- If every scaled summand in one finite family is disjoint from every summand in another finite
family, then the finite linear combination is disjoint from the other finite sum. -/
theorem disjoint_support_sum_smul_sum {α β : Type*} (s : Finset α) (t : Finset β)
    (c : α → ℂ) (f : α → ZetaAdmissibleFunction) (g : β → ZetaAdmissibleFunction)
    (hdisjoint : ∀ a ∈ s, ∀ b ∈ t,
      Disjoint (Function.support (c a • f a)) (Function.support (g b))) :
    Disjoint (Function.support (∑ a in s, c a • f a)) (Function.support (∑ b in t, g b)) := by
  intro x hx hy
  have hs : x ∈ s.biUnion fun a => Function.support (c a • f a) := by
    exact support_sum_smul_subset (s := s) (c := c) (f := f) hx
  have ht : x ∈ t.biUnion fun b => Function.support (g b) := by
    exact support_sum_subset (s := t) (f := g) hy
  rcases Finset.mem_biUnion.mp hs with ⟨a, ha, hax⟩
  rcases Finset.mem_biUnion.mp ht with ⟨b, hb, hbx⟩
  exact (hdisjoint a ha b hb).not_mem_left hax hbx

/-- If every scaled summand in one finite family is disjoint from every scaled summand in another
finite family, then the two finite linear combinations are disjoint. -/
theorem disjoint_support_sum_smul_sum_smul {α β : Type*} (s : Finset α) (t : Finset β)
    (c : α → ℂ) (d : β → ℂ) (f : α → ZetaAdmissibleFunction) (g : β → ZetaAdmissibleFunction)
    (hdisjoint : ∀ a ∈ s, ∀ b ∈ t,
      Disjoint (Function.support (c a • f a)) (Function.support (d b • g b))) :
    Disjoint (Function.support (∑ a in s, c a • f a))
      (Function.support (∑ b in t, d b • g b)) := by
  intro x hx hy
  have hs : x ∈ s.biUnion fun a => Function.support (c a • f a) := by
    exact support_sum_smul_subset (s := s) (c := c) (f := f) hx
  have ht : x ∈ t.biUnion fun b => Function.support (d b • g b) := by
    exact support_sum_smul_subset (s := t) (c := d) (f := g) hy
  rcases Finset.mem_biUnion.mp hs with ⟨a, ha, hax⟩
  rcases Finset.mem_biUnion.mp ht with ⟨b, hb, hbx⟩
  exact (hdisjoint a ha b hb).not_mem_left hax hbx

/-- Translating an admissible function preserves compact support. -/
theorem hasCompactSupport_translate (c : ℝ) (f : ZetaAdmissibleFunction) :
    HasCompactSupport (translate c f) := by
  simpa [ZetaAdmissibleFunction.translate] using f.hasCompactSupport.comp continuous_add_right

/-- The support of a translate is the translate of the support. -/
theorem support_translate (c : ℝ) (f : ZetaAdmissibleFunction) :
    Function.support (translate c f) = (fun x => x - c) ⁻¹' Function.support f := by
  ext x
  simp [Function.mem_support, ZetaAdmissibleFunction.translate_apply, sub_eq_add_neg, add_comm,
    add_left_comm, add_assoc]

/-- Translation preserves disjointness of supports. -/
theorem disjoint_support_translate (c : ℝ) (f g : ZetaAdmissibleFunction)
    (hfg : Disjoint (Function.support f) (Function.support g)) :
    Disjoint (Function.support (translate c f)) (Function.support (translate c g)) := by
  rw [support_translate c f, support_translate c g]
  exact hfg.preimage (fun x => x - c)

/-- Translation preserves pairwise disjointness of supports on a finite family. -/
theorem pairwise_disjoint_support_translate {α : Type*} (c : ℝ) (f : α → ZetaAdmissibleFunction)
    (hfg : Pairwise (fun i j => Disjoint (Function.support (f i)) (Function.support (f j)))) :
    Pairwise (fun i j => Disjoint (Function.support (translate c (f i)))
      (Function.support (translate c (f j)))) := by
  intro i j hij
  exact disjoint_support_translate c (f i) (f j) (hfg hij)

/-- Reflecting an admissible function preserves compact support. -/
theorem hasCompactSupport_reflect (f : ZetaAdmissibleFunction) :
    HasCompactSupport (reflect f) := by
  simpa [ZetaAdmissibleFunction.reflect] using f.hasCompactSupport.comp continuous_neg

/-- The support of a reflection is the reflection of the support. -/
theorem support_reflect (f : ZetaAdmissibleFunction) :
    Function.support (reflect f) = (fun x => -x) ⁻¹' Function.support f := by
  ext x
  simp [Function.mem_support, ZetaAdmissibleFunction.reflect_apply]

/-- Scaling an admissible function on the real variable preserves compact support. -/
theorem hasCompactSupport_scale (a : ℝ) (f : ZetaAdmissibleFunction) :
    HasCompactSupport (scale a f) := by
  simpa [ZetaAdmissibleFunction.scale] using f.hasCompactSupport.comp continuous_const.mul

/-- The support of a scaled function is the pullback of the original support under multiplication. -/
theorem support_scale (a : ℝ) (f : ZetaAdmissibleFunction) :
    Function.support (scale a f) = (fun x => a * x) ⁻¹' Function.support f := by
  ext x
  simp [Function.mem_support, ZetaAdmissibleFunction.scale_apply]

/-- Scaling preserves disjointness of supports. -/
theorem disjoint_support_scale (a : ℝ) (f g : ZetaAdmissibleFunction)
    (hfg : Disjoint (Function.support f) (Function.support g)) :
    Disjoint (Function.support (scale a f)) (Function.support (scale a g)) := by
  rw [support_scale a f, support_scale a g]
  exact hfg.preimage (fun x => a * x)

/-- Scaling preserves pairwise disjointness of supports on a finite family. -/
theorem pairwise_disjoint_support_scale {α : Type*} (a : ℝ) (f : α → ZetaAdmissibleFunction)
    (hfg : Pairwise (fun i j => Disjoint (Function.support (f i)) (Function.support (f j)))) :
    Pairwise (fun i j => Disjoint (Function.support (scale a (f i)))
      (Function.support (scale a (f j)))) := by
  intro i j hij
  exact disjoint_support_scale a (f i) (f j) (hfg hij)

/-- The support of the affine transport `translate c (scale t f)` is the affine pullback of the
original support. -/
theorem support_translate_scale (c t : ℝ) (f : ZetaAdmissibleFunction) :
    Function.support (translate c (scale t f)) =
      (fun x => t * (x + c)) ⁻¹' Function.support f := by
  ext x
  simp [Function.mem_support, ZetaAdmissibleFunction.translate_apply,
    ZetaAdmissibleFunction.scale_apply, mul_add, add_comm, add_left_comm, add_assoc]

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
