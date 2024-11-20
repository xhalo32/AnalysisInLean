import Mathlib

open Topology
open Filter
open Set

/-
# Basic results about supremums and infimums

Lemmas about supremums starting with `c` are easier to use as they are formulated using boundedness (`BddAbove`) assumptions. `c` stands for "Conditionally complete linear order".
-/

-- The supremum of a set is a member of its closure
#check csSup_mem_closure

-- Every element in the set is ≤ the supremum
#check le_csSup

-- `a` is ≥ the supremum of `s`, iff every element in `s` is ≤ `a`
#check csSup_le_iff

-- Set up some variables used in the lemmas
variable {a b : ℝ}
variable [hab : Fact (a ≤ b)]
variable {f : ℝ → ℝ} -- f is defined over all reals to avoid annoying subtypes

-- Here are some lemmas for you to get started
omit hab in
lemma s_bdd : BddAbove { x ∈ Icc a b | f x < 0 } := by
  rw [bddAbove_def]
  use b
  intro y hy
  rw [mem_setOf] at hy
  obtain ⟨yab, hy⟩ := hy
  rw [mem_Icc] at yab
  exact yab.2

lemma a_in_s (ha : f a < 0) : a ∈ { x ∈ Icc a b | f x < 0 } := by
  rw [mem_setOf]
  constructor
  · simp only [mem_Icc, le_refl, true_and, and_self, hab.elim]
  · exact ha

/--
# Bolzano theorem

A continuous function defined on a closed interval `[a, b]` has a zero if `f a < 0` and `f b > 0`.

## Proof

Follow <https://en.wikipedia.org/wiki/Intermediate_value_theorem#Proof_version_B> directly and use `u = 0`.

The key observation is that `{ x ∈ Icc a b | f x < 0 }` has a supremum `c` (by the completeness axiom of the Real numbers) which is the `x` for which `f x = 0`. Showing this can be done by contradiction.

Start by splitting the goal into cases `f c < 0`, `f c > 0` and `f c = 0`. Show a contradiction in the first two cases and the proof is complete.

Notice that due to a mistake in the proof on wikipedia `N > 1`, so use `N = δ / (b - c) + 1`.

## Useful theorems for formalizing from scratch

- `Metric.continuousOn_iff`
- `Real.dist_eq`
-/
theorem bolzano {ha : f a < 0} {hb : f b > 0} (h : ContinuousOn f (Icc a b)) : ∃ x, f x = 0 := by
  let s := { x ∈ Icc a b | f x < 0 }
  let c := sSup s

  -- The first lemma in the proof.
  -- Hint: use `csSup_mem_closure`.
  have c_mem_icc : c ∈ Icc a b
  · apply csSup_mem_closure
    · use a
      exact a_in_s ha
    · exact s_bdd
    rw [mem_setOf]
    constructor
    · exact isClosed_Icc
    · intro x xh
      rw [mem_setOf] at xh
      exact xh.1

  use c
  by_cases hf : f c < 0
  · -- Case f c < 0
    rw [Metric.continuousOn_iff] at h
    specialize h _ c_mem_icc
    specialize h (-f c) (by linarith)
    obtain ⟨δ, δh, h⟩ := h

    -- This will come in quite handy with `lt_div_iff₀`.
    -- Hint: `lt_of_le_of_ne` and `csSup_le_iff` might be helpful.
    have bc_pos : b - c > 0
    · rw [gt_iff_lt, lt_sub_iff_add_lt, zero_add]
      -- show < by showing ≤ and ≠
      apply lt_of_le_of_ne
      · rw [csSup_le_iff s_bdd]
        intro x xh
        rw [mem_setOf] at xh
        rw [mem_Icc] at xh
        exact xh.1.2
        use a
        exact @a_in_s _ _ hab f ha
      · intro eq
        rw [← eq] at hb
        exact not_lt_of_gt hb hf

    -- Choose a suitable N
    let N := δ / (b - c) + 1

    -- Error in the proof in wikipedia which only assumes N > 0
    -- Need > 1 so that `x` is closer than `δ` to c
    have nh : N > 1
    ·
      simp only [N, lt_add_iff_pos_left]
      rw [lt_div_iff₀ bc_pos]
      simp only [zero_mul, δh]

    -- Also useful in a future `lt_div_iff₀`
    have npos : N > 0
    · linarith

    let x := c + δ/N

    have hcx : c < x
    · simp only [x, lt_add_iff_pos_right]
      rw [lt_div_iff₀ npos]
      simp only [zero_mul, δh]

    -- This assumption is needed to specialize `h`
    -- Hint: use `le_csSup`.
    have x_icc : x ∈ Icc a b
    ·
      rw [mem_Icc]
      constructor
      · apply le_trans' hcx.le
        apply le_csSup s_bdd
        exact @a_in_s _ _ hab f ha
      · apply add_le_of_le_sub_left
        rw [div_le_iff₀ npos, mul_comm, ← div_le_iff₀ bc_pos]
        linarith

    -- Also needed to specialize `h`
    have xh : dist x c < δ
    · simp [x, δh.le, npos.le, abs_eq_self.mpr]
      rw [div_lt_iff₀ npos]
      rw [lt_mul_iff_one_lt_right δh]
      exact nh

    -- Finally use continuity
    specialize h x x_icc xh

    -- Try to manipulate `h` so that you get `h : f x < 0`
    rw [Real.dist_eq] at h
    rw [abs_lt] at h
    obtain ⟨_, h⟩ := h
    rw [neg_eq_zero_sub] at h
    rw [sub_lt_sub_iff_right] at h

    -- We use the property of the supremum it to obtain a clear contradiction with `hcx`.
    have hxc : x ≤ c
    · apply le_csSup s_bdd
      rw [mem_setOf]
      exact ⟨x_icc, h⟩

    exfalso
    exact not_le_of_gt hcx hxc

  · -- Case f c ≥ 0
    by_cases hf' : f c > 0
    · -- Case f c > 0
      sorry -- I'm too lazy
    · -- Case f c = 0
      linarith
