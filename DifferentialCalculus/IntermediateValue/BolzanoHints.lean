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
  · sorry

  use c
  by_cases hf : f c < 0
  · -- Case f c < 0
    -- Start by unfolding `ContinuousOn` at `h`
    -- rw [Metric...] at h

    -- Then specialize it with `x₀ = c` and `ε = -f c`
    -- specialize h ...

    -- Finally obtain the `δ` for which the function is within `ε` of `f c`
    obtain ⟨δ, δh, h⟩ := h

    -- This will come in quite handy with `lt_div_iff₀`.
    -- Hint: `lt_of_le_of_ne` and `csSup_le_iff` might be helpful.
    have bc_pos : b - c > 0
    · sorry

    -- Choose a suitable N
    let N := δ / (b - c) + 1

    -- Error in the proof in wikipedia which only assumes N > 0
    -- Need > 1 so that `x` is closer than `δ` to c
    have nh : N > 1
    · sorry

    -- Also useful in a future `lt_div_iff₀`
    have npos : N > 0
    · linarith

    let x := c + δ/N

    have hcx : c < x
    · sorry

    -- This assumption is needed to specialize `h`
    -- Hint: use `le_csSup`.
    have x_icc : x ∈ Icc a b
    · sorry

    -- Also needed to specialize `h`
    have xh : dist x c < δ
    · sorry

    -- Finally use continuity
    specialize h x x_icc xh

    -- Try to manipulate `h` so that you get `h : f x < 0`
    -- rw [Real.dist_eq] at h
    -- ...

    -- We use the property of the supremum it to obtain a clear contradiction with `hcx`.
    have hxc : x ≤ c
    · sorry

    exfalso
    exact not_le_of_gt hcx hxc

  · -- Case f c ≥ 0
    by_cases hf' : f c > 0
    · -- Case f c > 0
      sorry
    · -- Case f c = 0
      linarith
