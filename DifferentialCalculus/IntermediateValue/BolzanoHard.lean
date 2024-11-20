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
  sorry

lemma a_in_s (ha : f a < 0) : a ∈ { x ∈ Icc a b | f x < 0 } := by
  sorry

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

  sorry
