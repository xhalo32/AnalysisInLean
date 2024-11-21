import Mathlib
open Real
open Set

/-
# Bolzano-Weierstrass or sequential compactness theorem

In this file we will formalize Bolzano-Weierstrass using the proof from wikipedia: <https://en.wikipedia.org/wiki/Bolzano%E2%80%93Weierstrass_theorem#Proof>

We begin with `monotone_of_frequently_increasing` after which a more general result `eventually_monotone_of_frequently_increasing` is proven. Then the key lemma `subseq_monotone_or_antitone` and finally the theorem `tendsto_subseq_of_bddAbove_bddBelow`.

Good luck!
-/

/--
## Definition: Peak
Let us call an index `n` of a sequence a "peak" of the sequence when all values in the sequence that come after `n` are less than or equal to the peak.
-/
def IsPeak (x : ℕ → ℝ) (n : ℕ) := ∀ m > n, x m ≤ x n

-- Set of all peaks is infinite
def setOf_peaks_infinite (x : ℕ → ℝ) := { n | IsPeak x n }.Infinite

-- This is useful for working with the proof terms (⋯) that appear in the following lemma
set_option pp.proofs true in

/--
Lemma: Every frequently increasing sequence `(xₙ)` has a monotone subsequence. I.e. for each index `n` there is further index `m` such that `xₙ ≤ xₘ`.

We use `φ` to refer to a renumbering of indices such that `x ∘ φ` is the monotone subsequence.

Coming up with `φ` requires a tricky technique involving recursively choosing the next index that comes after the previous one.

Proof:

Let `φ₀` be the next index at which `x φ₀ > x₀` (given by `h`). Inductively define `φ (n + 1)` to be the next index at which `x (φ (n + 1)) > x φₙ`.

First, to show strict monotonicity of `φ`, i.e. `a < b ⊢ φ a < φ b` we use induction on `b`. In the base case we use the fact that `a` must equal `0` and `(h (φ 0)).choose_spec` to get `φ 0 < φ 1`. In the inductive case we use `(h (φ (b + 1))).choose_spec` to get the induction hypothesis `φ (b + 1 + 1) > φ (b + 1)` (formed when constructing `φ`) as well as the induction hypothesis `a < b + 1 → φ a < φ (b + 1)`.

To show monotonicity of `x ∘ φ`, i.e. `a ≤ b ⊢ x (φ a) ≤ x (φ b)` is similar, but we are working with ≤ instead of <.
-/
lemma monotone_of_frequently_increasing {x : ℕ → ℝ} (h : ∀ (n : ℕ), ∃ m > n, x n ≤ x m) : ∃ φ : ℕ → ℕ, StrictMono φ ∧ Monotone (x ∘ φ) := by
  -- Magic ingredient: the indices of the subsequence are generated iteratively with choice from `h`
  let φ (n : ℕ) : ℕ := by
    -- Try to define this inductively using `n`. Check the solution file `BolzanoWeierstrass.lean` if you get stuck.
    sorry

  use φ
  constructor
  · intro a b hab
    -- Offset `b` by one as `φ 0` is not less than `φ 0`
    have : ∃ b', b = b' + 1 := ⟨b - 1, (Nat.sub_add_cancel (by linarith)).symm⟩
    obtain ⟨b, eq⟩ := this
    subst eq

    induction b
    case zero
    · -- `(h (φ 0)).choose_spec.1` will come in handy
      sorry
    case succ b bih
    · -- Notice that `(h (φ (b + 1))).choose ≡ (φ (b + 1 + 1))`
      sorry

  · -- This proof is very similar to the above one, no offsetting required though.
    -- Check out `(h (φ (b))).choose_spec.2`
    sorry

/--
Lemma: Every eventually frequently increasing sequence `(xₙ)` has a monotone subsequence. I.e. for some `N` and each index `n > N` there is further index `m` such that `xₙ ≤ xₘ`.

The proof is very simple, offset every index by `N + 1` and apply `monotone_of_frequently_increasing`. Convincing Lean is the hard part.
-/
lemma eventually_monotone_of_frequently_increasing {x : ℕ → ℝ} (N : ℕ) (h : ∀ a > N, ∃ b > a, x a ≤ x b) : ∃ φ : ℕ → ℕ, StrictMono φ ∧ Monotone (x ∘ φ) := by
  -- Use the previous lemma to get a monotone subsequence
  have := monotone_of_frequently_increasing (x := x ∘ (. + N + 1))
  specialize this ?_
  · -- This requires a bit of fiddling with subtraction in ℕ
    sorry
  obtain ⟨φ, φ_mono, φh⟩ := this

  -- Now we use the shifted renumbering
  use (. + N + 1) ∘ φ
  -- This is more straight-forward
  sorry

/--
Lemma: Every infinite sequence `(xₙ)` in ℝ has an infinite monotone or antitone subsequence (a subsequence that is either non-decreasing or non-increasing).

This is the key lemma in proving Bolzano-Weierstrass, and the first section of the proof on wikipedia <https://en.wikipedia.org/wiki/Bolzano%E2%80%93Weierstrass_theorem#Proof>. Follow that proof and formalize every step.

Useful theorems:
- `Set.Infinite.exists_gt`
- `antitone_iff_forall_lt`
- `Set.not_infinite`
- `Set.Finite.exists_finset`
-/
lemma subseq_monotone_or_antitone (x : ℕ → ℝ) :
  (∃ φ : ℕ → ℕ, StrictMono φ ∧ Monotone (x ∘ φ)) ∨
  (∃ φ : ℕ → ℕ, StrictMono φ ∧ Antitone (x ∘ φ)) := by

  -- Start by case splitting on `setOf_peaks_infinite x`
  by_cases h : setOf_peaks_infinite x <;> rw [setOf_peaks_infinite] at h
  · -- Suppose first that the sequence has infinitely many peaks,
    -- which means there is an antitone subsequence defined by those peaks
    right

    -- First, we show nonemptyness of the set of peaks
    have ne : Nonempty {n | IsPeak x n}
    · sorry

    -- Next, we show that the set of peaks has no largest element.
    -- Here we need to work with subtypes because the elements are of type `Elem {n | IsPeak x n}`. If you have a `n : ℕ` and `nh : IsPeak x n`, you can form such an element using `⟨n, nh⟩`
    have nmo : NoMaxOrder {n | IsPeak x n} := {
      exists_gt := by
        sorry
    }

    -- Select `φ` such that it gives all peaks in order.
    -- `Nat.exists_strictMono` is very convenient for this.
    #check Nat.exists_strictMono

    -- `Subtype.val` gets us a seqence of numbers rather than peaks. `Subtype.val_prop` is useful inside the cases to get the subtype predicate
    -- use Subtype.val ∘ φ
    sorry

  ·
    by_cases ne : Set.Nonempty {n | IsPeak x n}
    · -- x has finitely many peaks (but at least one peak),
      -- which means there is a monotone subsequence starting after the last peak
      left

      -- Here, form the set `s : Finset ℕ` which is the finite set of peaks
      have s : Finset ℕ := sorry

      -- N is the index of the final peak
      let N := s.max' sorry

      -- Now we should show that after `N` there are no more peaks
      have no_more_peaks : ¬ ∃ m > N, IsPeak x m
      · sorry

      -- Using `no_more_peaks` we can show that the sequence must increase frequently
      have frequently_increasing : ∀ a > N, ∃ b > a, x a ≤ x b
      · sorry

      -- Here we get to use `eventually_monotone_of_frequently_increasing` now that we know `N` is the final peak
      sorry

    · -- There are no peaks, therefore there must be a monotone subsequence
      left

      -- Using the fact that the set of peaks is empty, like before, we can show that the sequence must increase frequently
      have frequently_increasing : ∀ a, ∃ b > a, x a ≤ x b
      · sorry

      -- And after applying `monotone_of_frequently_increasing` we are left with a completed proof.
      sorry

open Filter
open Topology

/--
## Bolzano-Weierstrass theorem in ℝ.

The theorem states that each infinite bounded sequence in ℝ has a convergent subsequence.

An equivalent formulation is that a subset of ℝ is sequentially compact if and only if it is closed and bounded.

Useful theorems:
- `tendsto_of_monotone` and `tendsto_of_antitone`
- `Filter.unbounded_of_tendsto_atTop` and `Filter.unbounded_of_tendsto_atBot`
- `range_subset_range_iff_exists_comp`
-/
theorem tendsto_subseq_of_bddAbove_bddBelow {x : ℕ → ℝ} (hx : BddAbove (range x) ∧ BddBelow (range x)) : ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ a, Tendsto (x ∘ φ) atTop (𝓝 a) := by
  -- Because every sequence has a monotone or antitone subsequence, we can case split on it
  cases' subseq_monotone_or_antitone x with subseq subseq
  · -- Monotone case
    -- Use monotone convergence theorem (`tendsto_of_monotone`) to show that `φ` either tends to some value or diverges
    sorry
  · -- Antitone case
    -- Use antitone convergence theorem (`tendsto_of_antitone`) to show that `φ` either tends to some value or divergesobtain ⟨φ, φ_mono, φh⟩ := subseq
    sorry
