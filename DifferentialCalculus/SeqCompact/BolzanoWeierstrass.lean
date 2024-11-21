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
    induction n
    case zero
    · exact (h 0).choose
    case succ _ φn
    · exact (h φn).choose -- Call h with the result of `φ n`

  use φ
  constructor
  · intro a b hab
    -- Offset `b` by one as `φ 0` is not less than `φ 0`
    have : ∃ b', b = b' + 1 := ⟨b - 1, (Nat.sub_add_cancel (by linarith)).symm⟩
    obtain ⟨b, eq⟩ := this
    subst eq

    induction b
    case zero
    · have : a = 0
      · linarith
      subst a
      exact (h (φ 0)).choose_spec.1
    case succ b bih
    · have hb := (h (φ (b + 1))).choose_spec.1
      -- Notice that `(h (φ (b + 1))).choose ≡ (φ (b + 1 + 1))`
      by_cases hsa : a = b + 1
      · subst a
        exact hb
        -- exact Nat.zero_lt_succ b
      · apply lt_trans' hb
        apply bih
        apply lt_of_le_of_ne
        · linarith
        · exact hsa

  · intro a b hab
    induction b
    case zero
    · have : a = 0
      · linarith
      subst a
      exact le_rfl
    case _ b bih
    · have hb := (h (φ (b))).choose_spec.2
      by_cases hsa : a = b + 1
      · subst a
        exact le_rfl
      · apply le_trans' hb
        apply bih
        apply Nat.le_of_lt_add_one
        apply lt_of_le_of_ne
        · linarith
        · exact hsa

/--
Lemma: Every eventually frequently increasing sequence `(xₙ)` has a monotone subsequence. I.e. for some `N` and each index `n > N` there is further index `m` such that `xₙ ≤ xₘ`.

The proof is very simple, offset every index by `N + 1` and apply `monotone_of_frequently_increasing`. Convincing Lean is the hard part.


-/
lemma eventually_monotone_of_frequently_increasing {x : ℕ → ℝ} (N : ℕ) (h : ∀ a > N, ∃ b > a, x a ≤ x b) : ∃ φ : ℕ → ℕ, StrictMono φ ∧ Monotone (x ∘ φ) := by
  have h' : (∀ (a : ℕ), ∃ b > a, (x ∘ fun x => x + N + 1) a ≤ (x ∘ fun x => x + N + 1) b)
  · intro a
    obtain ⟨b, bh⟩ := h (a + N + 1) (by linarith)

    have nb1 : N ≤ b - 1
    ·
      rw [← add_le_add_iff_right 1]
      rw [Nat.sub_add_cancel]
      linarith
      linarith

    use (b - 1 - N)
    constructor
    · -- this is annoyingly verbose
      rw [gt_iff_lt]
      rw [← add_lt_add_iff_right N]
      rw [← add_lt_add_iff_right 1]
      rw [Nat.sub_add_cancel]
      rw [Nat.sub_add_cancel]
      exact bh.1
      linarith
      exact nb1
    · simp
      rw [Nat.sub_add_cancel]
      rw [Nat.sub_add_cancel]
      exact bh.2
      linarith
      exact nb1

  -- Now we use the previous lemma to get a monotone subsequence
  have := monotone_of_frequently_increasing (x := x ∘ (. + N + 1))
  specialize this h'
  obtain ⟨φ, φ_mono, φh⟩ := this

  -- Now we use the shifted renumbering
  use (. + N + 1) ∘ φ
  constructor
  · intro a b hab
    simp only [Function.comp_apply, add_lt_add_iff_right]
    exact φ_mono hab
  · exact φh

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
    · obtain ⟨x, xh⟩ := h.nonempty
      use x

    -- Next, we show that the set of peaks has no largest element.
    -- Here we need to work with subtypes because the elements are of type `Elem {n | IsPeak x n}`. If you have a `n : ℕ` and `nh : IsPeak x n`, you can form such an element using `⟨n, nh⟩`
    have nmo : NoMaxOrder {n | IsPeak x n} := {
      exists_gt := by
        intro a
        obtain ⟨b, bh⟩ := Set.Infinite.exists_gt h a
        use ⟨b, bh.1⟩
        exact bh.2
    }

    -- Select `φ` such that it gives all peaks in order.
    -- `Nat.exists_strictMono` is very convenient for this.
    #check Nat.exists_strictMono
    have ⟨φ, φ_mono⟩ := Nat.exists_strictMono {n | IsPeak x n}

    -- There is probably a lemma about showing existence with subtype in the codomain implies existence which we could use here, but I just used `Subtype.val ∘ φ` and `Subtype.val_prop` inside the cases to get the subtype predicate.
    use Subtype.val ∘ φ
    constructor
    · exact φ_mono
    · rw [antitone_iff_forall_lt]
      intro a b h
      let φa := φ a
      have φah := mem_setOf.mp (Subtype.val_prop φa)

      -- We know that because φ a is a peak, then for all b > a, x (φ b) ≤ x (φ a)
      -- Note that φ b can be a peak but it doesn't have to be
      rw [IsPeak] at φah
      apply φah

      -- Therefore we need to show that φ b > φ a, which we know by monotonicity of φ
      exact φ_mono h

  ·
    by_cases ne : Set.Nonempty {n | IsPeak x n}
    · -- x has finitely many peaks (but at least one peak),
      -- which means there is a monotone subsequence starting after the last peak
      left
      rw [Set.not_infinite] at h
      have ⟨s, sh⟩ := Set.Finite.exists_finset h

      obtain ⟨n, nh⟩ := ne
      apply (sh n).mpr at nh
      have sne : s.Nonempty := ⟨n, nh⟩

      -- N is the index of the final peak
      let N := s.max' sne

      -- Now we should show that after `N` there are no more peaks
      have no_more_peaks : ¬ ∃ m > N, IsPeak x m
      · intro ⟨m, mh1, mh2⟩
        simp only [N] at mh1

        -- All elements in the set are smaller than the maximum
        have := Finset.le_max' s m $ (sh _).mpr mh2
        -- have : m ≤ N := this -- these are the same

        have := lt_of_lt_of_le mh1 this
        simp only [lt_self_iff_false] at this

      -- Using `no_more_peaks` we can show that the sequence must increase frequently
      have frequently_increasing : ∀ a > N, ∃ b > a, x a ≤ x b
      ·
        push_neg at no_more_peaks
        simp_rw [IsPeak] at no_more_peaks
        intro a ah
        specialize no_more_peaks _ ah
        push_neg at no_more_peaks
        obtain ⟨m, mh⟩ := no_more_peaks
        use m
        constructor <;> linarith

      -- Here we get to use `eventually_monotone_of_frequently_increasing` now that we know `N` is the final peak
      exact eventually_monotone_of_frequently_increasing N frequently_increasing

    · -- There are no peaks, therefore there must be a monotone subsequence
      left

      -- Using the fact that the set of peaks is empty, like before, we can show that the sequence must increase frequently
      have frequently_increasing : ∀ a, ∃ b > a, x a ≤ x b
      ·
        push_neg at ne
        simp_rw [eq_empty_iff_forall_not_mem, mem_setOf] at ne
        simp_rw [IsPeak] at ne
        intro a
        specialize ne a
        push_neg at ne
        obtain ⟨m, mh⟩ := ne
        use m
        constructor <;> linarith

      -- And after applying `monotone_of_frequently_increasing` we are left with a completed proof.
      exact monotone_of_frequently_increasing frequently_increasing

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
    obtain ⟨φ, φ_mono, φh⟩ := subseq
    use φ
    refine ⟨φ_mono, ?_⟩

    -- Monotone convergence theorem: `φ` either tends to some value or diverges
    cases' tendsto_of_monotone φh with subseq subseq
    · -- Derive a contradiction using the fact that `x` is bounded from above
      have := Filter.unbounded_of_tendsto_atTop subseq
      exfalso
      apply this

      have range_subset : range (x ∘ φ) ⊆ range x
      · rw [range_subset_range_iff_exists_comp]
        use φ

      rw [not_bddAbove_iff] at this
      rw [bddAbove_def] at *
      obtain ⟨n, nh⟩ := hx.1
      refine ⟨n, fun y yh ↦ ?_⟩
      apply nh
      exact range_subset yh
    · exact subseq
  · obtain ⟨φ, φ_mono, φh⟩ := subseq
    use φ
    refine ⟨φ_mono, ?_⟩
    cases' tendsto_of_antitone φh with subseq subseq
    · -- Derive a contradiction using the fact that `x` is bounded from below
      have := Filter.unbounded_of_tendsto_atBot subseq
      exfalso
      apply this

      have range_subset : range (x ∘ φ) ⊆ range x
      · rw [range_subset_range_iff_exists_comp]
        use φ

      rw [not_bddBelow_iff] at this
      rw [bddBelow_def] at *
      obtain ⟨n, nh⟩ := hx.2
      refine ⟨n, fun y yh ↦ ?_⟩
      apply nh
      exact range_subset yh
    · exact subseq
