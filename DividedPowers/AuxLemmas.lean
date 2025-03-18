import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Sym
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Finset.NatAntidiagonal

/-! # Auxiliary lemmas

This file contains auxiliary lemmas used in the formalization of divided powers on sums of ideals.
These lemmas are of two kinds:

- Lemmas to rewrite 4-fold sums with a different ordering of the variables.
- Lemmas to operate with the sum `Finset.sum (range (n + 1)) fun i => count i k * i`.

-/

open BigOperators Finset

section FourFoldSums

/-- The sum of `f(x, y)` on `x + y = m` and `z + t = n` and `x + z = u` and `y + t = v`
  is equal to the sum of `f(x, y)` on `x + y = m`, provided `f (x, y)` vanishes if `x > u` or
  `y > v`.
  This lemma is awkward and mathematically obvious, it just rewrites the sum using the variable `x`
  which determines `y`, `z`, `t`. However, one of its points is to reduce a 4-fold sum to a
  2-fold sum.  -/
theorem rewriting_4_fold_sums {α : Type*} [AddCommMonoid α] {m n u v : ℕ} (h : m + n = u + v)
  (f : ℕ × ℕ → α) {g : (ℕ × ℕ) × ℕ × ℕ → α} (hgf : g = fun x => f (x.fst.fst, x.fst.snd))
  (hf : ∀ x : ℕ × ℕ, u < x.fst ∨ v < x.snd → f x = 0) :
  (filter (fun x : (ℕ × ℕ) × ℕ × ℕ => x.fst.fst + x.snd.fst = u ∧ x.fst.snd + x.snd.snd = v)
    (antidiagonal m ×ˢ antidiagonal n)).sum g = (antidiagonal m).sum f := by
  have hq :∀ x ∈ filter
    (fun x : (ℕ × ℕ) × ℕ × ℕ => x.fst.fst + x.snd.fst = u ∧ x.fst.snd + x.snd.snd = v)
      (antidiagonal m ×ˢ antidiagonal n), x.fst ∈ antidiagonal m := by
    intro x; simp; intro h'; simp [h']
  rw [← sum_fiberwise_of_maps_to hq]
  apply sum_congr rfl
  rintro ⟨i, j⟩ hij; simp only [mem_antidiagonal] at hij
  rw [sum_filter, sum_filter]
  simp_rw [← ite_and]
  suffices hf' :
    ∀ x : (ℕ × ℕ) × ℕ × ℕ,
      ite ((x.fst.fst + x.snd.fst = u ∧ x.fst.snd + x.snd.snd = v) ∧ x.fst = (i, j)) (g x) 0 =
        ite ((x.fst.fst + x.snd.fst = u ∧ x.fst.snd + x.snd.snd = v) ∧ x.fst = (i, j)) 1 0 •
          f ⟨i, j⟩ by
    rw [sum_congr rfl fun x _ => hf' x, ← sum_smul]
    by_cases hij' : i ≤ u ∧ j ≤ v
    · conv_rhs => rw [← one_smul ℕ (f ⟨i, j⟩)]
      apply congr_arg₂ _ _ rfl
      rw [sum_eq_single (⟨⟨i, j⟩, ⟨u - i, v - j⟩⟩ : (ℕ × ℕ) × ℕ × ℕ)]
      simp only [Nat.add_sub_of_le hij'.1, Nat.add_sub_of_le hij'.2, eq_self_iff_true, and_self_iff,
        if_true]
      · rintro ⟨⟨x, y⟩, ⟨z, t⟩⟩ hb hb'; rw [if_neg]; intro hb''
        simp only [mem_product, mem_antidiagonal] at hb
        simp only [ne_eq, Prod.mk.injEq, not_and, and_imp] at hb'
        simp only [Prod.mk_inj] at hb''
        specialize hb' hb''.2.1 hb''.2.2
        rw [hb''.2.1, hb''.2.2] at hb
        apply hb'
        apply Nat.add_left_cancel; rw [Nat.add_sub_of_le hij'.1, ← hb''.2.1, hb''.1.1]
        apply Nat.add_left_cancel; rw [Nat.add_sub_of_le hij'.2, ← hb''.2.2, hb''.1.2]
      · intro hb; rw [if_neg]; intro hb'; apply hb
        simp only [eq_self_iff_true, and_true] at hb'
        simp only [mem_product, mem_antidiagonal]
        apply And.intro hij
        apply Nat.add_left_cancel; rw [h, ← hij]
        conv_rhs => rw [← hb'.1, ← hb'.2]
        simp only [← add_assoc, add_left_inj]
        simp only [add_assoc, add_right_inj]
        rw [add_comm]
    · simp only [not_and_or, not_le] at hij'
      rw [hf ⟨i, j⟩ hij', smul_zero]
  · intro x
    split_ifs with hx
    · simp only [one_smul, hgf, hx.2]
    · rw [zero_smul]

open BigOperators

variable {α : Type*} [AddMonoid α] [Finset.HasAntidiagonal α]

def antidiagonalTwoTwo (n : α) : Finset ((α × α) × (α × α)) :=
  (antidiagonal n).disjiUnion (fun k ↦ (antidiagonal k.1) ×ˢ (antidiagonal k.2))
  (fun k _ l _ hkl ↦ by
    simp_rw [disjoint_iff_ne]
    intro x hx y hy hxy
    simp only [mem_product, mem_antidiagonal] at hx hy
    apply hkl
    ext
    · simp only [← hx.1, ← hy.1, hxy]
    · simp only [← hx.2, ← hy.2, hxy])

theorem mem_antidiagonalTwoTwo {n : α} {x : (α × α) × (α × α)} :
    x ∈ antidiagonalTwoTwo n ↔ x.1.1 + x.1.2 + x.2.1 + x.2.2 = n := by
  simp only [antidiagonalTwoTwo, mem_disjiUnion, mem_antidiagonal, mem_product]
  exact ⟨fun ⟨u, hu, hx⟩ ↦ by rw [add_assoc, hx.2, hx.1, hu], fun hx ↦
    ⟨(x.1.1 + x.1.2, x.2.1 + x.2.2), by simp only [← add_assoc, hx],
     Prod.mk.inj rfl⟩⟩

theorem sum_antidiagonalTwoTwo_eq {β : Type*} [AddCommMonoid β] (f : (α × α) × (α × α) → β) (n : α) :
    ∑ x ∈ antidiagonalTwoTwo n, f x =
      ∑ m ∈ antidiagonal n, ∑ x ∈ antidiagonal m.1, ∑ y ∈ antidiagonal m.2, f (x, y) := by
  simp_rw [antidiagonalTwoTwo, sum_disjiUnion, Finset.sum_product]

 /-- Rewrites a 4-fold sum from variables (12)(34) to (13)(24) -/
theorem sum_4_rw {α : Type*} [AddCommMonoid α] (f : ℕ × ℕ × ℕ × ℕ → α) (n : ℕ) :
  (Finset.sum (range (n + 1)) fun k => Finset.sum (range (k + 1)) fun a =>
      Finset.sum (range (n - k + 1)) fun c => f (a, k - a, c, n - k - c)) =
    Finset.sum (range (n + 1)) fun l => Finset.sum (range (l + 1)) fun a =>
      Finset.sum (range (n - l + 1)) fun b => f (a, b, l - a, n - l - b) := by
  rw [sum_sigma', sum_sigma', sum_sigma', sum_sigma']
  let φ : (Σ (_ : Σ (_ : ℕ), ℕ), ℕ) → (Σ (_ : Σ (_ : ℕ), ℕ), ℕ) :=
    fun ⟨⟨k, a⟩, c⟩ => ⟨⟨a + c, a⟩, k - a⟩
  have h1 : ∀ (a : (_ : (_ : ℕ) × ℕ) × ℕ) (ha : a ∈ Finset.sigma
      (Finset.sigma (range (n + 1)) fun l => range (l + 1)) fun x => range (n - x.fst + 1)),
      (fun m _ => φ m) a ha ∈ Finset.sigma (Finset.sigma (range (n + 1))
        fun k => range (k + 1)) fun x => range (n - x.fst + 1) := by
    rintro ⟨⟨k, a⟩, c⟩ h
    simp only [mem_sigma, mem_range, Nat.lt_succ_iff] at h
    simp_rw [mem_sigma, mem_range, Nat.lt_succ_iff]
    refine ⟨⟨le_trans (add_le_add h.1.2 h.2) (by rw [add_comm, Nat.sub_add_cancel h.1.1]),
      le_self_add⟩, ?_⟩
    simp only [φ]
    rw [add_comm a c, ← Nat.sub_sub n c a]
    apply Nat.sub_le_sub_right
    rw [Nat.le_sub_iff_add_le (le_trans h.2 (Nat.sub_le n k))]
    rw [Nat.le_sub_iff_add_le h.1.1, add_comm] at h
    exact h.2
  have h2 : ∀ (a : (_ : (_ : ℕ) × ℕ) × ℕ) (ha : a ∈ Finset.sigma (Finset.sigma (range (n + 1))
      fun k => range (k + 1)) fun x => range (n - x.fst + 1)),
      (fun m _ => φ m) ((fun m _ => φ m) a ha) ((fun m _ => φ m) a ha ∈
        Finset.sigma (Finset.sigma (range (n + 1)) fun k => range (k + 1))
          fun x => range (n - x.fst + 1)) = a := by
    rintro ⟨⟨k, a⟩, c⟩ h
    simp only [mem_sigma, mem_range, Nat.lt_succ_iff] at h
    rw [Sigma.mk.inj_iff]
    simp only [Sigma.mk.inj_iff, heq_eq_eq, and_true, add_tsub_cancel_left]
    exact add_tsub_cancel_of_le h.1.2
  refine sum_bij' (fun m _ => φ m) (fun m _ => φ m) h1 h1 h2 h2 ?_
  · rintro ⟨⟨k, a⟩, c⟩ h
    simp only [mem_sigma, mem_range, Nat.lt_succ_iff] at h
    simp only [φ, Nat.add_sub_self_left a c, Nat.sub_sub,
      add_comm (a + c), ← add_assoc, Nat.sub_add_cancel h.1.2]

end FourFoldSums

open Multiset

theorem range_sym_weighted_sum_le {m n : ℕ} {k : Sym ℕ m} (hk : k ∈ (Finset.range (n + 1)).sym m) :
    ((Finset.range (n + 1)).sum fun i => count i k * i) ≤ m * n := by
  suffices h : ∀ i ∈ Finset.range (n + 1), count i k * i ≤ count i k * n by
    exact le_trans (sum_le_sum h) (by rw [← sum_mul, Finset.sum_count_of_mem_sym hk])
  exact fun _ hi ↦ Nat.mul_le_mul_left _ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))

theorem sum_range_sym_mul_compl {m n : ℕ} {k : Sym ℕ m} (hk : k ∈ (Finset.range (n + 1)).sym m) :
    (Finset.sum (range (n + 1)) fun i => count i k * (n - i)) =
      m * n - Finset.sum (range (n + 1)) fun i => count i k * i := by
  suffices h : (((Finset.range (n + 1)).sum fun i => count i k * (n - i)) +
        (Finset.range (n + 1)).sum fun i => count i k * i) = m * n by
    rw [← h, Nat.add_sub_cancel]
  simp_rw [← sum_add_distrib, ← mul_add]
  have hn : ∀ x ∈ Finset.range (n + 1), count x ↑k * (n - x + x) = count x ↑k * n := fun _ hx ↦ by
    rw [Nat.sub_add_cancel (Nat.lt_succ_iff.mp (Finset.mem_range.mp hx))]
  rw [sum_congr rfl hn, ← sum_mul, Finset.sum_count_of_mem_sym hk]
