import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
An information bound for non-adaptive incidence probes. Thirty distinct binary
signatures of length eight cannot have only six positive answers in each column.
This is a combinatorial bound; it does not assume that the signatures come from
octonions, nor does it prove optimality of any longer probe set.
-/

namespace MathResearch.ProbeLowerBound

abbrev Word := Fin 8 → Bool

def weight (w : Word) : ℕ := ∑ j, if w j then 1 else 0

def deficit (w : Word) : ℕ := 2 - weight w

theorem total_deficit : ∑ w : Word, deficit w = 10 := by
  decide +kernel

theorem weight_add_deficit (w : Word) : 2 ≤ weight w + deficit w := by
  unfold deficit
  omega

theorem thirty_distinct_words_weight (code : Fin 30 → Word)
    (hinj : Function.Injective code) : 50 ≤ ∑ i, weight (code i) := by
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin 30))) => weight_add_deficit (code i))
  have hd : (∑ i, deficit (code i)) ≤ 10 := by
    calc
      (∑ i, deficit (code i)) = ∑ w ∈ Finset.univ.image code, deficit w := by
        rw [Finset.sum_image]
        intro i _ j _ hij
        exact hinj hij
      _ ≤ ∑ w : Word, deficit w := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ = 10 := total_deficit
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] at hsum
  omega

theorem eight_probes_impossible (code : Fin 30 → Word)
    (hcolumn : ∀ j, (∑ i : Fin 30, if code i j then 1 else 0) = 6) :
    ¬ Function.Injective code := by
  intro hinj
  have hlower := thirty_distinct_words_weight code hinj
  have htotal : (∑ i, weight (code i)) = 48 := by
    unfold weight
    rw [Finset.sum_comm]
    simp [hcolumn]
  omega

/-- Fewer columns cannot help: repeat an existing column to reach eight.
The zero-column case is handled without assuming a column exists. -/
theorem at_most_eight_probes_impossible {n : ℕ} (hn : n ≤ 8)
    (code : Fin 30 → Fin n → Bool)
    (hcolumn : ∀ j, (∑ i : Fin 30, if code i j then 1 else 0) = 6) :
    ¬ Function.Injective code := by
  intro hinj
  by_cases hn0 : n = 0
  · subst n
    have heq : code 0 = code 1 := funext (fun j => Fin.elim0 j)
    have hbad := hinj heq
    norm_num at hbad
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    let select : Fin 8 → Fin n := fun j =>
      if h : j.val < n then ⟨j.val, h⟩ else ⟨0, hnpos⟩
    let padded : Fin 30 → Word := fun i j => code i (select j)
    have hpc : ∀ j, (∑ i : Fin 30, if padded i j then 1 else 0) = 6 := by
      intro j
      exact hcolumn (select j)
    have hpi : Function.Injective padded := by
      intro i k heq
      apply hinj
      funext j
      have h := congrFun heq (⟨j.val, lt_of_lt_of_le j.isLt hn⟩ : Fin 8)
      simpa [padded, select, j.isLt] using h
    exact eight_probes_impossible padded hpc hpi

#print axioms total_deficit
#print axioms weight_add_deficit
#print axioms thirty_distinct_words_weight
#print axioms eight_probes_impossible
#print axioms at_most_eight_probes_impossible

end MathResearch.ProbeLowerBound
