import Mdd154.Lib


open Verbose French m154

private lemma abs_le_of_le_and_le {α : Type*} [LinearOrderedAddCommGroup α] {a b : α}
    (h : -b ≤ a ∧ a ≤ b) : |a| ≤ b := abs_le.2 h

private lemma abs_le_of_le_and_le' {α : Type*} [LinearOrderedAddCommGroup α] {a b : α}
    (h : a ≤ b ∧ -b ≤ a) : |a| ≤ b := abs_le.2 ⟨h.2, h.1⟩

lemma mul_le_mul_of_pos_left {α : Type*} {a b c : α}  [OrderedSemiring α]
    (h : 0 < a) (h' : b ≤ c) : a * b ≤ a * c :=
  mul_le_mul_of_nonneg_left h' h.le

lemma mul_le_mul_of_pos_right {α : Type*} {a b c : α} [OrderedSemiring α]
    (h : 0 < a) (h' : b ≤ c) : b*a ≤ c*a :=
  mul_le_mul_of_nonneg_right h' h.le

lemma not_gt_eq (x y : ℝ) (h : x = y) (h' : x > y) : Faux := h'.ne' h

lemma not_lt_eq (x y : ℝ) (h : x = y) (h' : x < y) : Faux := h'.ne h

lemma non_pair_impair (n : ℤ) (h : n est pair) (h' : n est impair) : False :=
  non_pair_et_impair n ⟨h, h'⟩

lemma pair_iff_even (n : ℤ) : n est pair ↔ Even n := by
  apply exists_congr (fun k ↦ ?_)
  rw [Int.two_mul]

lemma impair_iff_odd (n : ℤ) : n est impair ↔ Odd n := Iff.rfl

@[push_neg_extra]
lemma non_pair_ssi_impair (n : ℤ) : ¬ n est pair ↔ n est impair := by
  simp [pair_iff_even, impair_iff_odd]

@[push_neg_extra]
lemma non_impair_ssi_pair (n : ℤ) : ¬ n est impair ↔ n est pair := by
  simp [pair_iff_even, impair_iff_odd]

-- Les deux lemmes suivants sont nécéssaires si `sufficesPushNeg` a déplié la
-- définition de pair ou impair

@[push_neg_extra]
lemma non_pair_ssi_impair' (n : ℤ) : (∀ k, n ≠ 2*k) ↔ n est impair := by
  rw [← non_pair_ssi_impair, «pair», not_exists]

@[push_neg_extra]
lemma non_impair_ssi_pair' (n : ℤ) : (∀ k, n ≠ 2*k + 1) ↔ n est pair := by
  rw [← non_impair_ssi_pair, «impair», not_exists]

lemma impair_car_non_pair (n : ℤ) (h : ¬ n est pair) : n est impair :=
  (non_pair_ssi_impair n).1 h

lemma pair_car_non_impair (n : ℤ) (h : ¬ n est impair) : n est pair :=
  (non_impair_ssi_pair n).1 h

lemma non_pair_car_impair (n : ℤ) (h : n est impair) : ¬ n est pair :=
  (non_pair_ssi_impair n).2 h

lemma non_impair_car_pair (n : ℤ) (h : n est pair) : ¬ n est impair :=
  (non_impair_ssi_pair n).2 h

lemma impair_succ_pair (n : ℤ) (h : n est pair) : (n + 1) est impair := by
  rcases h with ⟨k, rfl⟩
  use k

lemma pair_succ_impair (n : ℤ) (h : n est impair) : (n + 1) est pair := by
  rcases h with ⟨k, rfl⟩
  use k+1
  ring

axiom Bar : Type
axiom buveur : Bar → Prop

postfix:90 "boit" => buveur

/-- Multiplicité de `2` dans la décomposition en produit de facteurs premiers d’un entier -/
axiom v₂ : ℤ → ℤ

axiom v₂_square (p : ℤ) : v₂ (p^2) est pair

axiom v₂_two_mul (p : ℤ) (hp : p ≠ 0) : v₂ (2*p) = v₂ p + 1

lemma abs_of_neg' {α : Type} [Lattice α] [AddGroup α] [AddLeftMono α]{a : α} (h : a < 0) : a = -|a| := by
  rw [abs_of_neg h]
  simp

lemma abs_of_nonneg' (x : ℝ) (h : x ≥ 0) : |x| = x := abs_of_nonneg h

lemma non_le_lt (a b : ℝ) (h : a ≤ b) (h' : b < a) : False := lt_irrefl a (lt_of_le_of_lt h h')
lemma non_lt_le (a b : ℝ) (h : a < b) (h' : b ≤ a) : False := lt_irrefl a (lt_of_lt_of_le h h')

configureAnonymousFactSplittingLemmas
le_of_abs_le' le_of_abs_le le_le_of_abs_le' le_le_of_abs_le le_le_of_max_le
eq_zero_or_eq_zero_of_mul_eq_zero le_antisymm le_antisymm'
non_zero_abs_pos carre_pos
m154.pos_pos m154.neg_neg
extraction_superieur_id extraction_croissante unicite_limite
Iff.symm
le_max_left le_max_right le_of_max_le_left le_of_max_le_right
ex_mul_of_dvd ex_mul_of_dvd'
abs_diff ineg_triangle abs_plus
le_trans lt_of_le_of_lt lt_of_lt_of_le lt_trans
abs_of_nonneg' abs_of_neg abs_of_neg' abs_of_nonpos sq_nonneg
add_pos mul_pos
pow_le_pow_left₀
mul_le_mul_of_pos_right mul_le_mul_of_pos_left
not_gt_eq not_lt_eq
non_pair_impair pair_car_non_impair impair_car_non_pair non_pair_car_impair non_impair_car_pair
pair_succ_impair impair_succ_pair
Or.resolve_left Or.resolve_right
v₂_square v₂_two_mul pow_ne_zero
non_le_lt non_lt_le

configureHelpProviders SinceHypHelp SinceGoalHelp helpByContradictionGoal helpShowContrapositiveGoal

macro:max (priority := high) atomic("|" noWs) a:term noWs "|" : term => `(@abs ℝ _ _ $a)
