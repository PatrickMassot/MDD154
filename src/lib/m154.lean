import data.int.parity
import tactic.apply_fun
import data.real.basic
import algebra.group.pi

import lib.tactiques

namespace tactic.interactive
setup_tactic_parser

open tactic

meta def verifie : tactic unit :=
`[ { repeat { unfold limite_suite},
   repeat { unfold continue_en },
   push_neg,
   try { simp only [exists_prop] },
   try { exact iff.rfl },
   done } <|> fail "Ce n'est pas cela. Essayez encore." ]

end tactic.interactive

notation `|`:1024 x:1 `|`:1 := abs x

namespace m154

lemma inferieur_ssi {x y : ℝ} : x ≤ y ↔ 0 ≤ y - x :=
sub_nonneg.symm

lemma pos_pos {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x*y :=
mul_nonneg hx hy

lemma neg_neg {x y : ℝ} (hx : x ≤ 0) (hy : y ≤ 0) : 0 ≤ x*y :=
mul_nonneg_of_nonpos_of_nonpos hx hy

lemma inferieur_ssi' {x y : ℝ} : x ≤ y ↔ x - y ≤ 0 :=
by rw [show x-y = -(y-x), by ring, inferieur_ssi, neg_le, neg_zero]
end m154

open nat
def pgcd := nat.gcd

lemma divise_refl (a : ℕ) : a ∣ a :=
dvd_refl a

lemma divise_pgcd_ssi {a b c : ℕ} : c ∣ pgcd a b ↔ c ∣ a ∧ c ∣ b :=
dvd_gcd_iff

lemma divise_antisym {a b : ℕ} : a ∣ b → b ∣ a → a = b :=
dvd_antisymm

lemma divise_def (a b : ℤ) : a ∣ b ↔ ∃ k, b = a*k :=
iff.rfl

def pair (n : ℤ) := ∃ k, n = 2*k
def impair (n : ℤ) := ∃ k, n = 2*k + 1

lemma pair_ou_impair (n : ℤ) : pair n ∨ impair n :=
by by_cases h : n % 2 = 0 ; [left, {right ; rw int.mod_two_ne_zero at h}] ;
  rw [← int.mod_add_div n 2, h] ; use n/2 ; ring

lemma non_pair_et_impair (n : ℤ) : ¬ (pair n ∧ impair n) :=
begin
  rintro ⟨h, h'⟩,
  change even n at h,
  rw int.even_iff at h,
  rcases h' with ⟨k, rfl⟩,
  simp only [int.add_mul_mod_self_left, add_comm, euclidean_domain.mod_eq_zero] at h,
  cases h with l hl,
  rw eq_comm at hl,
  have := int.eq_one_of_mul_eq_one_right (by linarith) hl,
  linarith
end

lemma abs_inferieur_ssi (x y : ℝ) : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y :=
abs_le

lemma abs_diff (x y : ℝ) : |x - y| = |y - x| :=
abs_sub_comm x y

lemma pos_abs (x : ℝ) : |x| > 0 ↔ x ≠ 0 :=
abs_pos

variables {α : Type*} [linear_order α]
lemma superieur_max_ssi (p q r : α) : r ≥ max p q  ↔ r ≥ p ∧ r ≥ q :=
max_le_iff

lemma inferieur_max_gauche (p q : α) : p ≤ max p q :=
le_max_left _ _

lemma inferieur_max_droite (p q : α) : q ≤ max p q :=
le_max_right _ _

lemma egal_si_abs_diff_neg {a b : ℝ} : |a - b| ≤ 0 → a = b :=
eq_of_abs_sub_nonpos

lemma egal_si_abs_eps (x y : ℝ) : (∀ ε > 0, |x - y| ≤ ε) → x = y :=
begin
  intro h,
  apply egal_si_abs_diff_neg,
  by_contradiction H,
  push_neg at H,
  specialize h ( |x-y|/2) (by linarith),
  linarith
end

lemma ineg_triangle (x y : ℝ) : |x + y| ≤ |x| + |y| :=
abs_add x y

namespace m154
def limite_suite (u : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

lemma unicite_limite {u l l'}: limite_suite u l → limite_suite u l' → l = l' :=
begin
  -- sorry
  intros hl hl',
  apply egal_si_abs_eps,
  intros ε ε_pos,
  specialize hl (ε/2) (by linarith),
  cases hl with N hN,
  specialize hl' (ε/2) (by linarith),
  cases hl' with N' hN',
  specialize hN (max N N') (inferieur_max_gauche _ _),
  specialize hN' (max N N') (inferieur_max_droite _ _),
  calc |l - l'| = |(l-u (max N N')) + (u (max N N') -l')| : by ring_nf
  ... ≤ |l - u (max N N')| + |u (max N N') - l'| : by apply ineg_triangle
  ... =  |u (max N N') - l| + |u (max N N') - l'| : by rw abs_diff
  ... ≤ ε/2 + ε/2 : by linarith
  ... = ε : by ring,
end

end m154

open m154

def extraction (φ : ℕ → ℕ) := ∀ n m, n < m → φ n < φ m

-- Dans la suite, φ désignera toujours une fonction de ℕ dans ℕ
variable { φ : ℕ → ℕ}


/-- Un réel `a` est valeur d'adhérence d'une suite `u` s'il
existe une suite extraite de `u` qui tend vers `a`. -/
def valeur_adherence (u : ℕ → ℝ) (a : ℝ) :=
∃ φ, extraction φ ∧ limite_suite (u ∘ φ) a

/-- Toute extraction est supérieure à l'identité. -/
lemma extraction_superieur_id : extraction φ → ∀ n, n ≤ φ n :=
begin
  intros hyp n,
  induction n with n hn,
    exact nat.zero_le _,
  exact nat.succ_le_of_lt (by linarith [hyp n (n+1) (by linarith)]),
end

open filter

lemma extraction_machine (ψ : ℕ → ℕ) (hψ : ∀ n, ψ n ≥ n) : ∃ f : ℕ → ℕ, extraction (ψ ∘ f) ∧ ∀ n, f n ≥ n :=
begin
  refine ⟨λ n, nat.rec_on n 0 (λ n ih, ψ ih + 1), λ m n h, _, λ n, _⟩,
  { induction h; dsimp [(∘)],
    { exact hψ _ },
    { exact lt_trans h_ih (hψ _) } },
  { induction n, {apply le_refl},
    exact nat.succ_le_succ (le_trans n_ih (hψ _)) }
end