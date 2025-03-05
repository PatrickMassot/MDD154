import Verbose.French.All
import Mdd154.Notation3


def surjective (f : ℝ → ℝ) := ∀ y, ∃ x, f x = y

notation:50 f:80 " est surjective" => surjective f

def injective (f : ℝ → ℝ) := ∀ x y, f x = f y → x = y

notation:50 f:80 " est injective" => injective f

def paire (f : ℝ → ℝ) := ∀ x, f (-x) = f x

notation:50 f:80 " est paire" => paire f

def impaire (f : ℝ → ℝ) := ∀ x : ℝ, f (-x) = -f x

notation:50 f:80 " est impaire" => impaire f

def croissante {α β : Type} [LE α] [LE β] (f : α → β) := ∀ x₁, (∀ x₂, x₁ ≤ x₂ ⇒ f x₁ ≤ f x₂)

notation:50 f:80 " est croissante" => croissante f

def decroissante {α β : Type} [LE α] [LE β] (f : α → β) := ∀ x₁ x₂, x₁ ≤ x₂ ⇒ f x₁ ≥ f x₂

notation:50 f:80 " est décroissante" => decroissante f

def limite_suite (u : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

notation3:50 u:80 " tend vers " l => limite_suite u l

/-- La suite `u` tend vers `+∞`. -/
def limite_infinie_suite (u : ℕ → ℝ) := ∀ A, ∃ N, ∀ n ≥ N, u n ≥ A

notation3:50 u:80 " tend vers +∞"  => limite_infinie_suite u

def est_borne_sup (M : ℝ) (u : ℕ → ℝ) :=
(∀ n, u n ≤ M) ∧ ∀ ε > 0, ∃ n₀, u n₀ ≥ M - ε

notation3:50 M:80 " est borne sup de " u => est_borne_sup M u

namespace m154

lemma inferieur_ssi {x y : ℝ} : x ≤ y ↔ 0 ≤ y - x :=
sub_nonneg.symm

lemma pos_pos {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x*y :=
mul_nonneg hx hy

lemma neg_neg {x y : ℝ} (hx : x ≤ 0) (hy : y ≤ 0) : 0 ≤ x*y :=
mul_nonneg_of_nonpos_of_nonpos hx hy

lemma inferieur_ssi' {x y : ℝ} : x ≤ y ↔ x - y ≤ 0 :=
by rw [show x-y = -(y-x) by ring, inferieur_ssi, neg_le, neg_zero]

lemma inferieur_diff_pos {x y : ℝ} : x ≤ y → 0 ≤ y - x :=
sub_nonneg.mpr

lemma diff_pos_inferieur {x y : ℝ} : 0 ≤ y - x → x ≤ y:=
sub_nonneg.mp

lemma inferieur_diff_neg {x y : ℝ} : x ≤ y → x - y ≤ 0 :=
sub_nonpos.mpr

lemma diff_neg_inferieur {x y : ℝ} : x - y ≤ 0 → x ≤ y:=
sub_nonpos.mp

lemma carre_pos {a : ℝ} : a > 0 → a^2 > 0 := sq_pos_of_pos

end m154

section

def pgcd := Nat.gcd

lemma divise_refl (a : ℕ) : a ∣ a :=
dvd_refl a

axiom divise_pgcd_ssi {a b c : ℕ} : c ∣ pgcd a b ↔ c ∣ a ∧ c ∣ b

axiom divise_si_divise_pgcd {a b c : ℕ} : c ∣ pgcd a b → c ∣ a ∧ c ∣ b
axiom divise_si_divise_left {a b c : ℕ} : c ∣ pgcd a b → c ∣ a
axiom divise_si_divise_right {a b c : ℕ} : c ∣ pgcd a b → c ∣ b
axiom divise_pgcd_si {a b c : ℕ} :  c ∣ a → c ∣ b → c ∣ pgcd a b
axiom pgcd_divise_left {a b : ℕ} : pgcd a b ∣ a
axiom pgcd_divise_right {a b : ℕ} : pgcd a b ∣ b

lemma divise_antisym {a b : ℕ} : a ∣ b → b ∣ a → a = b :=
dvd_antisymm

lemma divise_def (a b : ℤ) : a ∣ b ↔ ∃ k, b = a*k :=
Iff.rfl

def pair (n : ℤ) := ∃ k, n = 2*k
notation:50 n:70 " est pair" => pair n

def impair (n : ℤ) := ∃ k, n = 2*k + 1
notation:50 n:70 " est impair" => impair n

lemma pair_ou_impair (n : ℤ) : n est pair ∨ n est impair := by
  convert Int.even_or_odd n
  ext n
  rw [even_iff_exists_two_nsmul]
  rfl

lemma non_pair_et_impair (n : ℤ) : ¬ (n est pair ∧ n est impair) := by
  rintro ⟨⟨k, rfl⟩, ⟨l, h⟩⟩
  omega
end

lemma abs_inferieur_ssi {x y : ℝ} : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y :=
abs_le

lemma abs_diff (x y : ℝ) : |x - y| = |y - x| :=
abs_sub_comm x y

lemma pos_abs {x : ℝ} : |x| > 0 ↔ x ≠ 0 :=
abs_pos

lemma non_zero_abs_pos {a : ℝ} : a ≠ 0 → |a| > 0 :=
abs_pos.mpr

open Lean PrettyPrinter Delaborator SubExpr in
@[app_delab Max.max]
def delabMax : Delab := do
  let e ← getExpr
  guard <| e.isAppOfArity ``Max.max 4
  let m := mkIdent `max
  let x ← withNaryArg 2 delab
  let y ← withNaryArg 3 delab
  `($(m) $(x) $(y))

open Lean PrettyPrinter Delaborator SubExpr in
@[app_delab Min.min]
def delabMin : Delab := do
  let e ← getExpr
  guard <| e.isAppOfArity ``Min.min 4
  let m := mkIdent `min
  let x ← withNaryArg 2 delab
  let y ← withNaryArg 3 delab
  `($(m) $(x) $(y))

variable {α : Type*} [LinearOrder α]

lemma superieur_max_ssi (p q r : α) : r ≥ max p q  ↔ r ≥ p ∧ r ≥ q :=
max_le_iff

lemma inferieur_max_gauche (p q : α) : p ≤ max p q :=
le_max_left _ _

lemma inferieur_max_droite (p q : α) : q ≤ max p q :=
le_max_right _ _

lemma egal_si_abs_diff_neg {a b : ℝ} : |a - b| ≤ 0 → a = b :=
eq_of_abs_sub_nonpos

lemma egal_si_abs_eps (x y : ℝ) : (∀ ε > 0, |x - y| ≤ ε) → x = y := by
  intro h
  apply egal_si_abs_diff_neg
  by_contra H
  push_neg at H
  specialize h ( |x-y|/2) (by linarith)
  linarith


lemma abs_plus (x y : ℝ) : |x + y| ≤ |x| + |y| :=
abs_add x y

lemma ineg_triangle (x y z : ℝ) : |x - y| ≤ |x - z| + |z - y| :=
abs_sub_le x z y

/- Note: A priori les deux variantes suivantes ne seront pas mentionées dans les feuilles.
Elles permettent d'économiser des `rw abs_diff` mais Patrick pense que ça n'en vaut pas la peine
car sur papier on écrirait ces étapes.
-/

lemma ineg_triangle' (x y z : ℝ) : |x - y| ≤ |x - z| + |y - z| := by
  rw [abs_diff y z]; apply abs_sub_le

lemma ineg_triangle'' (x y z : ℝ) : |x - y| ≤ |z - x| + |z - y| := by
  rw [abs_diff z x]; apply abs_sub_le

namespace m154

lemma unicite_limite {u l l'}: limite_suite u l → limite_suite u l' → l = l' := by
  intros hl hl'
  apply egal_si_abs_eps
  intros ε ε_pos
  specialize hl (ε/2) (by linarith)
  rcases hl with ⟨N, hN⟩
  specialize hl' (ε/2) (by linarith)
  rcases hl' with ⟨N', hN'⟩
  specialize hN (max N N') (inferieur_max_gauche _ _)
  specialize hN' (max N N') (inferieur_max_droite _ _)
  calc |l - l'| ≤ |u (max N N') - l| + |u (max N N') - l'| := by apply ineg_triangle''
  _ ≤ ε/2 + ε/2 := by linarith
  _ = ε := by ring


end m154

namespace M154
variable {a b c : ℝ}

lemma inferieur_mul_droite (hc : 0 ≤ c) (hab : a ≤ b) : a*c ≤ b*c :=
mul_le_mul_of_nonneg_right hab hc

lemma inferieur_mul_gauche (hc : 0 ≤ c) (hab : a ≤ b) : c*a ≤ c*b :=
mul_le_mul_of_nonneg_left hab hc

lemma inferieur_add_gauche : a ≤ b → c + a ≤ c + b :=
(add_le_add_iff_left c).mpr

lemma inferieur_add_droite : a ≤ b →  a + c ≤ b + c :=
(add_le_add_iff_right c).mpr

lemma inferieur_simpl_gauche : c + a ≤ c + b → a ≤ b :=
(add_le_add_iff_left c).mp

lemma inferieur_simpl_droite : a + c ≤ b + c → a ≤ b :=
(add_le_add_iff_right c).mp

end M154

open m154

def extraction (φ : ℕ → ℕ) := ∀ n m, n < m → φ n < φ m

notation3:50 φ:80 " est une extraction" => extraction φ

def suite_cauchy (u : ℕ → ℝ) := ∀ ε > 0, ∃ N, ∀ p ≥ N, ∀ q ≥ N, |u p - u q| ≤ ε

notation3:50 u:80 " est de Cauchy" => suite_cauchy u

-- Dans la suite, φ désignera toujours une fonction de ℕ dans ℕ
variable { φ : ℕ → ℕ}


/-- Un réel `a` est valeur d'adhérence d'une suite `u` s'il
existe une suite extraite de `u` qui tend vers `a`. -/
def valeur_adherence (u : ℕ → ℝ) (a : ℝ) :=
∃ φ, φ est une extraction ∧ limite_suite (u ∘ φ) a

notation3:50 a:80 " est valeur d'adhérence de " u => valeur_adherence u a

/-- Toute extraction est supérieure à l'identité. -/
lemma extraction_superieur_id : φ est une extraction → ∀ n, n ≤ φ n := by
  intros hyp n
  induction n with
  | zero => exact Nat.zero_le _
  | succ n hn => exact Nat.succ_le_of_lt (by linarith [hyp n (n+1) (by linarith)])




lemma extraction_machine (ψ : ℕ → ℕ) (hψ : ∀ n, ψ n ≥ n) :
    ∃ f : ℕ → ℕ, ψ ∘ f est une extraction ∧ ∀ n, f n ≥ n := by
  let θ : ℕ → ℕ := fun n ↦ Nat.recOn n 0 (fun n q ↦ ψ q + 1)
  refine ⟨θ, fun m n h ↦ ?_, fun n ↦ ?_⟩
  { induction h with
    | refl => exact hψ _
    | @step p Ih Ih' => simp at *; specialize hψ (θ <| p + 1); linarith }
  { induction n with
    | zero => apply le_refl
    | succ n ih =>  exact Nat.succ_le_succ (le_trans ih (hψ _)) }

macro "verifie" : tactic =>
`(tactic|
    first |(
        try unfold limite_suite;
        try unfold continue_en;
        push_neg;
        try simp only [exists_prop];
        try rfl ;
        done) |
      fail "Ce n'est pas cela. Essayez encore.")

section Subset
variable {α : Type*}

/- The Mathlib definition of `Set.Subset` uses a strict-implicit
argument which confuses Verbose Lean. So let us replace it. -/

protected def Verbose.French.Subset (s₁ s₂ : Set α) :=
  ∀ a, a ∈ s₁ → a ∈ s₂

instance (priority := high) Verbose.French.hasSubset : HasSubset (Set α) :=
  ⟨Verbose.French.Subset⟩

end Subset

open Verbose.French

lemma le_le_of_abs_le' {α : Type*} [LinearOrderedAddCommGroup α] {a b : α} : |a| ≤ b → a ≤ b ∧ -b ≤ a := fun h ↦ ⟨abs_le.1 h |>.2, abs_le.1 h |>.1⟩

lemma le_of_abs_le' {α : Type*} [LinearOrderedAddCommGroup α] {a b : α} : |a| ≤ b → -b ≤ a := fun h ↦ abs_le.1 h |>.1

lemma le_antisymm' {α : Type*} [PartialOrder α] {a b : α} (h : b ≤ a) (h' : a ≤ b) : a = b :=
  (le_antisymm h h').symm

lemma ex_mul_of_dvd {R : Type*} [CommSemiring R] {a b : R} (h : a ∣ b) : ∃ k, b = k * a := by
  rcases h with ⟨k, hk⟩
  use k
  rw [hk, mul_comm]

lemma ex_mul_of_dvd' {a b : ℤ} (h : ∃ k, b = k * a) : a ∣ b := by
   rcases h with ⟨k, hk⟩
   use k
   rw [hk, mul_comm]

private lemma abs_le_of_le_and_le {α : Type*} [LinearOrderedAddCommGroup α] {a b : α}
    (h : -b ≤ a ∧ a ≤ b) : |a| ≤ b := abs_le.2 h

private lemma abs_le_of_le_and_le' {α : Type*} [LinearOrderedAddCommGroup α] {a b : α}
    (h : a ≤ b ∧ -b ≤ a) : |a| ≤ b := abs_le.2 ⟨h.2, h.1⟩

configureAnonymousFactSplittingLemmas le_of_abs_le' le_of_abs_le le_le_of_abs_le' le_le_of_abs_le le_le_of_max_le eq_zero_or_eq_zero_of_mul_eq_zero le_antisymm le_antisymm' non_zero_abs_pos carre_pos m154.pos_pos m154.neg_neg extraction_superieur_id unicite_limite le_max_left le_max_right Iff.symm le_of_max_le_left le_of_max_le_right ex_mul_of_dvd ex_mul_of_dvd' abs_diff ineg_triangle abs_plus le_trans lt_of_le_of_lt lt_of_lt_of_le lt_trans abs_of_nonneg abs_of_neg abs_of_nonpos

configureAnonymousGoalSplittingLemmas LogicIntros AbsIntros Set.Subset.antisymm le_antisymm le_antisymm' lt_irrefl abs_le_of_le_and_le abs_le_of_le_and_le' egal_si_abs_eps

configureAnonymousCaseSplittingLemmas le_or_gt lt_or_gt_of_ne lt_or_eq_of_le eq_or_lt_of_le eq_zero_or_eq_zero_of_mul_eq_zero Classical.em pair_ou_impair le_total

configureAnonymousComputeLemmas abs_diff ineg_triangle abs_plus inferieur_max_gauche inferieur_max_droite

useDefaultDataProviders

useDefaultSuggestionProviders

configureUnfoldableDefs «croissante» «decroissante» «paire» «impaire»
  «valeur_adherence» «limite_suite» «surjective» «injective» «pair» «impair» «extraction» suite_cauchy limite_infinie_suite

-- Remarque : en arrivant aux feuilles de négations on pourra ajouter helpByContradictionGoal
configureHelpProviders SinceHypHelp SinceGoalHelp

disableWidget

macro_rules | `($x / $y)   => `(HDiv.hDiv ($x : ℝ) ($y : ℝ))

macro_rules | `($x ∣ $y)   => `(@Dvd.dvd ℤ Int.instDvd ($x : ℤ) ($y : ℤ))

macro "setup_env" : command => `(set_option linter.unusedTactic false
set_option linter.style.multiGoal false)

macro "fct " x:ident " ↦ " y:term : term => `(fun ($x : ℝ) ↦ ($y : ℝ))
macro "suite " i:ident " ↦ " y:term : term => `(fun ($i : ℕ) ↦ ($y : ℝ))

section
open Lean Meta PrettyPrinter Delaborator SubExpr
def delabLamWithTypes (domainTy : Expr) (bodyTy : Expr) (mk : Ident → Term → DelabM Term) : Delab := do
  let checkDefEq (a b : Expr) := do guard <| ← withReducible <| isDefEq a b
  withBindingDomain do checkDefEq domainTy (← getExpr)
  withBindingBodyUnusedName fun x => do
    checkDefEq (← inferType (← getExpr)) bodyTy
    let body ← delab
    mk ⟨x⟩ body

@[delab lam]
def delabFct : Delab := delabLamWithTypes (mkConst ``Real) (mkConst ``Real) fun x y => `(fct $x ↦ $y)

@[delab lam]
def delabSuite : Delab := delabLamWithTypes (mkConst ``Nat) (mkConst ``Real) fun x y => `(suite $x ↦ $y)
end

notation3bis "Prédicat sur " X => X → Prop
notation3bis "Énoncé" => Prop
notation3 "Faux" => False
