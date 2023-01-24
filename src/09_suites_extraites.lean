import lib.m154 

open m154
namespace f06
/-
Cette feuille continue l'étude du chapitre 2 du cours de math 101, en abordant
les suites extraites, les valeurs d'adhérence et les suites de Cauchy.
Il n'y a aucun nouvelle commande Lean à apprendre. Cependant les
exercices sont globalement un peu plus difficiles mathématiquement que dans
la feuille 8. Il est donc inutile de travailler cette feuille si la
feuille 8 n'est pas solidement comprise.

On rappelle des lemmes potentiellement utiles :

`abs_inferieur_ssi (x y : ℝ) : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y`

`abs_plus (x y : ℝ) : |x + y| ≤ |x| + |y|`

`ineg_triangle (x y z : ℝ) : |x - y| ≤ |x - z| + |z - y|`

`abs_diff (x y : ℝ) : |x - y| = |y - x|`

`superieur_max_ssi (p q r) : r ≥ max p q  ↔ r ≥ p ∧ r ≥ q`

`inferieur_max_gauche p q : p ≤ max p q`

`inferieur_max_droite p q : q ≤ max p q`
-/

lemma demi_pos { ε : ℝ } : ε > 0 → ε/2 > 0 :=
begin
  Supposons hyp,
  On conclut par hyp,
end

/- On rappelle aussi la définition de « u tend vers l » -/

/-- `limite_suite u l` signifie que la suite `u` tend vers `l` -/
def limite_suite (u : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

/-
On a démontré dans la feuille 5 l'unicité de la limite d'une suite convergente :

`unicite_limite : limite_suite u l → limite_suite u l' → l = l'`
-/

/-- Une fonction `φ : ℕ → ℕ` est une extraction si elle est
strictement croissante. -/
def extraction (φ : ℕ → ℕ) := ∀ n m, n < m → φ n < φ m

-- Dans la suite, φ désignera toujours une fonction de ℕ dans ℕ
variable { φ : ℕ → ℕ}

/-
On pourra utiliser le lemme suivant dont la démonstration est une récurrence
immédiate (mais nous n'avons pas encore vu comment faire des démonstrations
par récurrence avec Lean).

`extraction_superieur_id : extraction φ → ∀ n, n ≤ φ n`

Pour l'exercice suivant, il est utile de se souvenir que la notation
`∃ n ≥ N, P n` est l'abréviation de `∃ n, n ≥ N ∧ P n`.
-/

/-- Si `φ` est une extraction alors elle prend des valeurs
 arbitrairement grandes pour des indices arbitrairement grands. -/
lemma extraction_superieur : extraction φ → ∀ N N', ∃ n ≥ N', φ n ≥ N :=
begin
  sorry
end

/-- Un réel `a` est valeur d'adhérence d'une suite `u` s'il
existe une suite extraite de `u` qui tend vers `a`. -/
def valeur_adherence (u : ℕ → ℝ) (a : ℝ) :=
∃ φ, extraction φ ∧ limite_suite (u ∘ φ) a

-- Dans la suite u désigne une suite de réels, et a et l sont des réels
variables {u : ℕ → ℝ} {a l : ℝ}

/-- Si `a` est valeur d'adhérence de `u` alors il existe des valeurs
de `u` aussi proche qu'on veut de `a` pour des indices aussi grands qu'on veut. -/
lemma valeur_proche_adherence :
  valeur_adherence u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε :=
begin
  sorry
end

/-- Si `u` tend vers `l` alors toutes ses suites extraites tendent vers `l`. -/
lemma limite_extraction_si_limite (h : limite_suite u l) (hφ : extraction φ) :
limite_suite (u ∘ φ) l :=
begin
  sorry
end

/-- Si une suite `u` qui tend vers `l` alors elle n'a pas d'autre valeur
d'adhérence que `l`. -/
lemma val_adh_lim (hl : limite_suite u l) (ha : valeur_adherence u a) : a = l :=
begin
  sorry
end

/-- Une suite `u` est de Cauchy si ses termes sont aussi proches qu'on
veut pour des indices assez grands. -/
def suite_cauchy (u : ℕ → ℝ) := ∀ ε > 0, ∃ N, ∀ p ≥ N, ∀ q ≥ N, |u p - u q| ≤ ε

/-- Si une suite `u` converge alors elle est de Cauchy. -/
lemma cauchy_si_converge : (∃ l, limite_suite u l) → suite_cauchy u :=
begin
  sorry
end


/- Dans l'exercice suivant, on pourra utiliser valeur_proche_adherence
  démontré plus haut et dont on rappelle l'énoncé :

`valeur_proche_adherence : valeur_adherence u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε`
-/

/-- Si une suite de Cauchy `u` admet une valeur d'adhérence `l` alors elle
converge vers `l`. -/
example (hu : suite_cauchy u) (hl : valeur_adherence u l) : limite_suite u l :=
begin
  sorry
end

end f06
