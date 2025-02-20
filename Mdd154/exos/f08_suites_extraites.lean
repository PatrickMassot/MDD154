import Mdd154.Lib
setup_env

open m154
/-
# Feuille 8 : Suites extraites, valeurs d'adhérence et suites de Cauchy.
-/

/-
Cette feuille continue l'étude du chapitre 2 du cours de math 101, en abordant
les suites extraites, les valeurs d'adhérence et les suites de Cauchy.
Il n'y a aucune nouvelle commande Lean à apprendre. Cependant les
exercices sont globalement un peu plus difficiles mathématiquement que dans
la feuille 7. Il est donc inutile de travailler cette feuille si la
feuille 7 n'est pas solidement comprise.

On rappelle des lemmes potentiellement utiles.
Les commandes `Comme` et `Il suffit de montrer que` et la justification
`puisque` des étapes de calcul connaissent le lemme

`∀ x y |x| ≤ y ↔ -y ≤ x ∧ x ≤ y`

La commande `On calcule` et la justification `par calcul` connaissent les lemmes
`∀ x y, |x + y| ≤ |x| + |y|`

`∀ x y z, |x - y| ≤ |x - z| + |z - y|`

`∀ x y, |x - y| = |y - x|`

`∀ p q r, r ≥ max p q  ⇒ r ≥ p ∧ r ≥ q`

`∀ p q, max p q ≥ p`

`∀ p q, max p q ≥ q`
-/

/- On rappelle aussi la définition :

`u tend vers l : ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε`

Étant donnée une fonction `φ : ℕ → ℕ`, on dit que
`φ est une extraction` si elle est strictement croissante :
∀ n m, n < m → φ n < φ m

Les commandes `Comme` et `Il suffit de montrer que` et la justification
`puisque` des étapes de calcul connaissent le lemme
suivant (sa démonstration est une récurrence immédiate).

`φ est une extraction ⇒ ∀ n, n ≤ φ n`

ainsi que le résultat

`u tend vers l ∧ u tend vers l' ⇒ l = l'`

démontré dans la feuille précédente.

Pour l'exercice suivant, il est également utile de se souvenir que la notation
`∃ n ≥ N, P n` est l'abréviation de `∃ n, n ≥ N ∧ P n`.
-/

Exercice-lemme extraction_superieur "08.1 Si `φ` est une extraction alors elle prend des valeurs
 arbitrairement grandes pour des indices arbitrairement grands."
  Données : {φ : ℕ → ℕ}
  Hypothèses : (h : φ est une extraction)
  Conclusion : ∀ N N', ∃ n ≥ N', φ n ≥ N
Démonstration :
  sorry
QED

/-
L'exercice précédent est un exercice-lemme, de sorte qu'il vous sera possible
de l'invoquer implicitement dans les démonstrations suivantes.

Un réel `a` est valeur d'adhérence d'une suite `u` s'il
existe une suite extraite de `u` qui tend vers `a` :

`a est valeur d'adhérence de u : ∃ φ, φ est une extraction ∧ (u ∘ φ) tend vers a'
-/

Exercice-lemme valeur_proche_adherence
  "08.2 Si `a` est valeur d'adhérence de `u` alors il existe des valeurs
  de `u` aussi proches qu'on veut de `a` pour des indices aussi grands qu'on veut."
  Données : {u : ℕ → ℝ} {a : ℝ}
  Hypothèses : (hyp : a est valeur d'adhérence de u)
  Conclusion : ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε
Démonstration :
  sorry
QED

Exercice-lemme limite_extraction_si_limite
  "08.3 Si `u` tend vers `l` alors toutes ses suites extraites tendent vers `l`."
  Données : {u : ℕ → ℝ} {φ : ℕ → ℕ} {l : ℝ}
  Hypothèses : (h : u tend vers l) (hφ : φ est une extraction)
  Conclusion :  u ∘ φ tend vers l
Démonstration :
  sorry
QED

Exercice-lemme val_adh_lim
  "08.4 Si une suite `u` tend vers `l` alors elle n'a pas d'autre valeur d'adhérence que `l`."
  Données : {u : ℕ → ℝ} {l a : ℝ}
  Hypothèses : (hl : u tend vers l) (ha : a est valeur d'adhérence de u)
  Conclusion : a = l
Démonstration :
  sorry
QED

/-
Une suite `u` est de Cauchy si ses termes sont aussi proches qu'on
veut pour des indices assez grands :

`u est de Cauchy : ∀ ε > 0, ∃ N, ∀ p ≥ N, ∀ q ≥ N, |u p - u q| ≤ ε`
-/

Exercice-lemme cauchy_si_converge "08.5 Si une suite `u` converge alors elle est de Cauchy."
  Données : {u : ℕ → ℝ}
  Hypothèses :
  Conclusion : (∃ l, u tend vers l) → u est de Cauchy
Démonstration :
  sorry
QED

/- Dans l'exercice suivant, on pourra utiliser l’énoncé démontré plus haut :

`a est valeur d'adhérence de u ⇒ ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε`
-/

Exercice "08.6
  Si une suite de Cauchy `u` admet une valeur d'adhérence `l` alors elle converge vers `l`."
  Données : (u : ℕ → ℝ) (l : ℝ)
  Hypothèses : (hu : u est de Cauchy) (hl :  l est valeur d'adhérence de u)
  Conclusion : u tend vers l
Démonstration :
  sorry
QED

