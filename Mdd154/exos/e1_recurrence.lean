import Mdd154.LibRec

setup_env

/-
# Exercices supplémentaires 1 : Démonstrations par récurrence.
-/

/-
La commande `Montrons par récurrence que ∀ (n : ℕ), P n` permet
de démontrer par récurrence la propriété `∀ (n : ℕ), P n`, puis
de l'ajouter au contexte local (ou démontrer le but courant si possible).
Cette commande crée 2 nouveaux buts :
1) l'initialisation de la récurrence, c'est-à-dire `P 0`
2) le pas inductif, c'est-à-dire `∀ (n : ℕ), P n ⇒ P (n+1)`.
-/

Exemple "Une inégalité assez simple pour commencer"
  Données : (n : ℕ)
  Hypothèses :
  Conclusion : 2^n > n
Démonstration :
  Montrons par récurrence que ∀ (n : ℕ), 2^n > n
  · Montrons que 2 ^ 0 > 0
    On calcule
  · Montrons que ∀ n, 2 ^ n > n ⇒ 2 ^ (n + 1) > n + 1
    Soit k : ℕ
    Supposons que 2 ^ k > k
    Calc
    2^(k+1) = 2 * 2^k   par calcul
        _   > 2 * k + 1 puisque 2^k > k
        _   ≥ k + 1     par calcul
QED

Exercice "E.1 Toute suite géométrique s'écrit sous la forme v n = a * b^n."
  Données :  (v : ℕ → ℝ) (k : ℝ)
  Hypothèses : (h : ∀ n, v (n + 1) = k * v n)
  Conclusion : ∃ a b, ∀ n, v n = a * b^n
Démonstration :
  sorry
QED


/-
  Pour démontrer par récurrence une proposition P(n) pour tout naturel n ≥ n₀,
  on utilise que la base de données de lemmes contient
  `∀ n m, n ≤ m ⇒ ∃ k, m = n + k`
  (ainsi que la variante avec `k + n`) et ensuite faire une récurrence sur `k`.
-/

Exemple "Récurrence à partir de n = 5"
  Données : (n : ℕ)
  Hypothèses : (h : n ≥ 5)
  Conclusion : 2^n ≥ 5 * n
Démonstration :
  Comme n ≥ 5 on obtient m tel que n = m + 5
  Comme n = m + 5 il suffit de montrer que 2 ^ (m + 5) ≥ 5 * (m + 5)
  Montrons par récurrence que ∀ (k : ℕ), 2^(k + 5) ≥ 5*(k + 5)
  · Montrons que 2 ^ (0 + 5) ≥ 5 * (0 + 5)
    On calcule
  · Montrons que ∀ k : ℕ, 2 ^ (k + 5) ≥ 5 * (k + 5) ⇒ 2 ^ ((k + (5 + 1))) ≥ 5 * ((k + (5 + 1)))
    Soit k
    Supposons que 2 ^ (k + 5) ≥ 5 * (k + 5)
    Calc
      2^(k + 5+1) = 2*2^(k + 5) par calcul
         _    ≥ 2*(5*(k + 5)) puisque 2 ^ (k + 5) ≥ 5 * (k + 5)
         _    = 5*(k + 5 + 1 + k + 4) par calcul
         _    ≥ 5*(k + 5 + 1) par calcul
QED

Exercice "E.2 À vous de jouer avec cette nouvelle technique."
  Données : (n : ℕ)
  Hypothèses : (h : n ≥ 6)
  Conclusion : 2^n ≥ 6 * n + 7
Démonstration :
  sorry
QED

Exercice "E.3 Formule pour une suite définie par récurrence."
  Données : (u : ℕ → ℝ)
  Hypothèses : (h : ∀ n : ℕ, u (n+1) = 2 * u n + 1) (h' : u 0 = 0)
  Conclusion : ∀ n : ℕ, u n = 2^n - 1
Démonstration :
  sorry
QED

/-
On rappelle la définition d'extraction : pour `φ : ℕ → ℕ`,
l’énoncé `φ est une extraction` signifie que
`∀ n m, n < m ⇒ φ n < φ m`.
-/

Exercice "E.4 Toute extraction est supérieure à Id"
  Données : (φ : ℕ → ℕ)
  Hypothèses : (h : φ est une extraction)
  Conclusion : ∀ n, n ≤ φ n
Démonstration :
  sorry
QED

Exercice "E.5 Une suite est croissante si et seulement si elle augmente à chaque pas."
  Données : (u : ℕ → ℝ)
  Hypothèses :
  Conclusion : u est croissante ⇔ ∀ n, u n ≤ u (n+1)
Démonstration :
  sorry
QED

/-
La base de données de lemme contient en fait l’implication qui n’est pas
évidente : `(∀ n, u (n + 1) ≥ u n) ⇒ u est croissante`. On pourra l’utiliser
dans l’exercice suivant.

Pour tout réel u₀, `suite_rec f u₀` est la suite `u` définie par récurrence
au moyen des relations `u 0 = u₀` et `u (n+1) = f(u n)` pour tout naturel `n`.
Ces deux relations sont vraies par définition. En particulier la commande
`On calcule` ou la justification `par calcul` dans `Calc` connaissent ces relations.
-/

Exercice "E.6 Une suite définie par récurrence au moyen d'une fonction
               croissante est elle-même croissante."
  Données : (f : ℝ → ℝ) (u₀ : ℝ)
  Hypothèses : (hyp : u₀ ≤ f u₀) (hf : f est croissante)
  Conclusion : suite_rec f u₀ est croissante
Démonstration :
  sorry
QED


Exercice "E.7 Inégalité entre suites définies par récurrence."
  Données : (g : ℝ → ℝ)
  Hypothèses : (hg : g est croissante) (hfg : ∀ x, f x ≤ g x) (u₀ : ℝ)
  Conclusion : ∀ n, (suite_rec f u₀) n ≤ (suite_rec g u₀) n
Démonstration :
  sorry
QED


