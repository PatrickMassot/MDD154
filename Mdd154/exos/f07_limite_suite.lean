import Mdd154.Lib
setup_env

/-
# Feuille 7 : Suites convergentes.
-/

/-
Une suite u est une fonction de ℕ dans ℝ, Lean écrit donc u : ℕ → ℝ

`u tend vers l` signifie `∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε`

Il faut bien garder à l’esprit que `∀ ε > 0, …` est l’abbréviation de
`∀ ε, ε > 0 ⇒ …`.

Pour démontrer un énoncé qui commence ainsi, la commande `Soit` permet
d’utiliser l’abbréviation
`Soit ε > 0`
à la place de la suite de commandes
`Soit ε : ℝ`
`Supposons ε_pos : ε > 0`.

Pour utiliser un énoncé qui commence ainsi, il faut donner à la commande
`Comme` l’énoncé et le fait que le nombre auquel on veut spécialiser l’énoncé est
strictement positif.

Voyons un exemple artificiel.
-/

Exemple "Énoncé commençant par ∀ ε > 0"
  Données : (u : ℕ → ℝ)
  Hypothèses : (hu : ∀ δ > 0, ∃ n, u n < δ)
  Conclusion :  ∀ ε > 0, ∃ n, u n < ε/2
Démonstration :
  Soit ε > 0
  Comme ∀ δ > 0, ∃ n, u n < δ et ε/2 > 0 on conclut que ∃ n, u n < ε/2
QED

/-
Dans l’exemple ci-dessus, on notera que l’utilisation de la lettre `δ`
dans l’hypothèse et `ε` dans la conclusion permet de clarifier les choses,
car on peut dire qu’on a « spécialisé l’hypothèse à `δ = ε/2` ».
Mais `ε` et `δ` sont des variables liées donc on peut nommer les deux `ε` sans
rien changer.

Voyons maintenant un exemple qui utilise la définition de limite.
-/

Exemple "Un exemple pour démarrer"
  Données : (u v : ℕ → ℝ) (l : ℝ)
  Hypothèses : (hu : u tend vers l) (hv : ∀ n, v n = u n - l)
  Conclusion : v tend vers 0
Démonstration :
  Soit ε > 0
  Comme u tend vers l et ε > 0 on obtient N₁ tel que hN₁ : ∀ n ≥ N₁, |u n - l| ≤ ε
  Montrons que N₁ convient
  Soit N ≥ N₁
  Comme ∀ n ≥ N₁, |u n - l| ≤ ε et N ≥ N₁ on obtient hN₁' : |u N - l| ≤ ε
  Calc
    |v N - 0| = |u N - l - 0| puisque ∀ n, v n = u n - l
    _         = |u N - l|     par calcul
    _         ≤ ε             par hypothèse
QED

Exercice "07.1 Si u est constante de valeur l, alors u tend vers l"
  Données : (u : ℕ → ℝ) (l : ℝ)
  Hypothèses :
  Conclusion : (∀ n, u n = l) ⇒ u tend vers l
Démonstration :
  sorry
QED

/- Concernant les valeurs absolues, la base de données de résultats utilisables sans
les mentionner explicitement inclut

`∀ x y, |x + y| ≤ |x| + |y|`

`∀ x y z, |x - y| ≤ |x - z| + |z - y|`

`∀ x y, |x - y| = |y - x|`

Ces trois résultats sont utilisés par la commande `On calcule`
(ou `par calcul` dans les `Calc`).

Les commandes `Comme …` et `Il suffit de montrer que …` savent que
`∀ x y, |x| ≤ y ⇔ -y ≤ x et x ≤ y`

Il est conseillé de noter ces lemmes sur une feuille car ils
peuvent être utiles dans chaque exercice.
-/

Exercice "07.2 Si u tend vers l strictement positif, alors u n ≥ l/2 pour n assez grand."
  Données : (u : ℕ → ℝ) (l : ℝ)
  Hypothèses : (hl : l > 0)
  Conclusion : (u tend vers l) ⇒ ∃ N, ∀ n ≥ N, u n ≥ l/2
Démonstration :
  sorry
QED

/-
La base de données de résultats contient également des résultats
concernant le maximum de deux nombres

`∀ p q, p ≤ max p q`

`∀ p q, q ≤ max p q`

Il est conseillé de noter ces lemmes sur une feuille car ils
peuvent être utiles dans chaque exercice.
-/

Exercice "07.3 Si u tend vers l et v tend vers l' alors u+v tend vers l+l'"
  Données : (u v : ℕ → ℝ) (l l' : ℝ)
  Hypothèses : (hu : u tend vers l) (hv : v tend vers l')
  Conclusion : (u + v) tend vers (l + l')
Démonstration :
  sorry
QED

Exercice "07.4 théorème des gendarmes"
  Données : (u v w : ℕ → ℝ) (l : ℝ)
  Hypothèses : (hu : u tend vers l) (hw : w tend vers l)
               (h : ∀ n, u n ≤ v n) (h' : ∀ n, v n ≤ w n)
  Conclusion : v tend vers l
Démonstration :
  sorry
QED

Exercice "07.5 La dernière inégalité dans la définition de limite peut être remplacée par
          une inégalité stricte."
  Données : (u : ℕ → ℝ) (l : ℝ)
  Hypothèses :
  Conclusion : (u tend vers l) ⇔ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε
Démonstration :
  sorry
QED

/-
Dans l’exercice suivant on pourra utiliser que la commande
`Il suffit de montrer que`
connait le lemme
`∀ x y : ℝ, (∀ ε > 0, |x - y| ≤ ε) ⇒ x = y`

et la commande `Comme` connait les lemmes
`∀ a b, max a b ≥ a`
et
`∀ a b, max a b ≥ b`
-/


Exercice "07.6 Une suite u admet au plus une limite"
  Données : (u : ℕ → ℝ) (l l' : ℝ)
  Hypothèses : (hl : u tend vers l) (hl' : u tend vers l')
  Conclusion : l = l'
Démonstration :
  sorry
QED

/-
`M est borne sup de u` signifie
  (∀ n, u n ≤ M) ∧ (∀ ε > 0, ∃ n₀, u n₀ ≥ M - ε)
-/
Exercice "07.7 Toute suite croissante ayant une borne supérieure tend vers cette borne"
  Données : (u : ℕ → ℝ) (M : ℝ)
  Hypothèses : (h : M est borne sup de u) (h' : u est croissante)
  Conclusion : u tend vers M
Démonstration :
  sorry
QED

