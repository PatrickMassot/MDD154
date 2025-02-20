import Mdd154.LibPgcd
setup_env

namespace m154
open Nat M154
/-
# Feuille 06 : Conjonctions


Étant donnés deux énoncés `P` et `Q`, l'énoncé « `P` et `Q` » (noté `P ∧ Q`) est appelé
la *conjonction* de `P` et `Q` :

`P ∧ Q` est vrai si et seulement si `P` et `Q` sont tous les deux vrais.

## Démonstration d’une conjonction

Pour démontrer une conjonction `P ∧ Q`, il faut démontrer les deux énoncés `P` et `Q`.
Pour cela on utilise la commande `Montrons d'abord que …` pour annoncer le premier but
puis, une fois ce but démontré, `Montrons maintenant que …` (ce sont les mêmes commandes
que pour démontrer les deux implications d’une équivalence).
-/

Exemple "Démonstration de conjonction."
  Données : (a : ℝ)
  Hypothèses : (ha : a > 0)
  Conclusion : a^2 > 0 ∧ |a| > 0
Démonstration :
  Montrons d'abord que a^2 > 0
  Comme a > 0 on conclut que a^2 > 0
  Montrons maintenant que |a| > 0
  Comme a > 0 on obtient H : a ≠ 0
  Comme a ≠ 0 on conclut que |a| > 0
QED

Exercice "06.1 Démonstration de conjonction."
  Données : (a : ℝ)
  Hypothèses : (ha : a > 0)
  Conclusion : 2*a > 0 ∧ (a^2)^2 > 0
Démonstration :
  sorry
QED

/-
Le cours dispose également d’une petite base de données d’énoncés qui
comportent des implications dont la l’hypothèse est une conjonction, ce qui
conduit à devoir démontrer des conjonctions. Ces énoncés peuvent être utilisé
sans justification à l’aide de la commande
`Il suffit de montrer que …`
comme d’habitude avec les implications implicites.

Un exemple de tel énoncé est `∀ x y, (-y ≤ x ∧ x ≤ y) ⇒ |x| ≤ y`.
-/

Exemple "Démonstration d’un énoncé découlant d’une conjonction."
  Données : (a b : ℝ)
  Hypothèses : (h : a - b ≥ -1) (h' : a - b ≤ 1)
  Conclusion : |a - b| ≤ 1
Démonstration :
  Il suffit de montrer que -1 ≤ a - b et a - b ≤ 1
  Montrons d'abord que -1 ≤ a - b
  On conclut par hypothèse
  Montrons maintenant que a - b ≤ 1
  On conclut par hypothèse
QED


/-
## Utilisation d’une conjonction

Pour utiliser qu’une conjonction `P ∧ Q` est vraie on utilise que les énoncés `P` et `Q`
sont tous les deux vrais.

Pour cela on utilise la commande `Comme P ∧ Q on obtient hP : P et hQ : Q` où `hP`
et `hQ` sont des noms au choix, parmi les noms disponibles.
-/

Exemple "Utilisation d’une conjonction"
  Données : (a : ℝ)
  Hypothèses : (h : 0 ≤ a ∧ a ≤ 1)
  Conclusion : a ≤ 2
Démonstration :
  Comme 0 ≤ a ∧ a ≤ 1 on obtient ha : 0 ≤ a et ha' : a ≤ 1
  Comme a ≤ 1 on conclut que a ≤ 2
QED

/-
Dans l’exemple ci-dessus, l’hypothèse `ha` n’est jamais utilisée, on peut
omettre d’en parler.
-/
Exemple "Utilisation d’une partie d’une conjonction"
  Données : (a : ℝ)
  Hypothèses : (h : 0 ≤ a ∧ a ≤ 1)
  Conclusion : a ≤ 2
Démonstration :
  Comme 0 ≤ a ∧ a ≤ 1 on obtient ha' : a ≤ 1
  Comme a ≤ 1 on conclut que a ≤ 2
QED

/-
Par ailleurs la commande `Comme` prend l’initiative de scinder les conjonctions
apparaissant en hypothèse lorsqu’elle cherche les justifications des
énoncés apparaissant entre `Comme` et `on conclut que` ou bien `on obtient` ou bien
`il suffit de montrer que`. On peut donc se contenter de la seconde ligne
dans la démonstration ci-dessus.
-/

Exercice "06.2 Utilisation d’une conjonction"
  Données : (a b : ℝ)
  Hypothèses : (hab : a ≤ b ∧ b ≤ 1)
  Conclusion : a ≤ 1
Démonstration :
  sorry
QED

Exercice "06.3 Utilisation d’une conjonction"
  Données : (a b : ℝ)
  Hypothèses : (hab : 0 ≤ b ∧ a ≤ 1)
  Conclusion : a*b ≤ b
Démonstration :
  sorry
QED

/-
Le cours dispose également d’une petite base de données d’implications ayant une
conjonction comme conclusion. Ces énoncés peuvent être utilisés sans justification.

Un exemple de tel énoncé est `∀ x y, |x| ≤ y ⇒ (-y ≤ x ∧ x ≤ y)`.
-/

Exemple "Utilisation d’un énoncé impliquant une conjonction"
  Données : (a b : ℝ)
  Hypothèses : (ha : |a| ≤ 1)
  Conclusion : a ≤ 2
Démonstration :
  Comme |a| ≤ 1 et |a| ≤ 1 ⇒ -1 ≤ a ∧ a ≤ 1 on obtient ha' : -1 ≤ a et ha'' : a ≤ 1
  Comme a ≤ 1 on conclut que a ≤ 2
QED

/-
En fait on peut même laisser l’implication implicite.
-/

Exemple "Utilisation d’un énoncé impliquant une conjonction,
         en laissant l’implication implicite."
  Données : (a b : ℝ)
  Hypothèses : (ha : |a| ≤ 1)
  Conclusion : a ≤ 2
Démonstration :
  Comme |a| ≤ 1 on obtient ha' : -1 ≤ a et ha'' : a ≤ 1
  Comme a ≤ 1 on conclut que a ≤ 2
QED

/-
Un autre énoncé du même type qui servira très fréquemment dans les feuilles
suivantes est
`∀ x a b, x ≥ max a b ⇒ (x ≥ a ∧ x ≥ b)`.
-/

Exercice "06.4 Utilisation d’un lemme de la base de donnée dont la conclusion
          est une conjonction"
  Données : (x a b : ℝ)
  Hypothèses : (hx : x ≥ max a b) (ha : a ≥ 1)
  Conclusion : x ≥ 1
Démonstration :
  sorry
QED

/-
L’exercice suivant nécessite plus de réflexion. Il fait intervenir la notion
de pgcd de deux entiers naturels et la divisibilité. On rappelle que la
barre de divisibilité n’est pas la barre de la touche 6 sur un clavier azerty mais
un symbole unicode qu’on peut obtenir par `,dvd`.

La commande `On calcule` (et sa cousine la justification `par calcul` dans les `Calc`)
savent que
`∀ a b, pgcd a b ∣ a`
et
`∀ a b, pgcd a b ∣ b`
et aussi
`∀ a, a ∣ a`.

La base de données de lemmes contient l’énoncé
`∀ a b : ℕ, (a ∣ b ∧ b ∣ a) ⇒ a = b`
(notez que cet énoncé est faux pour des entiers relatifs et, pour cette raison,
l’exercice suivant ne fonctionnerait pas avec des entiers relatifs).

Elle contient également l’énoncé
`∀ a b c : ℕ, (c ∣ a ∧ c ∣ b) ⇒ c ∣ pgcd a b`

Ces cinq énoncés suffisent à faire l’exercice.
-/

Exercice "06.5"
  Données : (a b : ℕ)
  Hypothèses :
  Conclusion : a ∣ b ⇔ pgcd a b = a
Démonstration :
  sorry
QED

/-
L’exercice suivant nécessite également une réflexion assez poussée.

On pourra utiliser le lemme de disjonction affirmant que la relation d’ordre sur
les réels est totale :
`∀ x y, x ≤ y ∨ y ≤ x`

et le lemme d’anti-symétrie pour cette relation d’ordre :
`∀ x y, (x ≤ y ∧ y ≤ x) ⇒ x = y`
-/
Exercice "06.6"
  Données : (f : ℝ → ℝ)
  Hypothèses : (h : f est croissante) (h' : ∀ x, f (f x) = x)
  Conclusion : ∀ x, f x = x
Démonstration :
  sorry
QED

