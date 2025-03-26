import Mdd154.LibNeg
setup_env

open m154
/-
# Feuille 9 : Négations

## L’énoncé `Faux`

Cette feuille aborde l’étude de la négation. La grande nouveauté est
l’introduction d’un énoncé noté `Faux` qui représente une contradiction
mathématique. Le principe fondamental qui régit cet énoncé est la règle

« Pour tout énoncé P, Faux ⇒ P »

appellée principe d’explosion ou par son nom traditionnel « ex falso quodlibet »
(de faux, on déduit tout ce que l’on veut).
-/

Exemple "Si Faux alors 0 = 1"
  Données :
  Hypothèses :
  Conclusion : Faux ⇒ 0 = 1
Démonstration :
  Supposons h : Faux
  Comme Faux on conclut que 0 = 1
QED

-- De Faux, on peut aussi déduire des choses vraies.

Exemple "Si Faux alors 0 = 0"
  Données :
  Hypothèses :
  Conclusion : Faux ⇒ 0 = 0
Démonstration :
  Supposons h : Faux
  Comme Faux on conclut que 0 = 0
QED

/-
Pour insister sur le fait que *tout* découle de Faux, on peut explicitement
faire disparaître le but avec `Montrons une contradiction` (il faut être
vraiment sûr que les hypothèses courantes sont contradictoires).

L’exemple suivant illustre également le fait que la bibliothèque du cours sait
reconnaître un certain nombre d’énoncés faux, comme par exemple `1 > 2`.
-/
Exemple "À partir d’hypothèses contradictoires, on peut démontrer tout énoncé."
  Données : (x : ℝ) (P : Énoncé)
  Hypothèses : (hx : x = 1) (hx' : x > 2)
  Conclusion : P
Démonstration :
  -- On veut montrer P. Ex falso quodlibet, donc il suffit de montrer Faux.
  Montrons une contradiction
  Comme x = 1 et x > 2 on obtient H : 1 > 2
  Comme 1 > 2 on conclut que Faux
QED

Exercice "9.01 À partir d’hypothèses contradictoires, on peut démontrer tout énoncé."
  Données : (x : ℝ) (P : Énoncé)
  Hypothèses : (hx : x < 0) (hx' : x > 0)
  Conclusion : P
Démonstration :
  sorry
QED

/-
Dans l’exemple précédent, Lean déduit Faux d’une inégalité numérique fausse.
La base de données de faits du cours contient aussi l’incompatibilité de certains faits,
autrement dit des implications de la forme `(P ∧ Q) ⇒ Faux`.
Par exemple le fait qu’un entier ne peut pas être à la fois pair et impair.
-/

Exercice "9.02 Si un entier est pair et impair alors 0 = 1."
  Données : (n : ℤ)
  Hypothèses : (h_pair : n est pair) (h_impair : n est impair)
  Conclusion : 0 = 1
Démonstration :
  sorry
QED

/-
Dans ce cas le `Montrons une contradiction` est indispensable pour que la conclusion
attendue doit bien `Faux`. On ne peut pas retirer la première ligne et écrire
`Comme n est pair et n est impair on conclut que 0 = 1`.

## La négation

L’énoncé Faux est utilisé pour définir la négation. Par définition, la négation
d’un énoncé `P` est l’énoncé `P ⇒ Faux`, noté en général `¬ P`. On peut lire
`¬ P` comme « P est faux » (on reviendra sur ce point plus loin).

En particulier, pour démontrer de façon directe un énoncé de la forme `¬ P`, il
faut supposer `P` et montrer `Faux`. Voyons, en exemple, sachant que le symbole `≠`
est, par définition, la négation de `=`.
-/

Exemple "Démonstration d’une négation"
  Données : (x : ℕ)
  Hypothèses : (hyp : x^3 + x^2 - x + 3 = 0)
  Conclusion : x ≠ 1
Démonstration :
  Supposons hyp' : x = 1
  Montrons que Faux -- cette ligne est optionelle mais clarifie
  Il suffit de montrer que 0 = 4
  Calc
    0 = x^3 + x^2 - x + 3 par hypothèse
    _ = 1^3 + 1^2 - 1 + 3 puisque x = 1
    _ = 4                 par calcul
QED

Exercice "9.03 Démonstration d’une négation"
  Données : (x : ℕ)
  Hypothèses : (hyp : x^4 + 2*x^2 + x - 2 = 0)
  Conclusion : x ≠ 1
Démonstration :
  sorry
QED

/-
Voici maintenant l’exemple le plus célèbre de négation en mathématique :
`¬ ∃ x ∈ ℚ, x^2 = 2`
qui est souvent énoncé comme `¬ √2 ∈ ℚ`, mais l’écriture ci-dessus a l’avantage
de rester entièrement dans le monde des nombres rationnels.

Pour simplifier un tout petit peu l’exercice, nous allons démontrer l’énoncé
équivalent portant uniquement sur une paire d’entiers relatifs (qui seraient le
numérateur et le dénominateur d’une fraction de carré 2) :

`¬ ∃ p q : ℤ, p^2 = 2*q^2 ∧ q ≠ 0`.

Il y a plusieurs façons de montrer cet énoncé, selon qu’on suppose connu plus
ou moins d’arithmétique. Ici on suppose connu le théorème fondamental de l’arithmétique :
tout entier admet une unique décomposition en produit de facteurs premiers. En particulier
il existe une fonction `v₂ : ℤ → ℕ` telle que, pour tout entier `p`,
`p = 2^(v₂ p) * m` avec `m` impair. Ainsi `v₂ p` est l’exposant de 2 dans la
décomposition en produit de facteurs premiers de `p` (la lettre « v » est l’initiale du mot
« valuation »).

Dans l’exercice suivant il suffira d’utiliser que la bibliothèque du cours connait
les résultats suivants :

`∀ n : ℤ, v₂ (n^2) est pair`

`∀ n : ℤ, n ≠ 0 ⇒ v₂ (2*n) = v₂ n + 1`

`∀ n : ℤ, n ≠ 0 ⇒ n^2 ≠ 0`

On notera que dans cet exercice, les faits de la forme `x ≠ 0` interviendront
de façon « atomique » : le fait que `≠` soit défini via une négation n’interviendra pas.
-/

Exercice "9.04 Irrationalité de √2"
  Données : (p q : ℤ)
  Hypothèses : (hq : q ≠ 0)
  Conclusion : p^2 ≠ 2*q^2
Démonstration :
  sorry
QED

/-
Voyons maintenant comment *utiliser* une négation.

L’exemple suivant est rédigé de façon un peu lourde pour bien montrer le
mécanisme d’utilisation de la négation.
-/


Exemple "Utilisation d’une négation"
  Données : (x : ℝ)
  Hypothèses : (h : x ≠ 0) (h' : x*(x - 1) = 0)
  Conclusion : x = 1
Démonstration :
  Comme x*(x - 1) = 0 on obtient H : x = 0 ∨ x - 1 = 0
  On discute selon que x = 0 ou x - 1 = 0
  Supposons H : x = 0
  Montrons une contradiction
  Comme x = 0 et x ≠ 0 on conclut que Faux
  Supposons H : x - 1 = 0
  Comme x - 1 = 0 on conclut que x = 1
QED

/-
La partie un peu lourde est la discussion des deux cas alors qu’on sait déjà
qu’un des cas est impossible. On peut l’abréger en :
```
  Comme x*(x - 1) = 0 on obtient H : x = 0 ∨ x - 1 = 0
  Comme x = 0 ∨ x - 1 = 0 et x ≠ 0 on obtient H' : x - 1 = 0
```

Beaucoup plus souvent, une hypothèse qui est une négation est utilisée pour
démontrer un but qui est également une négation.
-/

Exemple "Deux réels inférieurs ou égaux et non égaux ne sont pas supérieurs ou égaux"
  Données : (x y : ℝ)
  Hypothèses : (h1 : x ≤ y) (h2 : x ≠ y)
  Conclusion : ¬ y ≤ x
Démonstration :
  Supposons h' : y ≤ x
  Comme y ≤ x et x ≤ y on obtient h3 : x = y
  Comme x = y et x ≠ y on conclut que Faux
QED

/-
La dernière ligne de l’exemple précédent est un exemple d’un fait beaucoup plus général
et important : la définition de la négation permet de montrer immédiatement
que, pour tout énoncé `P`, si `P` est vrai alors il n’est pas faux.
-/

Exercice "9.05 Si un énoncé `P` est vrai alors il n’est pas faux."
  Données : (P : Énoncé)
  Hypothèses : (h : P)
  Conclusion : ¬ (¬ P)
Démonstration :
  sorry
QED

/-

Pour les enthousiastes de la logique, voici un autre exercice sur la définition
de la négation. Vous pouvez passer cet exercice si la logique pure vous effraie
ou si vous êtes en retard sur le reste du groupe.
-/

Exercice "9.06 Si un énoncé implique sa négation alors il est faux."
  Données : (P : Prop)
  Hypothèses : (h : P ⇒ ¬ P)
  Conclusion : ¬ P
Démonstration :
  sorry
QED

/-
Une autre remarque théorique importante est que la définition de la négation
et le principe d’explosion assurent que, pour tout énoncé `P`, la négation de `P`
est vraie si et seulement si `P` est équivalent à `Faux`. C’est la raison pour laquelle
on peut lire `¬ P` comme « `P` est faux ».

Vous pouvez passer cet exercice si la logique pure vous fait peur ou si vous êtes un peu
en retard sur le reste du groupe. La démonstration est plus longue que celle de
l’exercice précédent mais pas fondamentalement plus compliquée.
-/

Exercice "9.07 Un énoncé P est faux si et seulement si il est équivalent à Faux."
  Données : (P : Énoncé)
  Hypothèses :
  Conclusion : (¬ P) ⇔ (P ⇔ Faux)
Démonstration :
  sorry
QED


