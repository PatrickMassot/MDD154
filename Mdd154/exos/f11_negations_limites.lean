import Mdd154.Lib
setup_env

open m154
/-
# Feuille 11 : Négation et limites de suites

Les 4 parties de l'exercice 11.1 sont spéciales : il ne faut rien démontrer !
Vous devez par contre compléter l'énoncé, en n'écrivant que des quantificateurs
sans négation et écrire « tend vers ». Au contraire, vous
devrez utiliser les règles de négation pour les expressions composites
(voir la section 10.3 du cours).
Vérifiez ensuite votre réponse en remplaçant le « sorry » de la démonstration
par `verifie`.

On rappelle la définition de « u tend vers l » :
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε
-/

Exercice "11.1a Négation de « u tend vers l »"
  Données : (u : ℕ → ℝ) (l : ℝ)
  Hypothèses :
  Conclusion : ¬ u tend vers l ⇔
  sorry
Démonstration :
  sorry
QED

Exercice "11.1b Négation de « f est continue en x₀ »"
  Données : (f : ℝ → ℝ) (x₀ : ℝ)
  Hypothèses :
  Conclusion : ¬ (∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ ⇒ |f x - f x₀| ≤ ε) ⇔
  sorry
Démonstration :
  sorry
QED

/-
Dans l'exercice suivant, il est utile de se souvenir que « ∀ x x', ... » est
l'abréviation de « ∀ x, ∀ x', ... ». De même « ∃ x x', ... » est
l'abréviation de « ∃ x, ∃ x', ... ».
-/
Exercice "11.1c Négation de « f est uniformément continue sur ℝ »"
  Données : (f : ℝ → ℝ)
  Hypothèses :
  Conclusion : ¬ (∀ ε > 0, ∃ δ > 0, ∀ x x', |x' - x| ≤ δ ⇒ |f x' - f x| ≤ ε) ⇔
  sorry
Démonstration :
  sorry
QED

Exercice "11.1d Négation de « f est séquentiellement continue en x₀ »"
  Données : (f : ℝ → ℝ) (x₀ : ℝ)
  Hypothèses :
  Conclusion : ¬ (∀ u : ℕ → ℝ, u tend vers x₀ ⇒ (f ∘ u) tend vers (f x₀)) ↔
  sorry
Démonstration :
  sorry
QED

/-
La suite de cette feuille explore des applications élémentaires de la négation
dans l'étude des convergences de suites de réels.

On rappelle que "on conclut que" peut débusquer des contradictions
faciles, comme dans l'exemple suivant.
-/

Exemple "Inégalités et contradiction"
  Données : (a b : ℝ)
  Hypothèses : (h : a < b) (h' : b < a)
  Conclusion : Faux
Démonstration :
  Fait H : a < a car
    Calc a < b par hypothèse
     _     < a par hypothèse
  Comme a < a on conclut que Faux
QED

/-
La variante suivante est également possible.
-/

Exemple "Inégalités et contradiction, une variante"
  Données : (a b : ℝ)
  Hypothèses : (h : a < b) (h' : b < a)
  Conclusion : Faux
Démonstration :
  Il suffit de montrer que a < a
  Calc a < b par hypothèse
    _    < a par hypothèse
QED

/-
Attention : si vous voulez utiliser cette méthode avec des nombres concrets
plutôt que des variables comme `a` ou `b`, il faut aider Lean à comprendre si
vous voulez parler de nombres réels ou d’entiers.

Par exemple, si le but est `Faux`, vous pouvez écire
`Il suffit de montrer que (2 : ℝ) ≤ 1`.

Ou bien écrire

Fait contradictoire : (2 : ℝ) ≤ 1 car
  …
Comme 2 ≤ 1 on conclut que Faux

On rappelle que la base de données de lemmes utilisables implicitement contient
entre autres lemmes :

`∀ x y, |x| ≤ y ↔ -y ≤ x ∧ x ≤ y`

`∀ p q r r ≥ max p q  ↔ r ≥ p ∧ r ≥ q`

`∀ p q, p ≤ max p q`

`∀ p q, q ≤ max p q`

On a aussi la définition, pour tout suite `u` de réels :

`u tend vers +∞` si `∀ A, ∃ N, ∀ n ≥ N, u n ≥ A`.
-/


Exercice "11.2 Si u tend vers +∞ alors u ne tend vers aucune limite finie"
  Données : (u : ℕ → ℝ)
  Hypothèses :
  Conclusion : u tend vers +∞ ⇒ ∀ l, ¬  u tend vers l
Démonstration :
  sorry
QED

Exercice "11.3 Si u est croissante et tend vers l alors tous les u_n sont inférieurs à l."
  Données : (u : ℕ → ℝ) (l : ℝ)
  Hypothèses : (h :  u tend vers l) (h' : u est croissante)
  Conclusion : ∀ n, u n ≤ l
Démonstration :
  sorry
QED

/-
Dans les exercices suivants, « A : Set ℝ » signifie que A est un ensemble de
nombres réels. On a la notation usuelle x ∈ A pour dire qu'un réel x est
dans l'ensemble de réels A.

La notation « ∀ x ∈ A, ...» est l'abréviation de « ∀ x, x ∈ A ⇒ ... »
(analogue à l'abréviation « ∀ ε > 0, ... »).

Étant donné un réel `x` et un ensemble de réels `A`,
`x majore A` signifie `∀ a ∈ A, a ≤ x`.
et
`x est borne sup de A` signifie `x majore A ∧ ∀ y, y majore A ⇒ x ≤ y`

Remarque : on peut montrer facilement qu'un ensemble de réels admet au plus
une borne supérieure, mais ce ne sera pas utile ici.

Attention : on rappelle que le quantificateur universel consomme tout ce qui
ressemble à un énoncé à sa droite, donc il ne faut pas oublier de mettre des
parenthèses. Par exemple, `∀ x, P x ⇒ Q` est toujours lu comme
`∀ x, (P x ⇒ Q)`, pas comme `(∀ x, P x) ⇒ Q`, même si l’absence de `x` dans `Q`
rend la deuxième lecture beaucoup plus vraisemblable sur papier.
-/

Exercice "11.4 Si un réel x est borne supérieure d'un ensemble de réels A alors
  pour tout y, si y < x alors il existe a dans A strictement plus grand que y."
  Données : (A : Set ℝ) (x : ℝ)
  Hypothèses : (hx : x est borne sup de A)
  Conclusion : ∀ y, y < x ⇒ ∃ a ∈ A, y < a
Démonstration :
  sorry
QED

/-
L'exercice suivant est une variante de l'exercice 10.9.
Le but ici est de montrer son application à l'étude des limites de suites
dans le dernier exercice 11.6.

La commande Exercice-lemme assure que cet énoncé sera utilisable implicitement
par les Commande `Comme` ou `Il suffit de montrer que`.
-/

Exercice-lemme inferieur_si_inferieur_plus_eps
  "Soit x et y deux réels. Si y ≤ x + ε pour tout ε > 0 alors y ≤ x."
  Données : (x y : ℝ)
  Hypothèses :
  Conclusion : (∀ ε > 0, y ≤ x + ε) ⇒ y ≤ x
Démonstration :
  sorry
QED

Exercice "11.6 Si u tend vers x et u_n ≤ y pour tout n alors x ≤ y."
  Données : {x y : ℝ} {u : ℕ → ℝ}
  Hypothèses : (hu :  u tend vers x) (ineg : ∀ n, u n ≤ y)
  Conclusion : x ≤ y
Démonstration :
  sorry
QED

