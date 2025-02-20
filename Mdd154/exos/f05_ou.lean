import Mdd154.Lib
setup_env

/-
# Feuille 05 : Disjonctions
-/

/-
À partir de deux énoncés `P` et `Q`, on peut former l’énoncé `P v Q` qui se lit
« P ou Q ».

Pour démontrer directement un énoncé de cette forme il faut démontrer `P` ou bien
démontrer `Q`.
Pour cela on utilise la commande `Montrons que` (c’est la même syntaxe que
lorsqu’on veut simplement faciliter la lecture en rappelant le but courant).
-/
Exemple "Premier exemple de disjonction."
  Données :
  Hypothèses :
  Conclusion : 2^3 = 3 ∨ 2^3 = 8
Démonstration :
  Montrons que 2^3 = 8
  On calcule
QED

/-
On notera qu’une telle démonstration nécessite une action courageuse et
irréversible. Annoncer la mauvaise démonstration peut conduire à une impasse.
Ainsi dans la démonstration ci-dessus, commencer par
`Montrons que 2^3 = 3`
est une manœuvre logiquement valide mais qui conduit à une impasse.
-/

Exercice "05.1"
  Données :
  Hypothèses :
  Conclusion : 1 + 1 = 2 ∨ 1 + 3 = 17
Démonstration :
  sorry
QED

/-
Pour utiliser une hypothèse de la forme `P v Q` afin de démontrer un but `R`, on
fait ce qu’on appelle une disjonction de cas. La démonstration se scinde en
deux branches, l’une dans laquelle on suppose `P` et on démontre `R` (il s’agit
donc de démontrer `P ⇒ R`) et l’autre dans laquelle on suppose `Q` et on
démontre `R` (il s’agit donc de démontrer `Q ⇒ R`). On notera que le but est le
même dans les deux branches : c’est le but de départ `R`.

Pour faire cela, on utilise la commande
`On discute selon que P ou Q`.
Cette commande vérifie que la disjonction `P v Q` est connue puis opère la disjonction
de cas.
-/
Exemple "Disjonction de cas"
  Données : (a : ℝ)
  Hypothèses : (h : a = 2 ∨ a = -2)
  Conclusion : a^2 = 4
Démonstration :
  On discute selon que a = 2 ou a = -2
  Supposons ha : a = 2
  Calc
    a^2 = 2^2 puisque a = 2
    _   = 4   par calcul
  Supposons ha : a = -2
  Calc
    a^2 = (-2)^2 puisque a = -2
    _   = 4      par calcul
QED

Exercice "05.2 Disjonction de cas"
  Données : (a : ℝ)
  Hypothèses : (h : a = 2 ∨ a = -3)
  Conclusion : a^2 + a = 6
Démonstration :
  sorry
QED

/-
Dans les exemples précédents, l’énoncé faisant intervenir une disjonction était une
hypothèse locale. Le cours dispose également d’une base de données de résultats
dont la conclusion est une disjonction. Par exemple

`∀ x y : ℝ, x * y = 0 ⇒ x = 0 v y = 0`.

Comme sur papier, on peut invoquer implicitement ces résultats (qui seront
mentionnés en temps utiles avant les exercices).
Lean cherchera automatiquement la prémisse `x * y = 0` parmi les hypothèses.
-/

Exemple "Utilisation implicite d’une disjonction."
  Données : (x : ℝ)
  Hypothèses : (hx : (x - 1) * (x + 1) = 0)
  Conclusion : x^2 = 1
Démonstration :
  On discute selon que x - 1 = 0 ou x + 1 = 0
  Supposons h : x - 1 = 0
  Montrons que x^2 = 1 -- cette ligne est optionnelle mais facilite la lecture
  Calc
    x^2 = 1^2 puisque x = 1
    _   = 1 par calcul
  Supposons h : x + 1 = 0
  Montrons que x^2 = 1 -- cette ligne est optionnelle mais facilite la lecture
  Calc
    x^2 = (-1)^2 puisque x = -1
    _   = 1 par calcul
QED

/-
Voyons maintenant des exemples qui successivement utilisent et démontrent
une disjonction. L'utilisation d'une disjonction crée un embranchement
dans la démonstration et la décision stratégique pour démontrer la disjonction
but dépend de la branche courante.

On en profite pour faire connaissance avec la commande
`Fait nom : … car`
qui introduit une nouvelle affirmation sans lien direct avec le but
courant. Après démonstration dans un bloc de commandes indenté, ce fait
devient disponible pour la démonstration du but courant, avec le nom donné.
-/

Exemple "Une disjonction montrée après dijonction de cas."
  Données : (a b : ℝ)
  Hypothèses :
  Conclusion : a = a*b ⇒ a = 0 ∨ b = 1
Démonstration :
  Supposons hyp : a = a*b
  -- À ce stade, il faut démontrer que a = 0 ou b = 1
  -- Mais il est impossible de trancher entre ces deux options.
  -- Il faut exploiter les hypothèses et faire une disjonction de cas.
  Fait H : a*(1 - b) = 0 car
    -- Dans ce bloc de code, il faut démontrer que a*(1 - b) = 0
    Calc a*(1 - b) = a - a*b par calcul
         _         = 0       puisque a = a*b
  -- Nous disposons maintenant du fait `H : a * (1 - b) = 0`
  -- prêt à être utilisé par `On discute`
  On discute selon que a = 0 ou 1 - b = 0
  Supposons h : a = 0
  -- On peut maintenant décider quel côté de la disjonction
  -- démontrer
  Montrons que a = 0 -- cette ligne est une décision irréversible
  On conclut par hypothèse
  Supposons h : 1 - b = 0
  -- Dans ce cas, nous décidons de démontrer l’autre conclusion possible.
  Montrons que b = 1 -- cette ligne est une décision irréversible
  Comme 1 - b = 0 on conclut que b = 1
QED

Exercice "05.3 Démonstration d’une disjonction en utilisant une disjonction"
  Données : (x y : ℝ)
  Hypothèses :
  Conclusion : x^2 = y^2 ⇒ x = y ∨ x = -y
Démonstration :
  sorry
QED

/-
L’exercice suivant utilise les notions de parité et d’imparité pour les entiers.

Par définition, un entier relatif `n` est pair si `∃ k, n = 2*k`.
Par définition, un entier relatif `n` est impair si `∃ k, n = 2*k + 1`.

Il peut donc être utile de réviser la feuille sur le quantificateur existentiel.

On pourra utiliser que la base de donnés de disjonctions contient l’énoncé :
`∀ n, n est pair v n est impair`.
-/
Exercice-lemme mul_succ_pair "05.4 n(n+1) est toujours pair"
  Données : (n : ℤ)
  Hypothèses :
  Conclusion : n*(n+1) est pair
Démonstration :
  sorry
QED

/-
L’exercice précédent est un exercice-lemme, ce qui signifie que son résultat a
été ajouté à la base de données de résultats utilisables sans les nommer.
Ainsi, si le contexte d’une démonstration comporte un entier `p`, on pourra
écrire
```
  Comme p*(p + 1) est pair on obtient l tel que hl : p*(p + 1) = 2*l
```
sans justifier pourquoi `p*(p + 1)` est pair.

On pourra réviser avec profit la feuille concernant l’implication et
l’équivalence pour se souvenir comment démontrer une équivalence vue comme
double implication.
-/

Exercice "05.5 Un entier est pair si et seulement si son carré est pair"
  Données : (n : ℤ)
  Hypothèses :
  Conclusion : n est pair ⇔ n^2 est pair
Démonstration :
  sorry
QED

/-
On va maintenant combiner le quantificateur universel, l’équivalence
et la disjonction.

La base de données de disjonctions du cours comporte l’énoncé
`∀ x y, x ≤ y ⇒ x = y v x < y`.
-/

Exercice "05.6 Une caractérisation des fonctions croissantes."
  Données : (f : ℝ → ℝ)
  Hypothèses :
  Conclusion : f est croissante ⇔ (∀ x y, x < y ⇒ f x ≤ f y)
Démonstration :
  sorry
QED


