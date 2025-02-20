import Mdd154.Lib

namespace m154
open Nat
/-
# Feuille 4 : Implications et équivalences

L’implication est un connecteur logique.
À partir de deux énoncés `P` et `Q`, on peut former l’énoncé `P ⇒ Q` qui se lit
« P implique Q », ou encore « Si P est vrai alors Q est vrai ».
Dans l’énoncé `P ⇒ Q`, l’énoncé `P` est appelé la prémisse de l’implication et
l’énoncé `Q` est appelé sa conclusion.

La règle d’utilisation d’un tel énoncé est appelée règle du modus ponens.
Elle affirme que si `P ⇒ Q` est vrai et si `P` est vrai alors `Q` est vrai.

L’exemple suivant montre comment utiliser directement cette règle.
-/

Exemple "Utilisation d’une implication"
  Données : (P Q : Énoncé)
  Hypothèses : (h : P ⇒ Q) (h' : P)
  Conclusion : Q
Démonstration :
  Comme P ⇒ Q et P on conclut que Q
QED

/-
La règle du modus ponens n’impose pas l’ordre des vérifications.
De façon purement cosmétique, cela signifie que la démonstration suivante est
en fait identique à la précédente.
-/

Exemple "Utilisation d’une implication, une modification d’ordre cosmétique"
  Données : (P Q : Énoncé)
  Hypothèses : (h : P ⇒ Q) (h' : P)
  Conclusion : Q
Démonstration :
  Comme P et P ⇒ Q on conclut que Q
QED

/-
De façon un peu plus significative, on peut remettre à plus tard la démonstration
de la prémisse. On parle alors de raisonnement vers l’arrière (sous-entendu l’arrière
de la flèche d’implication). Ce mode de raisonnement est particulièrement utile
lorsque l’implication est claire et que la démonstration de la prémisse est le cœur
de l’affaire. L’exemple suivant est donc assez artificiel. Nous verrons des
exemples plus significatifs plus loin. Il s’agit d’une différence de pure présentation,
pas d’une nouvelle règle de logique.
-/

Exemple "Utilisation d’une implication, en raisonnant vers l’arrière"
  Données : (P Q : Énoncé)
  Hypothèses : (h : P ⇒ Q) (h' : P)
  Conclusion : Q
Démonstration :
  Comme P ⇒ Q il suffit de montrer que P
  On conclut par hypothèse
QED

/-
Dans les exemples précédents, la véracité de `P ⇒ Q` est simplement une hypothèse.
La bibliothèque de résultats du cours contient un certain nombre d’énoncé pouvant
servir à justifier des implications. Ces énoncés seront mentionnés en commentaire
avant les exercices.

Un exemple de tel énoncé est : `∀ x : ℝ, x > 0 ⇒ x^2 > 0`. On peut donc écrire
la démonstration suivante.
-/

Exemple "Carré positif"
  Données : (a : ℝ)
  Hypothèses : (ha : a > 0)
  Conclusion : a^2 > 0
Démonstration :
  Comme a > 0 ⇒ a^2 > 0 et a > 0 on conclut que a^2 > 0
QED

/-
Un autre exemple d’énoncé disponible est
`∀ x : ℝ, x ≠ 0 ⇒ |x| > 0`.

Attention : la barre de valeur absolue est la barre verticale ordinaire
(AltGr-6 sur un clavier azerty) mais il ne faut pas mettre d’espace après la
barre ouvrante ni avant la barre fermante.
-/

Exercice "04.1 Utilisation d’une implication"
  Données : (x : ℝ)
  Hypothèses : (h : x ≠ 0)
  Conclusion : |x| > 0
Démonstration :
  sorry
QED

/-
Voyons maintenant comment enchaîner l’utilisation de deux implications.
Lorsque la règle du modus ponens ne permet pas de conclure immédiatement, on peut
remplacer le `on conclut que …` final par `on obtient F : …` où `F` est un nom
d’hypothèse au choix (parmi les noms disponibles).
-/

Exemple "Enchaînement d’implications, vers l’avant."
  Données : (a : ℝ)
  Hypothèses : (ha : a > 0)
  Conclusion : (a^2)^2 > 0
Démonstration :
  Comme a > 0 et a > 0 ⇒ a^2 > 0 on obtient ha' : a^2 > 0
  Comme a^2 > 0 et a^2 > 0 ⇒ (a^2)^2 > 0 on conclut que (a^2)^2 > 0
QED

/-
Voici la même démonstration organisée en appliquant la première implication
vers l’arrière.
-/

Exemple "Enchaînement d’implications, vers l’arrière."
  Données : (a : ℝ)
  Hypothèses : (ha : a > 0)
  Conclusion : (a^2)^2 > 0
Démonstration :
  Comme a^2 > 0 ⇒ (a^2)^2 > 0 il suffit de montrer que a^2 > 0
  Comme a > 0 et a > 0 ⇒ a^2 > 0 on conclut que a^2 > 0
QED

/-
Notez comme cette variante change l’ordre dans lequel
les implications sont utilisées. Observez soigneusement quel est
le but au début de la seconde ligne des deux démonstrations précédentes.

Lorsque vous aurez bien compris cette subtilité, choisissez votre style préféré pour
l’exercice suivante.
-/

Exercice "04.2 Enchaînement d’implications, dans votre style préféré"
  Données : (a : ℝ)
  Hypothèses : (ha : a ≠ 0)
  Conclusion : |a|^2 > 0
Démonstration :
  sorry
QED

/-
Maintenant essayez l’autre style. L’ordinateur ne vérifiera pas que les deux styles
sont différents donc vérifiez bien que les buts en début de seconde ligne sont différents.
-/

Exercice "04.3 Enchaînement d’implications, dans l’autre style"
  Données : (a : ℝ)
  Hypothèses : (ha : a ≠ 0)
  Conclusion : |a|^2 > 0
Démonstration :
  sorry
QED

/-
Arrivé à ce stade, on se lasse d’écrire des implications bien connues.
Heureusement, les commandes `Comme … on conclut que …` et
`Comme … on obtient …` font l’effort d’aller chercher dans la base de données
d’implications du cours.
On peut donc laisser ces implications implicites comme on le ferait sur papier.
-/

Exemple "Enchaînement d’implications, en laissant les implications implicites"
  Données : (a : ℝ)
  Hypothèses : (ha : a ≠ 0)
  Conclusion : |a|^2 > 0
Démonstration :
  Comme a ≠ 0 on obtient ha' : |a| > 0
  Comme |a| > 0 on conclut que |a|^2 > 0
QED

/-
Dans le style vers l’arrière, on peut commencer directement par `Il suffit de montrer que`.
-/

Exemple "Enchaînement d’implications, en laissant les implications implicites,
         avec la première implication vers l’arrière"
  Données : (a : ℝ)
  Hypothèses : (ha : a ≠ 0)
  Conclusion : |a|^2 > 0
Démonstration :
  Il suffit de montrer que |a| > 0
  Comme a ≠ 0 on conclut que |a| > 0
QED

/-
Les fans inconditionnels du modus ponens vers l’arrière pourront même écrire :
-/

Exemple "Enchaînement d’implications, en laissant les implications implicites,
         avec les deux implications vers l’arrière"
  Données : (a : ℝ)
  Hypothèses : (ha : a ≠ 0)
  Conclusion : |a|^2 > 0
Démonstration :
  Il suffit de montrer que |a| > 0
  Il suffit de montrer que a ≠ 0
  On conclut par hypothèse
QED

/-
On notera que le logiciel a pour instruction de n’utiliser qu’une implication de la base de
données à la fois. La démonstration optimiste
  `Comme a ≠ 0 on conclut que |a|^2 > 0`
ne fonctionnerait pas (c’est un choix du cours bien sûr, pas une limitation du logiciel).

Ainsi l’innocente règle du modus ponens suffit déjà à engendrer une grande diversité de styles
plus ou moins explicites et présentant l’argument dans des ordres variés.
Réfléchir à ce genre de choses est un des objectifs de ce cours.

La règle de démonstration directe d’une implication est beaucoup plus simple
car elle n’admet aucune variante stylistique.
Pour démontrer un énoncé de la forme `P ⇒ Q`, on suppose que `P` est vrai et on démontre `Q`.
Ici on utilise la commande `Supposons nom : …` où `nom` est un nom à choisir parmi les
noms disponibles et `…` est à remplacer par l’énoncé `P` (en fait le `: …` est optionnel
mais il aide la lisibilité).

On peut reprendre un exercice précédent mais, au lieu de supposer a priori
l’hypothèse `a ≠ 0`, on annonce une implication l’ayant pour prémisse.
À partir de la seconde ligne la démonstration est comme ci-dessus.
-/

Exemple "Démonstration d’une implication"
  Données : (a : ℝ)
  Hypothèses :
  Conclusion : a ≠ 0 ⇒ |a|^2 > 0
Démonstration :
  Supposons ha : a ≠ 0
  Comme a ≠ 0 on obtient ha' : |a| > 0
  Comme |a| > 0 on conclut que |a|^2 > 0
QED

Exercice "04.4 Démonstration d’une implication"
  Données : (a : ℝ)
  Hypothèses :
  Conclusion : a > 0 ⇒ (a^2)^2 > 0
Démonstration :
  sorry
QED


/-
Voyons maintenant comment manipuler des prédicats plus complexes.
On se donne une fonction `f : ℝ → ℝ` et on forme le prédicat
portant sur deux nombres `x₁` et `x₂` auxquels on associe
l'énoncé `x₁ ≤ x₂ ⇒ f x₁ ≤ f x₂` (Si x₁ ≤ x₂ alors f(x₁) ≤ f(x₂)).

On peut emboîter deux quantificateurs universels pour obtenir la définition
de fonction croissante :

`f est croissante` signifie `∀ x₁, (∀ x₂, x₁ ≤ x₂ ⇒ f x₁ ≤ f x₂)`

Un tel emboîtement est un peu lourd à lire, on peut l'abréger en
`∀ x₁ x₂, x₁ ≤ x₂ ⇒ f x₁ ≤ f x₂`.

`f est décroissante` signifie `∀ x₁ x₂, x₁ ≤ x₂ ⇒ f x₁ ≥ f x₂`.
-/

Exemple "Une composée de fonctions croissantes est croissante"
  Données : (f g : ℝ → ℝ)
  Hypothèses : (hf : f est croissante) (hg : g est croissante)
  Conclusion : (g ∘ f) est croissante
Démonstration :
  Soit x₁ x₂
  Supposons h : x₁ ≤ x₂
  Montrons que g (f x₁) ≤ g (f x₂) -- Cette ligne est facultative mais facilite la lecture
  Comme f est croissante et x₁ ≤ x₂ on obtient H : f x₁ ≤ f x₂
  Comme g est croissante et f x₁ ≤ f x₂ on conclut que g (f x₁) ≤ g (f x₂)
QED


Exemple "Une composée de fonctions croissantes est croissante.
         Variante en raisonnant vers l’arrière."
  Données : (f g : ℝ → ℝ)
  Hypothèses : (hf : f est croissante) (hg : g est croissante)
  Conclusion : (g ∘ f) est croissante
Démonstration :
  Soit x₁ x₂
  Supposons h : x₁ ≤ x₂
  Montrons que (g ∘ f) x₁ ≤ (g ∘ f) x₂
  Comme g est croissante il suffit de montrer que f x₁ ≤ f x₂
  Comme f est croissante et x₁ ≤ x₂ on conclut que f x₁ ≤ f x₂
QED

Exercice "04.5 La composée d’une fonction croissante et d’une fonction décroissante
          est décroissante."
  Données : (f g : ℝ → ℝ)
  Hypothèses : (hf : f est croissante) (hg : g est décroissante)
  Conclusion : (g ∘ f) est décroissante
Démonstration :
  sorry
QED

/-
Pour les exercices suivants, on rappelle qu’une fonction `f` est injective si,
pour tous `x` et `y`, `f x = f y ⇒ x = y`.
-/

Exercice "04.6 Une composée de fonctions injectives est injective."
  Données : (f g : ℝ → ℝ)
  Hypothèses : (hf : f est injective) (hg : g est injective)
  Conclusion : g ∘ f est injective
Démonstration :
  sorry
QED

Exercice "04.7 Si une composée est injective alors la première fonction appliquée
          est injective."
  Données : (f g : ℝ → ℝ)
  Hypothèses :
  Conclusion : g ∘ f est injective ⇒ f est injective
Démonstration :
  sorry
QED

/-
Un connecteur logique cousin de l’implication est l’équivalence.

À partir de deux énoncés `P` et `Q`, on peut former l’énoncé `P ⇔ Q` qui se lit
« P équivaut à Q » ou encore « P est vrai si et seulement si Q est vrai ».

Il y a deux façons de voir ce connecteur logique.

On peut le voir comme une double implication. En effet, dire que l’énoncé
`P ⇔ Q` est vrai signifie que les énoncés `P ⇒ Q` et `Q ⇒ P`
sont tous les deux vrais. Avec ce point de vue, il n’y a besoin d’aucune nouvelle règle
de logique. Pour utiliser que `P ⇔ Q` est vrai on peut utiliser l’une des
deux implications. Pour démontrer que `P ⇔ Q` est vrai, il faut démontrer les deux implications.

Du côté utilisation, les commandes `Comme … on obtient …` et `Comme … on conclut que …`
peuvent extraire une implication d’une équivalence, comme dans l’exemple suivant.
-/

Exemple "Utilisation d’une des implications d’une équivalence."
  Données : (P R : Énoncé)
  Hypothèses : (h : P ⇔ R) (h' : P)
  Conclusion : R
Démonstration :
  Comme R ⇔ P on obtient H : P ⇒ R
  Comme P ⇒ R et P on conclut que R
QED

Exercice "04.8 Utilisation d’une des implications d’une équivalence."
  Données : (P R : Énoncé)
  Hypothèses : (h : P ⇔ R) (h' : R)
  Conclusion : P
Démonstration :
  sorry
QED

Exercice "04.9 Utilisation d’une des implications d’une équivalence. Un cas plus complexe."
  Données : (P Q R S : Énoncé)
  Hypothèses : (hPR : P ⇔ R) (hQRS : (Q ⇒ R) ⇒ S)
  Conclusion : (Q ⇒ P) ⇒ S
Démonstration :
  sorry
QED

/-
Pour démontrer une équivalence vue comme double implication, il suffit de démontrer
les deux implications. La commande permettant d’initier cette scission est
`Montrons d'abord que …`.
-/

Exemple "Démonstration d’une équivalence par double implication."
  Données : (P Q R : Énoncé)
  Hypothèses : (hPR : P ⇒ R) (hPQ : R ⇒ Q) (hQP : Q ⇒ P)
  Conclusion : P ⇔ R
Démonstration :
  Montrons d'abord que P ⇒ R
  On conclut par hypothèse
  Montrons maintenant que R ⇒ P
  Supposons hR : R
  Comme R ⇒ Q et R on obtient hQ : Q
  Comme Q ⇒ P et Q on conclut que P
QED

Exercice "04.10 Nombre que zéro divise."
  Données : (a : ℤ)
  Hypothèses :
  Conclusion : 0 ∣ a ⇔ a = 0
Démonstration :
  sorry
QED

/-
L’autre point de vue sur l’équivalence consiste à lui faire jouer le rôle que
joue l’égalité entre objets mathématiques. De ce point de vue, on peut utiliser
un énoncé de la forme `P ⇔ Q` pour remplacer `P` par `Q` n’importe où `Q` intervient
(et vice-versa). On parle de réécriture d’énoncé (contrairement au point de vue
de la double implication, il s’agit d’une règle de logique qui vient s’ajouter à celles
concernant l’implication).

La commande `Comme … on conclut que …` et sa cousine `Comme … on obtient …`
permettent de faire cela.
-/

Exemple "Une réécriture d’énoncé qui permet de conclure directement."
  Données : (P Q R S : Énoncé)
  Hypothèses : (h : P ⇔ R) (h' : (Q ⇒ R) ⇒ S)
  Conclusion : (Q ⇒ P) ⇒ S
Démonstration :
  Comme R ⇔ P et (Q ⇒ R) ⇒ S on conclut que (Q ⇒ P) ⇒ S
QED

/-
On notera que ce point de vue rend très facile une démonstration qui était un peu complexe
par utilisation d’une double implication.

On peut également utiliser ce principe de réécriture pour changer le but,
en utilisant la commande `Comme … il suffit de montrer que …`.
Reprenons encore le même exemple.
-/

Exemple "Une réécriture d’énoncé qui permet de changer le but avant de conclure."
  Données : (P Q R S : Énoncé)
  Hypothèses : (h : P ⇔ R) (h' : (Q ⇒ R) ⇒ S)
  Conclusion : (Q ⇒ P) ⇒ S
Démonstration :
  Comme R ⇔ P il suffit de montrer que (Q ⇒ R) ⇒ S
  On conclut par hypothèse
QED

Exercice "04.11 Une réécriture d’énoncé qui permet de changer le but."
  Données : (P R : Énoncé)
  Hypothèses : (h : P ⇔ R) (h' : P)
  Conclusion : R
Démonstration :
  sorry
QED

/-
On voit encore mieux l’analogie avec l’égalité lorsqu’on démontre une équivalence
par réécritures successives.
-/

Exemple "Une démonstration d’équivalence par réécriture d’énoncés."
  Données : (P Q R S T : Énoncé)
  Hypothèses : (hPR : P ⇔ R) (hST : S ⇔ T)
  Conclusion : ((Q ⇒ R) ⇒ S) ⇔ ((Q ⇒ P) ⇒ T)
Démonstration :
  Calc
    ((Q ⇒ R) ⇒ S) ⇔ ((Q ⇒ P) ⇒ S) puisque P ⇔ R
    _             ⇔ ((Q ⇒ P) ⇒ T) puisque S ⇔ T
QED

