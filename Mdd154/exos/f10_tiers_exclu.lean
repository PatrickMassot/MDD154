import Mdd154.LibNeg
setup_env

open m154
/-
# Feuille 10 : Tiers exclu, raisonnements par l’absurde et contraposées.

## Le principe du tiers-exclu

Après l’énoncé `Faux` et la définition de la négation, le troisième et dernier
ingrédient de la théorie des négations est le principe du tiers-exclu :

« Pour tout énoncé P, P ou ¬ P ».

Ce principe ne découle pas du principe d’explosion et de la définition de la
négation, il faut le rajouter comme axiome.

Cet axiome se présente sous de multiple formes équivalentes. On commence par
l’utiliser sous sa forme d’origine.
-/

Exemple "Valeur absolue d’une somme"
  Données : (x y : ℝ)
  Hypothèses :
  Conclusion : |x + y| ≤ |x| + |y|
Démonstration :
  On discute selon que 0 ≤ x + y ou ¬ 0 ≤ x + y
  Supposons h : 0 ≤ x + y
  Calc
   |x + y| = x + y puisque x + y ≥ 0
   _       ≤ |x| + |y| puisque x ≤ |x| et y ≤ |y|
  Supposons h :  ¬ 0 ≤ x + y
  Comme ¬ 0 ≤ x + y on obtient h' : x + y < 0
  Calc
    |x + y| = -(x + y) puisque x + y < 0
    _       = -x + (-y) par calcul
    _       ≤ |x| + |y| puisque -x ≤ |x| et -y ≤ |y|
QED

/-
Dans l’exercice suivant, on pourra utiliser implicitement les faits suivants :
`∀ x ≥ 0, |x| = x`
`∀ x < 0, x = - |x|`
`∀ x, x^2 ≥ 0`
`∀ x, (-x)^2 = x^2`
-/

Exercice "10.01 Valeur absolue d’un carré"
  Données : (x : ℝ)
  Hypothèses :
  Conclusion : |x^2| = |x|^2
Démonstration :
  sorry
QED

/-
## Le raisonnement par l’absurde

On passe maintenant à la deuxième incarnation du principe du tiers exclu : le
principe de raisonnement par l’absurde. Ce raisonnement est basé sur la
conséquence suivante du tiers exclu :
Pour tout énoncé `P`, `¬ ¬ P ⇒ P`.
Ainsi pour démontrer `P`, il suffit de démontrer `¬ ¬ P`. Or, par définition, pour
démontrer `¬ ¬ P`, il suffit de supposer `¬ P` et de montrer `Faux`.
On en déduit que, pour montrer `P`, il suffit de supposer `¬ P` et de montrer
une contradiction. Comme ce raisonnement est très général et un peu fastidieux, on
l’abrège en la phrase « Supposons par l’absurde `¬ P` », où le `¬ P` peut être
remplacé par une formulation équivalente.
-/

Exemple "Dans un triangle rectangle (non dégénéré) de côtés a, b et c,
         c étant l’hypoténuse, on a : a + b > c."
  Données : (x y z : ℝ)
  Hypothèses : (hx : x > 0) (hy : y > 0) (hP : z^2 = x^2 + y^2)
  Conclusion : z < x + y
Démonstration :
  Supposons par l'absurde hn : z ≥ x + y
  Il suffit de montrer que x^2 + y^2 > x^2 + y^2
  Comme x > 0 et y > 0 on obtient hxpy: x + y > 0
  Comme x > 0 et y > 0 on obtient hxmy: x * y > 0
  Calc
   x^2 + y^2 = z^2 par hypothèse
   _ ≥ (x + y)^2 puisque x + y ≥ 0 et z ≥ x + y
   _ = x^2 + y^2 + 2*x*y par calcul
   _ > x ^ 2 + y ^ 2 puisque 2*x*y > 0
QED

/-
L’exemple suivant reprend l’exercice d’unicité de la limite d’un fichier précédent.
On ne peut pas démontrer ce résultat sans utiliser l’axiome du tiers exclu
quelque part. Dans la précédente version, cette utilisation était cachée dans le lemme
`∀ x y, (∀ ε > 0, |x - y| ≤ ε) ⇒ x = y`
(dont on démontrera une variante plus bas à l’aide du tiers exclu).
Cette fois, on illustre l’utilisation du raisonnement par l’absurde et de la
commande correspondante `Supposons par l'absurde`.
-/

Exemple "Unicité de la limite."
  Données : (u : ℕ → ℝ) (l l' : ℝ)
  Hypothèses : (hl : limite_suite u l) (hl' : limite_suite u l')
  Conclusion : l = l'
Démonstration :
  Supposons par l'absurde H : l ≠ l'
  Fait ineg : |l - l'| > 0 car
    Comme l ≠ l' on obtient H' : l - l' ≠ 0
    Comme l - l' ≠ 0 on conclut que |l - l'| > 0
  Comme u tend vers l et |l - l'|/4 > 0 on obtient N
      tel que hN : ∀ n ≥ N, |u n - l| ≤ |l - l'| / 4
  Comme u tend vers l' et |l - l'|/4 > 0 on obtient N'
      tel que hN' : ∀ n ≥ N', |u n - l'| ≤ |l - l'| / 4
  Posons N₀ := max N N' -- la commande « Posons » n'est jamais indispensable
                        -- mais elle économise quelques caractères.
  Comme ∀ n ≥ N, |u n - l| ≤ |l - l'| / 4 et N₀ ≥ N
     on obtient hN₁ : |u N₀ - l| ≤ |l - l'| / 4
  Comme ∀ n ≥ N', |u n - l'| ≤ |l - l'| / 4 et N₀ ≥ N'
     on obtient hN'₁ : |u N₀ - l'| ≤ |l - l'| / 4
  Montrons une contradiction -- Cette ligne n’est pas obligatoire mais clarifie
  -- La ligne suivante utilise implicitement l’énoncé `∀ x, x < x ⇒ Faux`
  Il suffit de montrer que |l - l'| < |l - l'|
  Calc
    |l - l'| ≤ |l - u N₀| + |u N₀ - l'|   par calcul
    _        = |u N₀ - l| + |u N₀ - l'|   par calcul
    _        ≤ |l - l'|/4 + |l - l'|/4    puisque |u N₀ -  l| ≤ |l - l'| / 4 et
                                                  |u N₀ - l'| ≤ |l - l'| / 4
    _        = |l - l'|/2                 par calcul
    _        < |l - l'|                   puisque |l - l'| > 0
QED

Exercice "10.02 Nombres plus petits que tout nombre strictement positif"
  Données : (x : ℝ)
  Hypothèses : (h : ∀ ε > 0, x ≤ ε)
  Conclusion :  x ≤ 0
Démonstration :
  sorry
QED

/-
## Le principe de contraposition

Une autre incarnation très utile de l’axiome du tiers exclu est le principe
de contraposition : pour démontrer « P ⇒ Q », il suffit de démontrer
« non Q ⇒ non P ».

L’exemple suivant illustre l’utilisation du principe de contraposition
et de la commande correspondante `Montrons la contraposée : …`.
-/

Exemple "Commande de contraposition"
  Données : (P Q : Prop)
  Hypothèses : (h : (¬ Q) ⇒ ¬ P)
  Conclusion : P ⇒ Q
Démonstration :
  Montrons la contraposée : (¬ Q) ⇒ ¬ P
  On conclut par hypothèse
QED

/-
Voici un exercice plus concret.
-/

Exercice "10.03 Contraposition concrète"
  Données : (f : ℝ → ℝ)
  Hypothèses : (hf : f est injective)
  Conclusion : ∀ x y, x ≠ y ⇒ f x ≠ f y
Démonstration :
  sorry
QED

/-
Le but de l’exercice suivant est de voir comment le principe de raisonnement
par l’absurde entraîne le principe de contradiction. Il est donc crucial de le
résoudre sans utiliser `Montrons la contraposée : …` mais en utilisant
`Supposons par l'absurde : …`.
-/
Exercice "10.04 Le principe de contraposition à partir du raisonnement par l’absurde."
  Données : (P Q : Prop)
  Hypothèses : (h : (¬ Q) ⇒ ¬ P)
  Conclusion : P ⇒ Q
Démonstration :
  sorry
QED


/- Dans cet exercice, on raisonnera par contraposition pour une des implications
et on utilisera les définitions de pair et impair.
On pourra aussi utiliser que la base de données de lemmes utilisables implicitement
contient les énoncés :
 `∀ n, ¬ n est pair ⇒ n est impair`
 `∀ n, ¬ n est impair ⇒ n est pair`
-/
Exercice "10.05 parité et élévation au carré"
  Données : (n : ℤ)
  Hypothèses :
  Conclusion : n^2 est pair ⇔ n est pair
Démonstration :
  sorry
QED


/-
## Négation des énoncés quantifiés

Il est crucial de comprendre les négations d'énoncés comportant des
quantificateurs. Dans l’exercice suivant, on utilisera seulement la
définition de la négation.
-/

Exercice "10.06 Négation d’un énoncé existentiel"
  Données : (n : ℤ)
  Hypothèses :
  Conclusion : ¬ (∃ k, n = 2*k) ⇔ ∀ k, n ≠ 2*k
Démonstration :
  sorry
QED

/-
Par contraste, la règle de négation du quantificateur universel requiert le
principe du tiers-exclu. Afin de ne pas faire trop de logique pure dans ce
cours, la section suivante explique comment utiliser ces règles de négation
sans les démontrer.

## Pousser la négation à travers un énoncé

L’exemple suivant montre comment `Il suffit de montrer que` peut reformuler le
but courant en poussant une négation à travers des quantificateurs.
-/

Exemple "La fonction x ↦ 2x n'est pas paire."
  Données :
  Hypothèses :
  Conclusion : ¬ (fun x ↦ 2*x) est paire
Démonstration :
  Montrons que ¬ ∀ x, 2 * (-x) = 2 * x -- Cette ligne est optionnelle
  Il suffit de montrer que ∃ x : ℝ, 2 * (-x) ≠ 2 * x
  Montrons que 42 convient
  -- On calcule -- ou bien
  Supposons hyp : 2 * -42 = 2 * 42
  Comme 2 * -42 = 2 * 42 on conclut que Faux
QED

Exercice "10.07 La fonction identité, x ↦ x, n'est pas majorée."
  Données :
  Hypothèses :
  Conclusion : ¬ ∃ M : ℝ, ∀ x, x ≤ M
Démonstration :
  sorry
QED

/-
Cette façon de pousser les négations est également disponible pour la commande
`Comme … on obtient h : …` où la nouvelle hypothèse `h` peut être simplement
obtenue en poussant la négation dans le fait fourni. Cela vaut également pour la variante
`Comme … on conclut que …`, comme on le voit dans l’exemple suivant.
-/

Exemple "Pousser la négation à travers un quantificateur"
  Données : (f : ℝ → ℝ)
  Hypothèses : (h : ¬ ∀ x, f (-x) ≤ f x)
  Conclusion : ∃ x, f (-x) > f x
Démonstration :
  Comme ¬ ∀ x, f (-x) ≤ f x on conclut que ∃ x, f (-x) > f x
QED

/-
Vous pouvez utiliser cette façon de pousser la négation pour démontrer un très
grand classique des « paradoxes » logiques : dans un bar non-vide, il existe
toujours une personne `p` telle que si `p` boit alors tout le monde boit.

La démonstration commence par une application du principe du tiers exclu,
c’est-à-dire par `On discute selon que … ou ¬ …` (avec le même énoncé pour remplacer
les deux séries de points de suspension).

Vous pouvez passer cet exercice si vous êtes un peu en retard sur le reste du groupe.
-/
Exercice "10.08 Le paradoxe du buveur"
  Données : (x : Bar) -- Le bar est supposé non-vide, on note `x` une personne du bar
  Hypothèses :
  Conclusion : ∃ p : Bar, (p boit ⇒ ∀ q : Bar, q boit)
Démonstration :
  sorry
QED

/-
La combinaison « contraposition puis pousser la négation » est tellement courante
que la commande `Montrons la contraposée : …` essaie automatiquement de pousser
la négation après la contraposition pour obtenir la contraposée annoncée, comme
vous le constaterez dans l’exercice suivant qui est la variante promise de
`∀ x y, (∀ ε > 0, |x - y| ≤ ε) ⇒ x = y` (et déjà démontrée par l’absurde plus haut).
-/

Exercice "10.09 Nombres plus petits que tout nombre strictement positif"
  Données : (x : ℝ)
  Hypothèses :
  Conclusion : (∀ ε > 0, x ≤ ε) ⇒ x ≤ 0
Démonstration :
  sorry
QED

/-
Dans l’exercice suivant, on pourra utiliser que la commande `On discute selon que`
connait le lemme `a ≤ b ⇒ a = b ∨ a < b`
Ainsi, en ayant l’hypothèse `hxy : x ≤ y`, la commande
`On discute selon que x = y ou x < y` permet de scinder
la discussion en deux branches, l’une supposant x = y et l’autre x < y.
-/

Exercice "10.10 Caractérisation des fonctions strictement croissantes"
  Données : (f : ℝ → ℝ)
  Hypothèses :
  Conclusion : (∀ x y, x < y ⇒ f x < f y) ⇔ (∀ x y, (x ≤ y ⇔ f x ≤ f y))
Démonstration :
  sorry
QED


