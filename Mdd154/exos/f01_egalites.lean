import Mdd154.Lib
setup_env

/-
# Feuille 1 : Calculs

Le logiciel connait les règles de simplification algébrique usuelles.
Cela lui permet de démontrer des égalités entre expressions portant
sur des nombres arbitraires, sans aucune hypothèse.

Commençons par un exemple où le résultat est clair à l’œil nu.
-/

Exemple "Calcul purement algébrique facile"
  Données : (a b : ℝ)
  Hypothèses :
  Conclusion : a + b - a = b
Démonstration :
  On calcule
QED

/-
L’ordinateur vérifie ce genre de résultat en développant patiemment.
L’important est que le résultat ne demande aucune hypothèse sur les nombres
`a` et `b`. Nous appelerons ceci du calcul « purement algébrique ».
-/

Exemple "Calcul purement algébrique d’apparence moins facile"
  Données : (a b : ℝ)
  Hypothèses :
  Conclusion : (a + b)^3 - (a - b)^3 = 6*a^2*b + 2*b^3
Démonstration :
  On calcule
QED

/-
À vous de jouer !
-/
Exercice "01.1 Calcul purement algébrique d’apparence moins facile"
  Données : (a b : ℝ)
  Hypothèses :
  Conclusion : (a + b)^3 + (a - b)^3 = 6*a*b^2 + 2*a^3
Démonstration :
  sorry
QED

/-
Les choses plus intéressantes commencent lorsqu’on fait des hypothèses.
On peut alors alterner des étapes faisant intervenir ces hypothèses et des
étapes de calcul algébrique purement algébrique.

Chaque hypothèse a un nom, mais il n’est pas nécessaire d’y faire référence.
Dans l’exemple suivant, on fait l’hypothèse que `b` vaut `2`, et on nomme cette
hypothèse `hb`. La première ligne du calcul invoque cette hypothèse, la seconde
est purement algébrique. La justification `par calcul` fait exactement le même
travail que `On calcule`.
-/

Exemple "Un calcul faisant intervenir une hypothèse"
  Données : (a b : ℝ)
  Hypothèses : (hb : b = 2)
  Conclusion : a + a*b = 3*a
Démonstration :
  Calc
    a + a*b = a + a*2 puisque b = 2
    a + a*2 = 3*a     par calcul
QED

/-
Il est important de bien distinguer les deux types d’étapes de calcul
apparaissant ci-dessus. La premier fait intervenir une hypothèse, la seconde non.

Les règles d’indentation sont très pointilleuses et un peu complexes,
particulièrement quand un calcul ne termine pas la démonstration.
Le plus sûr est de toujours laisser `Calc` seul sur sa ligne puis
indenter les lignes suivantes, avec le même niveau d’indentation d’une ligne à l’autre.

L’alignement des signes d’égalité et des justifications sont purement cosmétiques.

Le fait de répéter le `a + a*2` est pénible. Comme sur papier, on peut s’en passer.
Sur papier on écrit rien, ici on remplace la répétition par `_`, toujours avec la même règle
d’alignement.
-/

Exemple "Le même calcul, sans répéter le membre de droite à gauche de la ligne suivante."
  Données : (a b : ℝ)
  Hypothèses : (hb : b = 2)
  Conclusion : a + a*b = 3*a
Démonstration :
  Calc
    a + a*b = a + a*2 puisque b = 2
    _       = 3*a     par calcul
QED

Exercice "01.2 Calcul en deux étapes utilisant une hypothèse"
  Données : (a b : ℝ)
  Hypothèses : (ha : a = -b)
  Conclusion : b + b*(a + b) = b
Démonstration :
  sorry
QED

Exercice "01.3 Calcul en quatre étapes utilisant des hypothèses"
  Données : (a b c : ℝ)
  Hypothèses : (h : a = -b) (h' : b + c = 0)
  Conclusion : b*(a - c) = 0
Démonstration :
  sorry
QED

/-
Les calculs peuvent aussi démontrer des inégalités.
-/

Exemple "Une première inégalité"
  Données : (a b : ℝ)
  Hypothèses : (h : a ≤ 2*b)
  Conclusion : a + b ≤ 3*b
Démonstration :
  Calc
    a + b ≤ 2*b + b puisque a ≤ 2*b
    _     = 3*b     par calcul
QED

Exercice "01.4 Inégalité"
  Données : (a b : ℝ)
  Hypothèses : (h : b ≤ a)
  Conclusion : a + b ≤ 2*a
Démonstration :
  sorry
QED

Exercice "01.5 Inégalité"
  Données : (a b : ℝ)
  Hypothèses : (h : a + b ≤ 3)
  Conclusion : 2*a + b ≤ a + 3
Démonstration :
  sorry
QED

/-
On notera que la commande `Calc` se charge de gérer l’enchaînement des symboles
de relation, ici une inégalité (large) suivie d’une égalité. Voyons un exemple faisant
intervenir également une inégalité stricte. On notera que l’enchaînement d’une inégalité
large est d’une inégalité stricte fournit en conclusion une inégalité stricte.
-/

Exemple "Inégalités larges et strictes"
  Données : (a b : ℝ)
  Hypothèses : (h : a + b ≤ 3) (hb : a < 5)
  Conclusion : 2*a + b < 8
Démonstration :
  Calc
    2*a + b = a + a + b par calcul
    _       ≤ a + 3     puisque a + b ≤ 3
    _       < 5 + 3     puisque a < 5
    _       = 8         par calcul
QED

Exercice "01.6 Inégalités larges et strictes"
  Données : (a b : ℝ)
  Hypothèses : (h : 2*a + b ≤ 3) (hb : a < 5)
  Conclusion : 3*a + b < 8
Démonstration :
  sorry
QED


/-
Une étape de calcul peut faire intervenir deux hypothèses comme justification.
Il est important de comprendre que l’objectif n’est pas de regrouper deux lignes
de calcul en une. Dans l’exemple suivant, l’inégalité `b*(a + b) ≤ b*3`
nécessite à la fois de savoir que `a + b ≤ 3` et que `b ≥ 0`, on ne peut pas la séparer
en deux étapes.
-/

Exemple "Inégalité avec deux éléments de justification"
  Données : (a b : ℝ)
  Hypothèses : (h : a + b ≤ 3) (h' : b ≥ 0)
  Conclusion : b*(a + b) ≤ 3*b
Démonstration :
  Calc
    b*(a + b) ≤ b*3 puisque a + b ≤ 3 et b ≥ 0
    _         = 3*b par calcul
QED

Exercice "01.7 Inégalité avec deux éléments de justification"
  Données : (a b : ℝ)
  Hypothèses : (h : a + b ≤ 2) (h' : a ≥ 0)
  Conclusion : a*(a + b) + a ≤ 3*a
Démonstration :
  sorry
QED

