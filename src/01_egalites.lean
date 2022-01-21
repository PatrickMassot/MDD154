import lib.m154

/-
# Les calculs sont déjà des démonstrations

Au cœur de la notion de calcul en mathématiques se trouve le principe d'égalité de Leibniz : 
« deux objets mathématiques sont égaux si et seulement si on peut remplacer l'un par l'autre
dans n'importe quel énoncé sans changer la véracité de l'énoncé ». Pour appliquer ce principe,
il nous faut des théorèmes mathématiques assurant l'égalité de certains objets. Par exemple,
le théorème de commutativité de la multiplication assure que `a * b = b * a` pour tous nombres
`a` et `b`. Un calcul utilisant cette égalité est donc déjà une démonstration mathématique 
reposant sur un théorème.

Dans cette première feuille, nous allons explicitement réaliser des calculs par remplacements
successifs dans le but ou les hypothèses. Puis nous verrons comment présenter les choses de 
façon plus proche de ce qu'on écrit sur papier, et enfin comment éviter d'avoir à utiliser 
directement ces théorèmes.

Dans les exercices suivants on pourra utiliser les faits suivants :
  `mul_assoc a b c : a * b * c = a * (b * c)`
  `mul_comm a b : a * b = b * a`

Dans la formule `a * b * c = a * (b * c)`, il faut comprendre que le membre de gauche signifie
`(a * b) * c`. En cas de doute, la commande `parentheses` permet de forcer l'affichage de parenthèses
autour de toutes les opérations dans l'affichage du contexte et du but courant.

La commande `On réécrit via mul_assoc a b c,` va remplacer `a * b * c` par `a * (b * c)` dans
l'objectif courant.

Pour remplacer de la droite vers la gauche, on utilise
`On réécrit via ← mul_assoc a b c,` qui va remplacer `a * (b * c)` par `a * b * c` dans
l'objectif courant.
-/

example (a b c : ℝ) : (a * b) * c = b * (a * c) :=
begin
  parentheses, -- On demande à Lean d'afficher des parenthèses autour de toutes les opérations
  On réécrit via mul_comm a b,
  On réécrit via mul_assoc b a c,
end

/-
Voici maintenant la même démonstration avec l'affichage normal, sans la commande `parentheses`.
-/

example (a b c : ℝ) : (a * b) * c = b * (a * c) :=
begin
  On réécrit via mul_comm a b,
  On réécrit via mul_assoc b a c,
end


/-
C'est à vous de jouer. Remplacez le mot sorry par une démonstration acceptée par l'ordinateur.
-/

example (a b c : ℝ) : (c * b) * a = b * (a * c) :=
begin
  sorry
end

example (a b c : ℝ) : a * (b * c) = b * (a * c) :=
begin
  sorry
end

/-
Reprendre l'exemple précédent en expérimentant ce qui se passe si on ne fournit
pas les arguments aux énoncés `mul_assoc` ou `mul_comm`.
Par exemple on pourra commencer par `On réécrit via ← mul_assoc,`
-/

example (a b c : ℝ) : a * (b * c) = b * (a * c) :=
begin
  sorry
end

/-
On peut aussi réécrire dans une hypothèse du contexte local, en utilisant
par exemple `On réécrit via mul_comm a b dans hyp,` pour remplacer `a * b` par `b * a`
dans l'hypothèse `hyp`.

Dans l'exemple suivant on utilise le fait
`two_mul a : 2 * a = a + a`
-/

example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d :=
begin
  On réécrit via hyp' dans hyp,
  On réécrit via mul_comm d a dans hyp,
  On réécrit via ← two_mul (a * d) dans hyp,
  On réécrit via ← mul_assoc 2 a d dans hyp,
  On conclut par hyp,
end

/-
Dans l'exemple suivant, on pourra utiliser
`sub_self x : x - x = 0`
-/

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 :=
begin
  sorry
end

/-
La méthode des deux exemples précédents ne ressemble pas à ce qu'on écrit sur
papier. Voici comment présenter les choses autrement.
À l'intérieur de chaque paire d'accolades, l'objectif est l'égalité avec
la formule précédente. Il s'agit d'un point important, prenez le temps de bien
mettre le curseur après chaque accolade ouvrante pour voir quel est le but de chacune
de ces justifications.
-/

example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d :=
begin
  calc 
    c = d * a + b      : by { On réécrit via hyp }
  ... = d * a + a * d  : by { On réécrit via hyp' }
  ... = a * d + a * d  : by { On réécrit via mul_comm d a }
  ... = 2 * (a * d)    : by { On réécrit via two_mul }
  ... = 2 * a * d      : by { On réécrit via mul_assoc },
end

/-
Reprenons l'autre exemple par cette méthode. Le plus simple est d'écrire
d'abord tout le calcul avec ": by {}" à la fin de chaque ligne puis
de compléter les justifications.
-/

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 :=
begin
  sorry
end

/-
Les démonstrations précédentes ont épuisé notre patience avec `mul_comm`
et `mul_assoc`. Il est temps de faire travailler un peu plus l'ordinateur.
-/

example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d :=
begin
  calc 
    c = d * a + b   : by { On réécrit via hyp }
  ... = d * a + a*d : by { On réécrit via hyp' }
  ... = 2 * a * d   : by { On calcule },
end

example (a b c : ℝ) : a * (b * c) = b * (a * c) :=
begin
  sorry
end

example (a b : ℝ) : (a + b) + a = 2*a + b :=
begin
  sorry
end
/-
sub_add a b c : a - b + c = a - (b - c)
-/

/-
Si vous êtes en avance et pas encore convaincus par "On calcule",
démontrer le lemme suivant sans "On calcule", mais avec une partie des lemmes 
suivants (en plus des lemmes déjà mentionés plus haut) :
`pow_two x       : x^2 = x*x`
`mul_add a b c   : a*(b + c) = a*b + a*c`
`add_mul a b c   : (a + b)*c = a*c + b*c`
`mul_sub a b c   : a*(b - c) = a*b - a*c`
`sub_mul a b c   : (a - b)*c = a*c - b*c`
`add_sub a b c   : a + (b - c) = (a + b) - c`
`sub_add a b c   : a - b + c = a - (b - c)`
`add_assoc a b c : (a + b) + c = a + (b + c)`
`sub_sub a b c   : a - b - c = a - (b + c)`
`add_zero a      : a + 0 = a`
`zero_add a      : 0 + a = a`

Aucun des lemmes de cette feuille n'est à retenir pour la suite.
-/

example (a b : ℝ) : (a + b)*(a-b) = a^2 - b^2 :=
begin
  sorry
end

