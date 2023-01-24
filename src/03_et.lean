import lib.m154

namespace m154
open nat M154
-- Dans toute la suite, x, a, b, c et d désignent des nombres réels.
variables {x a b c d : ℝ}

/-
# Conjonctions

Ce fichier aborde l'étude du connecteur logique de conjonction, le « et » logique. 
Il est noté `∧` par l'ordinateur et simplement `et` sur papier la plupart du temps.

Lorsqu'on dispose d'un résultat de la forme `P ∧ Q`, on peut utiliser que `P` est vrai
et que `Q` est vrai. Il y a deux possibilités pour cela. On peut explicitement
obtenir les deux énoncés à l'aide de la commande `Par ... on obtient ...` comme
dans l'exemple suivant.
-/

example (h : 0 ≤ a ∧ b ≤ 1) : b ≤ 1 :=
begin
  Par h on obtient (ha : 0 ≤ a) (hb : b ≤ 1),
  On conclut par hb,
end

/-
Cette méthode est un peu lourde quand l'hypothèse est directement accessible et 
qu'on ne compte s'en servir qu'une fois. 
On peut alors raccourcir en utilisant les suffixes `.1` et `.2` pour accéder aux
deux énoncés.
-/

example (h : 0 ≤ a ∧ b ≤ 1) : b ≤ 1 :=
begin
  On conclut par h.2,
end

example (h : 0 ≤ a ∧ b ≤ 1) : 0 ≤ a :=
begin
  sorry
end

/-
Pour démontrer un énoncé de la forme `P ∧ Q`, il faut fournir une démonstration de `P`
et une démonstration de `Q`. On utilise la commande `Montrons que` pour annoncer le début 
de la démonstration de `P`. On peut aussi réutiliser cette commande au début de la 
démonstration de `Q` mais ce n'est pas obligatoire.
-/

example (ha : a > 0) : a^2 > 0 ∧ |a| > 0 :=
begin
  Montrons que a^2 > 0,
    On conclut par carre_pos appliqué à ha,
  Montrons que |a| > 0,
    On applique non_zero_abs_pos,
    -- Notez dans la ligne suivante que la commande `On conclut` fait pour nous le 
    -- travail de déduire `a ≠ 0` de `ha : a > 0`
    On conclut par ha, 
end

/-
Dans l'exercice suivant, on pourra réutiliser le lemme
`inferieur_mul_droite (hc : 0 ≤ c) (hab : a ≤ b) : a*c ≤ b*c`
-/

example (hb : a ≤ b ∧ b ≤ c) (hd : 0 ≤ d) : a * d ≤ b * d ∧ b * d ≤ c * d :=
begin
  sorry
end

end m154


