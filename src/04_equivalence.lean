import lib.m154

namespace m154
open nat M154
/-
# Equivalences 

Ce fichier aborde l'étude du connecteur logique `↔` (équivalence logique, notée ⇔ sur papier).
L'énoncé `P ↔ Q` si lit « `P` est vrai si et seulement si `Q` est vrai ».
Il affirme donc à la fois `P → Q` et `Q → P`.

Pour démontrer une équivalence par double implication on utilise
`Montrons que` suivi de l'implication directe.
Une fois celle-ci démontrée, on peut utiliser
`Montrons que` suivi de l'implication inverse, mais ce n'est pas obligatoire.
-/

-- Dans toute la suite, x, a, b, c et d désignent des nombres réels.
variables {x a b c d : ℝ}


/- Les lemmes `inferieur_diff_pos` et `diff_pos_inferieur` se combinent 
en une équivalence. -/

lemma inferieur_pos_ssi (x y : ℝ) : x ≤ y ↔ 0 ≤ y - x :=
begin
  Montrons que x ≤ y → 0 ≤ y - x,
  On conclut par inferieur_diff_pos,
  Montrons que 0 ≤ y - x → x ≤ y,
  On conclut par diff_pos_inferieur,
end

/-
Faites de même avec `inferieur_add_gauche` et `inferieur_simpl_gauche`.
-/

lemma inferieur_add_gauche_ssi : a ≤ b ↔ c + a ≤ c + b :=
begin
  sorry
end

/-
Pour utiliser une équivalence on peut accéder aux deux implications de façons complètement
analogue au connecteur `∧`, avec `Par ... on obtient ...` ou via le suffixe
`.1` pour l'implication de gauche à droite et `.2` pour l'autre sens.

Vérifions par exemple que le lemme ci-dessus permet de retrouver l'énoncé `inferieur_add_gauche`.
-/

example (h : a ≤ b) : c + a ≤ c + b :=
begin
  Par inferieur_add_gauche_ssi on obtient 
    (imp₁ : a ≤ b → c + a ≤ c + b) (imp₂ : c + a ≤ c + b → a ≤ b),
  On conclut par imp₁ appliqué à h,
end

/- Ou de façon plus concise. -/

example (h : a ≤ b) : c + a ≤ c + b :=
begin
  On conclut par inferieur_add_gauche_ssi.1 appliqué à h,
end

example (h : 2 + a ≤ 2 + b) : a ≤ b :=
begin
  sorry
end

/-
On peut également utiliser une équivalence pour réécrire le but ou une hypothèse, 
de même qu'une égalité peut servir à réécrire le but ou une hypothèse. La syntaxe est
la même que pour les égalités.

Par exemple, l'équivalence donnée par

`abs_inferieur_ssi : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y`

est utilisée pour réécrire l'hypothèse `h` dans la démonstration suivante.
-/

example (h : |a| ≤ 1) : a ≤ 1 :=
begin
  On réécrit via abs_inferieur_ssi dans h,
  On conclut par h.2,
end

example (h : |a| ≤ 1) : -1 ≤ a :=
begin
  sorry
end


/-
## Exercice de synthèse sur =, →, ∧, ↔

On a la relation de divisibilité sur les entiers naturels :
`a ∣ b` si `b` est un multiple de `a`. Attention la barre verticale n'est pas celle du
clavier mais s'obtient par ,|

Cette relation est réflexive et antisymétrique, c'est à dire qu'on a les deux énoncés :
`divise_refl (a : ℕ) : a ∣ a`
et
`divise_antisym {a b : ℕ} (h: a ∣ b) (h' : b ∣ a) : a = b`

De plus on a une fonction `pgcd` qui, à deux entiers naturels associde un troisième entier
(leur plus grand diviseur commun). Cette fonction est liée à la relation
de divisibilité par :

`divise_pgcd_ssi {a b c : ℕ} : c ∣ pgcd a b ↔ c ∣ a ∧ c ∣ b`

Dans l'exercice suivant, le jeu est de n'utiliser que ces trois énoncés, sans essayer
de faire avouer à Lean la définition de la divisibilité ou du pgcd.

Cet exercice est plus difficile que les exercices rencontrés jusqu'ici et nécessite 
de combiner beaucoup de manipulations logiques.
-/

example (a b : ℕ) : a ∣ b ↔ pgcd a b = a :=
begin
  sorry
end

end m154


