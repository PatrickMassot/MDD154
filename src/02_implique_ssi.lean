import lib.m154

namespace m154
open nat
/-
# Implications et équivalences

Ce fichier aborde l'étude des connecteurs logiques `↔` (équivalence logique, notée ⇔ sur papier)
et `→` (implication, notée `⇒` sur papier). Les exercices proposés, basés purement sur
ces connecteurs et les outils du fichier 01 sont un peu artificiels. Il s'agit d'être patient,
les exercices naturels arriveront dans le fichier suivant avec le quantificateur universel.

Dans la suite, on pourra utiliser les énoncés suivants.

`inferieur_ssi (x y : ℝ) : x ≤ y ↔ 0 ≤ y - x`

`inferieur_ssi' (x y : ℝ) : x ≤ y ↔ x - y ≤ 0`

`pos_pos (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x*y`

`neg_neg (x y : ℝ) (hx : x ≤ 0) (hy : y ≤ 0) : 0 ≤ x*y`

Pour utiliser une équivalence, on peut réécrire comme avec une égalité,
à l'aide de `On réécrit via` et `On réécrit via ←`.

Pour démontrer une équivalence par double implication on utilise
`Montrons que` suivi de l'implication directe.
Une fois celle-ci démontrée, on utilise
`Montrons que` suivi de l'implication inverse.

Pour démontrer une implication P → Q, la commande
`Supposons hyp,`
permet de remplacer le but par Q et d'inclure P 
dans nos hypothèses sous le nom hyp.

Pour introduire un énoncé intermédiaire, on utilise
`Fait nom : énoncé,`
Cela entraîne l'apparition d'un nouveau but à démontrer 
avant de reprendre le fil de la démonstration principale.
-/

-- Dans toute la suite, a, b, c et d désignent des nombres réels.
variables {a b c d : ℝ}

/-
Commençons par une rédaction qui ne serait pas naturelle sur papier
mais qui montre bien comment l'opération de remplacement en utilisant
une équivalence permet de transformer le but ou une hypothèse.
On notera que la démonstration utilise aussi le remplacement en
utilisant une égalité comme dans le fichier 01.
-/

lemma inferieur_add_gauche : a ≤ b ↔ c + a ≤ c + b :=
begin
  -- On commence par s'équiper d'un fait intermédiaire qui servira 
  -- pour les deux implications
  Fait clef : c + b - (c + a) = b - a,
    On calcule,
  -- On peut maintenant montrer la première implication
  Montrons que a ≤ b → c + a ≤ c + b,
    Supposons hab : a ≤ b,
    On réécrit via inferieur_ssi,   -- Ici On réécrit via en utilisant une équivalence
    On réécrit via clef,            -- Ici il s'agit d'une égalité
    On réécrit via ← inferieur_ssi, -- et ici de nouveau une équivalence
    On conclut par hab,
  -- On passe à l'implication réciproque
  Montrons que c + a ≤ c + b → a ≤ b,
  Supposons h : c + a ≤ c + b,
  On réécrit via inferieur_ssi,
  On réécrit via ← clef,
  On réécrit via inferieur_ssi dans h,
  On conclut par h,
end

/-
Comme dans le cas des manipulations d'égalité, on peut
obtenir une rédaction plus familière à l'aide de la commande `calc`.

Là encore, chaque justification doit faire le lien avec la ligne précédente
(ou avec le membre de gauche sur la première ligne).
-/

example : a ≤ b ↔ c + a ≤ c + b :=
begin
  Fait clef : c + b - (c + a) = b - a,
    On calcule,
  calc 
  a ≤ b ↔ 0 ≤ b - a              : by On réécrit via inferieur_ssi
    ... ↔ 0 ≤ (c + b) - (c + a)  : by On réécrit via clef
    ... ↔ c + a ≤ c + b          : by On réécrit via ← inferieur_ssi,
end

/-
Remarque : la commande `On calcule` est en fait capable de faire le 
remplacement de la deuxième ligne directement, on peut donc écrire :
-/

example : a ≤ b ↔ c + a ≤ c + b :=
begin
  calc 
  a ≤ b ↔ 0 ≤ b - a              : by On réécrit via inferieur_ssi
    ... ↔ 0 ≤ (c + b) - (c + a)  : by On calcule
    ... ↔ c + a ≤ c + b          : by On réécrit via ← inferieur_ssi,
end

lemma inferieur_add_droite : a ≤ b ↔ a + c ≤ b + c :=
begin
  sorry
end

/-
Dans l'exemple suivant, on utilise un remplacement d'énoncé à
l'intérieur d'un calcul sur des nombres. En effet, la justification
de la deuxième ligne doit démontrer `0 + b ≤ a + b`. On commence par
transformer ce but en `0 ≤ a` en invoquant le lemme 
`inferieur_add_droite` démontré ci-dessus, puis on conclut par l'hypothèse `hb`.
-/

lemma inferieur_add_pos_gauche (hb : 0 ≤ a) : b ≤ a + b :=
begin
  calc b = 0 + b : by On calcule
     ... ≤ a + b : by { On réécrit via ← inferieur_add_droite, On conclut par hb }
end

lemma inferieur_add_pos_droite (hb : 0 ≤ b) : a ≤ a + b :=
begin
  sorry
end

lemma inferieur_add_pos (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b :=
begin
  sorry
end

lemma inferieur_add (hab : a ≤ b) (hcd : c ≤ d) : a + c ≤ b + d :=
begin
  sorry
end

/-
Pour utiliser une implication on peut raisonner vers l'arrière : si P implique Q alors
pour montrer Q, il suffit de montrer P. La commande Lean pour faire cela avec une implication
`imp` dont la prémisse est `hyp`, est :
`Par imp il suffit de montrer que hyp,`
S'il y a plusieurs choses à montrer, disons `hyp₁` et `hyp₂`, on utilise
`Par imp il suffit de montrer que [hyp₁, hyp₂]`
-/

lemma inferieur_mul_droite (hc : 0 ≤ c) (hab : a ≤ b) : a*c ≤ b*c :=
begin
  On réécrit via inferieur_ssi,
  Fait clef : b*c - a*c = (b - a)*c,
    On calcule,
  On réécrit via clef,
  Par pos_pos il suffit de montrer que [0 ≤ b-a, 0 ≤ c], 
    -- Noter que Lean comprend tout seul à quels nombres appliquer le lemme pos_pos
  On réécrit via ← inferieur_ssi,
  On conclut par hab,
  On conclut par hc,
end

/- 
On peut aussi raisonner vers l'avant, en énonçant une succession de faits intermédiaires.
La commande `On conclut par ...` peut être complétée en fournissant un
argument ou une liste d'arguments, comme dans :
`On conclut par pos_pos appliqué à [hab', hc],`
de la démonstration suivante (du même énoncé que `inferieur_mul_droite`).
-/
example (hc : 0 ≤ c) (hab : a ≤ b) : a*c ≤ b*c :=
begin
  Fait hab' : 0 ≤ b - a,
    On réécrit via ← inferieur_ssi,
    On conclut par hab,
  Fait h₁ : 0 ≤ (b - a)*c,
    On conclut par pos_pos appliqué à [hab', hc],
  Fait h₂ : (b - a)*c = b*c - a*c,
    On calcule,
  Fait h₃ : 0 ≤ b*c - a*c,
    On réécrit via ← h₂,
    On conclut par h₁,
  On réécrit via inferieur_ssi,
  On conclut par h₃,
end

-- Encore une variante avec un calc
example (hc : 0 ≤ c) (hab : a ≤ b) : a*c ≤ b*c :=
begin
  Fait hab' : 0 ≤ b - a,
    On réécrit via ← inferieur_ssi,
    On conclut par hab,
  On réécrit via inferieur_ssi,
  calc 0 ≤ (b - a)*c  : by On conclut par pos_pos appliqué à [hab', hc]
     ... =  b*c - a*c : by On calcule,
end

example (hc : c ≤ 0) (hab :  a ≤ b) : b*c ≤ a*c :=
begin
  sorry
end

-- Essayer maintenant un autre style pour démontrer le même énoncé
example (hc : c ≤ 0) (hab :  a ≤ b) : b*c ≤ a*c :=
begin
  sorry
end

/-
Beaucoup d'énoncés ci-dessus cachent en fait des implications.
Par exemple, l'énoncé
`inferieur_add_pos_gauche (hb : 0 ≤ a) : b ≤ a + b`
se lit « Supposons que 0 ≤ a. Montrons que b ≤ a + b ». Mais on peut le réécrire
`inferieur_add_pos_gauche' : 0 ≤ a → b ≤ a + b`
qui se lit « Si 0 ≤ a alors b ≤ a + b ». Le contenu mathématique de ces deux énoncés est le même,
la différence est purement stylistique.

Vérifions qu'on peut ramener se ramener à la première version.
-/
lemma inferieur_add_pos_gauche' : 0 ≤ a → b ≤ a + b :=
begin
  Supposons ha,
  On conclut par inferieur_add_pos_gauche appliqué à ha,
end

/-
En fait Lean ne fait aucune différence entre les deux versions de ce lemme, comme on peut le voir
dans la version suivante.
-/
lemma inferieur_add_pos_gauche'' : 0 ≤ a → b ≤ a + b :=
begin
  On conclut par inferieur_add_pos_gauche,
end

/-
On se demande alors naturellement comment reformuler les énoncés faisant *deux* hypothèses, comme
`inferieur_add_pos (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b`

La solution la plus intuitive est de faire appel au connecteur logique « et », noté `∧`.
Une hypothèse hyp du contexte local qui est constituée de plusieurs morceaux peut être scindée
à l'aide de la commande 
`Par hyp on obtient (h₁ : énoncé₁) (h₂ : énoncé₂)` (si hyp contient 2 morceaux)
comme dans l'exemple suivant.
-/
lemma inferieur_add_pos' : (0 ≤ a ∧ 0 ≤ b) → 0 ≤ a + b :=
begin
  Supposons hyp : 0 ≤ a ∧ 0 ≤ b,
  Par hyp on obtient (ha : 0 ≤ a) (hb : 0 ≤ b),
  On conclut par inferieur_add_pos appliqué à [ha, hb],
end

/-
La nécessité de passer par une ligne intermédiaire qui scinde la conjonction `hyp` en `ha` et `hb`
montre que cette reformulation comme implication n'est pas celle que Lean utilise.
Lean reformule l'énoncé comme deux implications emboîtées, ce qui est plus commode à l'usage.

On hésitera pas à utiliser la commande `parentheses` si ces suites d'implications posent des problèmes
de lecture. 
-/
lemma inferieur_add_pos'' : 0 ≤ a → (0 ≤ b → 0 ≤ a + b) :=
begin
  On conclut par inferieur_add_pos,
end

/-
Montrons que la version utilisant une conjonction permet de retrouver la version de Lean.
Pour cela il faut savoir démontrer un énoncé de la forme `P ∧ Q` à l'aide de la commande
`Montrons que P,`
qui annonce la démonstration de `P` et incite Lean à créer un second but qui est de démontrer `Q`.
-/
lemma inferieur_add_pos''' : 0 ≤ a → (0 ≤ b → 0 ≤ a + b) :=
begin
  Supposons ha : 0 ≤ a,
  Supposons hb : 0 ≤ b,
  Par inferieur_add_pos' il suffit de montrer que 0 ≤ a ∧ 0 ≤ b,
  Montrons que 0 ≤ a,
    On conclut par ha,
  Montrons que 0 ≤ b,
  On conclut par hb,
end

/-
L'équivalence entre les deux reformulations est un fait complètement général.
Avant de démontrer ce fait, voici un exemple plus simple pour manipuler
`Par ... on obtient` et `Montrons que`.
Dans cet exercice, `P`, `Q` et `R` désignent des énoncés mathématiques quelconques.

Bien sûr Lean est parfaitement capable de démontrer automatiquement un tel énoncé,
mais ce n'est pas le but ici.
-/

example (P Q R : Prop): P ∧ Q → Q ∧ P :=
begin
  sorry
end

/-
Revenons maintenant aux deux façons de formuler des énoncés faisant deux hypothèses.
Si l'enchaînement des `Supposons ...` vous pèse, vous pouvez indiquer plusieurs 
hypothèses sur la même ligne. Par exemple si le but est de la forme `P → Q → ...`,
vous pouvez commencer par :
`Supposons (hP : P) (hQ : Q),`
-/
example (P Q R : Prop) : (P ∧ Q → R) ↔ (P → (Q → R)) :=
begin
  sorry
end

/-
## Final

On a la relation de divisibilité sur les entiers naturels :
`a ∣ b` si `b` est un multiple de `a`. Attention la barre verticale n'est pas celle du
clavier mais s'obtient par ,|

Cette relation est réflexive et antisymétrique, c'est à dire qu'on a les deux énoncés :
`divise_refl (a : ℕ) : a ∣ a`
et
`divise_antisym {a b : ℕ} : a ∣ b → b ∣ a → a = b`

De plus on a une fonction `pgcd` qui, à deux entiers naturels associde un troisième entier
(leur plus grand diviseur commun). Cette fonction est liée à la relation
de divisibilité par :

`divise_pgcd_ssi {a b c : ℕ} : c ∣ pgcd a b ↔ c ∣ a ∧ c ∣ b`

Dans l'exercice suivant, le jeu est de n'utiliser que ces trois énoncés, sans essayer
de faire avouer à Lean la définition de la divisibilité ou du pgcd.
-/

example (a b : ℕ) : a ∣ b ↔ pgcd a b = a :=
begin
  sorry
end
end m154

