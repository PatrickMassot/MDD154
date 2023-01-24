import lib.m154

namespace m154
open nat
/-
# Implications 

Ce fichier aborde l'étude du connecteur logique  `→` (implication, notée `⇒` sur papier).
Les exercices proposés, basés purement sur ce connecteur et les outils du fichier 01 sont un
peu artificiels. Il s'agit d'être patient, les exercices naturels arriveront dans le fichier 
concernant le quantificateur universel.

Un énoncé `P → Q` se lit `si P alors Q`. 
Cet énoncé permet de démontrer l'énoncé `Q` dès que on peut produire une preuve de `P`.
C'est donc une justification de `Q` sous l'hypothèse que `P` est vérifié.

Par exemple l'énoncé
`carre_pos {a : ℝ} : a > 0 → a^2 > 0`
affirme que si un nombre `a` est strictement positif alors son carré l'est aussi.
On dit que `a > 0` est la prémisse de l'implication et `a^2 > 0` sa conclusion.

On peut utiliser un tel énoncé pour démontrer la conclusion de l'implication en lui
fournissant une démonstration de la prémisse. 
La commande correspondante est `On conclut par ... appliqué à ...,`.
Dans l'exemple  qui suit, l'hypothèse `ha` est une démonstration de la prémisse.
-/

-- Dans toute la suite, x, a, b, c et d désignent des nombres réels.
variables {x a b c d : ℝ}


example (ha : a > 0) : a^2 > 0:=
begin
  On conclut par carre_pos appliqué à ha,
end

/-
Entraînez-vous en utilisant le théorème
`non_zero_abs_pos {a : ℝ} : a ≠ 0 → |a| > 0`
-/

example (h : x ≠ 0) : |x| > 0:=
begin
  sorry
end

/-
Les implications permettent aussi de faire du « raisonnement vers l'arrière » :
si le but à montrer est `Q` et que l'on a une hypothèse ou un théorème `nom` de la 
forme `P → Q`, alors on peut appliquer ce théorème pour transformer le but à prouver 
en `P`.
La commande correspondante est `Par ... il suffit de montrer que ...,`. 
Reprenons l'exemple du carré de cette façon.
-/

example (ha : a > 0) : a^2 > 0:=
begin
  Par carre_pos il suffit de montrer que a > 0,
  On conclut par ha,
end

/-
Bien sûr dans l'exemple ci-dessus on ne gagne rien à raisonner vers l'arrière.
Ce n'est intéressant que quand la prémisse n'est pas immédiatement disponible, comme
dans l'exemple suivant qui commence par un pas vers l'arrière pour passer
de `(a^2)^2` à `a^2` avant de conclure en appliquant vers l'avant le même résultat 
pour `a` lui-même.
-/

example (ha : a > 0) : (a^2)^2 > 0:=
begin
  Par carre_pos il suffit de montrer que a^2 > 0,
  On conclut par carre_pos appliqué à ha,
end

/-
On peut aussi conserver un mode de raisonnement vers l'avant du début à la fin en 
introduisant un énoncé intermédiaire. Pour cela, on utilise
`Fait nom : énoncé,`
Cela entraîne l'apparition d'un nouveau but à démontrer avant de reprendre le fil 
de la démonstration principale avec `nom : énoncé` disponible comme résultat 
supplémentaire. Dans l'exemple ci-dessous, le nom choisi est `F`.
-/

example (ha : a > 0) : (a^2)^2 > 0:=
begin
  Fait F : a^2 > 0,
    On conclut par carre_pos appliqué à ha,
  On conclut par carre_pos appliqué à F,
end

example (ha : a ≠ 0) : |a|^2 > 0:=
begin
  sorry
end

/-
Pour démontrer une implication `P → Q`, la commande `Supposons hyp,`
permet d'inclure `P` dans nos hypothèses sous le nom `hyp` et de remplacer le but 
par `Q`.
-/

example : a > 0 → (a^2)^2 > 0 :=
begin
  Supposons ha : a > 0, -- Ici on introduit l'hypothèse
  Montrons que (a^2)^2 > 0, -- Cette ligne est optionelle car Lean sait où nous en sommes, 
                            -- mais elle améliore la lisibilité pour nous.
  Fait F : a^2 > 0,
    On conclut par carre_pos appliqué à ha,
  On conclut par carre_pos appliqué à F,
end


/-
Dans la suite, on pourra utiliser les énoncés suivants qui font le lien 
entre une comparaison générale de deux éléments `x ≤ y` et une comparaison 
de leur différence à `0`.

`inferieur_diff_pos {x y : ℝ} : x ≤ y → 0 ≤ y - x`
`diff_pos_inferieur {x y : ℝ} : 0 ≤ y - x → x ≤ y`

`inferieur_diff_neg {x y : ℝ} : x ≤ y → x - y ≤ 0`
`diff_neg_inferieur {x y : ℝ} : x - y ≤ 0 → x ≤ y`

Voyons un exemple qui démontre une implication en utilisant deux implications connues
(`diff_pos_inferieur` et `inferieur_diff_pos`) et un calcul.
-/

lemma inferieur_add_gauche : a ≤ b → c + a ≤ c + b :=
begin
  Supposons hab : a ≤ b, 
  Montrons que c + a ≤ c + b, 
  Par diff_pos_inferieur il suffit de montrer que 0 ≤ (c+b) - (c+a),  
  calc 
    (c+b) - (c+a) = b - a : by On calcule
              ... ≥ 0     : by On conclut par inferieur_diff_pos appliqué à hab,
end

/- A vous de jouer ! -/

lemma inferieur_add_droite : a ≤ b →  a + c ≤ b + c :=
begin
  sorry
end

lemma inferieur_simpl_gauche : c + a ≤ c + b → a ≤ b :=
begin
  sorry
end


/- 
On rencontre aussi des théorèmes ayant plusieurs hypothèses. 
Par exemple les deux énoncés suivants donnent les règles de signes pour la multiplication

`pos_pos {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x*y`

`neg_neg {x y : ℝ} (hx : x ≤ 0) (hy : y ≤ 0) : 0 ≤ x*y`

Chacun de ces énoncés déduit la conclusion `0 ≤ x*y` de deux prémisses portant sur `x` et `y`. 

L'application de ces théorèmes nécessite de justifier chacune des hypothèses, il y aura 
donc autant de buts à montrer que d'hypothèses. La commande à utiliser est alors
`Par nom il suffit de montrer que [P, Q],`
où `P` et `Q` sont les prémisses à démontrer.
-/

example (hc : 0 ≤ c) (hab : a ≤ b) : 0 ≤ (b - a) * c :=
begin
  Par pos_pos il suffit de montrer que [0 ≤ b - a, 0 ≤ c], 
    On conclut par inferieur_diff_pos appliqué à hab,
  On conclut par hc,
end

example (hc : c ≤ 0) (hab : b ≤ a) : 0 ≤ (b - a) * c :=
begin
  sorry
end

/-
Voyons comment insérer ces exemples comme faits intermédiaires dans des contextes plus 
compliqués.
-/

lemma inferieur_mul_droite (hc : 0 ≤ c) (hab : a ≤ b) : a*c ≤ b*c :=
begin
  Par diff_pos_inferieur il suffit de montrer que 0 ≤ b*c - a*c,
  Fait clef : 0 ≤ (b - a)*c,
    Par pos_pos il suffit de montrer que [0 ≤ b - a, 0 ≤ c], 
      On conclut par inferieur_diff_pos appliqué à hab,
    On conclut par hc,
  calc 
    b*c - a*c = (b - a)*c : by On calcule
          ... ≥ 0 : by On conclut par clef,
end

/-
La démonstration ci-dessus est un peu tortueuse. Nous allons la simplifier en 
faisant travailler plus l'ordinateur. La commande `On applique` se charge de 
comprendre quels sont les buts restants puis cherche chacun de ces buts parmi
les hypothèses, ne laissant à démontrer que ce qui nécessite un nouvel argument.
Dans l'exemple de base, les deux prémisses sont déjà des hypothèses et il ne 
reste rien à faire.
-/

example (hc : 0 ≤ c) (hab : 0 ≤ b - a) : 0 ≤ (b - a) * c :=
begin
  On applique pos_pos, 
end

/-
Dans l'exemple plus compliqué, on veut justifier `(b - a) * c ≥ 0` à partir
des hypothèses `hc : 0 ≤ c` et `hab : a ≤ b` donc il reste un peu de travail.
-/

example (hc : 0 ≤ c) (hab : a ≤ b) : a*c ≤ b*c :=
begin
  Par diff_pos_inferieur il suffit de montrer que 0 ≤ b*c - a*c,
  calc 
    b*c - a*c = (b - a)*c : by On calcule
          ... ≥ 0         : by { On applique pos_pos,
                                 On conclut par inferieur_diff_pos appliqué à hab }
end

/-
Adaptez cet exemple en utilisant `neg_neg` et `inferieur_diff_neg`.
-/

example (hc : c ≤ 0) (hab :  a ≤ b) : b*c ≤ a*c :=
begin
  sorry
end

/- 
On peut aussi fournir les justifications de plusieurs prémisses en raisonnant 
vers l'avant. La commande `On conclut par ...` peut aussi être complétée en fournissant un
une liste d'arguments, comme dans :
`On conclut par pos_pos appliqué à [hab', hc],`
de la démonstration suivante (où l'énoncé est toujours le même que `inferieur_mul_droite`).
-/
example (hc : 0 ≤ c) (hab : a ≤ b) : a*c ≤ b*c :=
begin
  Fait hab' : 0 ≤ b - a,
    On conclut par inferieur_diff_pos appliqué à hab,
  Fait H : b*c - a*c ≥ 0,
    calc 
      b*c - a*c = (b - a) * c : by On calcule
      ...       ≥ 0           : by On conclut par pos_pos appliqué à [hab', hc],
  On conclut par diff_pos_inferieur appliqué à H,
end

/-
Adoptez maintenant le style de la démonstration précédente pour montrer l'énoncé suivant.
-/

example (hc : c ≤ 0) (hab :  a ≤ b) : b*c ≤ a*c :=
begin
  sorry
end

/-
On peut se demander à quel connecteur logique correspondent tous ces énoncés ayant 
deux prémisses et une conclusion. Il est possible de les voir comme des implications emboîtées.
L'énoncé `inferieur_mul_droite` peut se lire : « si `0 ≤ c` alors si `a ≤ b` alors `a*c ≤ b*c` ».

Vérifions que Lean y pense bien de cette façon.
-/

example : 0 ≤ c → (a ≤ b → a*c ≤ b*c) :=
begin
  On conclut par inferieur_mul_droite,
end

/-
Ce type d'implications emboitées est en fait si courant que les parenthèses de l'énoncé ci-dessus
ne sont pas nécessaires : par défaut, Lean interprète `P → Q → R` comme `P → (Q → R)`.

Nous verrons plus tard que l'on peut aussi utiliser le connecteur logique `et` pour
écrire de tels énoncés, mais cela se révèlera moins commode en pratique. 
-/
end m154


