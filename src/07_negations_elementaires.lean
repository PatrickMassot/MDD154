import lib.m154

open m154
/-
Négations, raisonnements par l'absurde et contraposées.

Cette feuille introduit les principes logiques et commandes Lean liées
aux négations d'énoncés. Elle introduit de nombreuses nouvelles commandes :
`Montrons une contradiction`, `Supposons par l'absurde`, `On contrapose`, 
`On discute selon que` et `On pousse la négation`.
Il est donc important de bien s'accrocher à son aide-mémoire Lean.

On introduit l'idée de contradiction mathématique ou absurdité mathématique,
sous la forme d'un énoncé spécial appelé « Faux » et noté `false` par Lean.
Par définition, cet énoncé n'a pas de démonstration.

Par conséquent, Faux entraîne n'importe quel autre énoncé : pour tout énoncé P,
« Faux ⇒ P » est vrai : « si Faux alors P » ne coûte rien puisque Faux n'est
pas vrai. Une autre façon d'y penser est de se dire, comme Lean le fait,
qu'une démonstration de « Faux ⇒ P » est une machine qui transforme toute
démonstration de Faux en démonstration de P, et la machine qui ne fait rien
convient car nous n'avons rien à lui donner en entrée.

Les logiciens aiment appeler cette implication de son nom latin
« ex falso quod libet » (du faux découle tout ce que l'on veut).
La commande pour invoquer ce principe est `Montrons une contradiction`.
-/

-- Montrons que si Faux alors 0 = 1
example : false → 0 = 1 :=
begin
  -- Supposons Faux
  Supposons h : false,
  -- On veut montrer 0 = 1. Ex falso quod libet, donc il suffit de montrer Faux.
  Montrons une contradiction,
  -- Or c'est ce que nous avons supposé.
  On conclut par h,
end

/-
L'exemple précédent suggère que la définition de Faux n'est pas très utile.
Mais c'est sur elle que va s'appuyer la définition de la négation.
Si P est un énoncé, sa négation est l'énoncé « non P » défini comme
« P ⇒ Faux». Les logiciens et Lean le notent `¬ P` (mais en maths quotidiennes
on n'utilise pas de notation ici).

Ainsi l'affirmation « non P » se lit : « Si P était vrai, on aurait une
contradiction ». Par exemple, la définition de « a ≠ b » est « non (a = b) ».

On peut montrer que « non P » est vrai si et seulement si « P ⇔ Faux » est vrai,
mais en pratique c'est vraiment la définition de « non P » qui est directement
utile.
-/

-- Soit x un réel. Montrons que « non x < x ».
lemma non_strictement_inferieur_soi {x : ℝ} : ¬ x < x :=
begin
  -- Suppons x < x et démontrons une contradiction.
  Supposons hyp : x < x,
  -- L'hypothèse x < x signifie que x ≤ x et x ≠ x
  On réécrit via lt_iff_le_and_ne dans hyp,
  -- en particulier x ≠ x
  Par hyp on obtient (hyp_inf : x ≤ x) (hyp_non : x ≠ x),
  -- (l'autre condition ne servira pas).
  On oublie hyp_inf, -- La commande "On oublie"" oublie une hypothèse, 
  -- Lean n'en a pas besoin, c'est juste pour nous clarifier les idées.
  -- Par définition de ≠, l'hypothèse hyp_non signifie que, pour obtenir une
  -- contradiction, il suffit de montrer que x = x.
  On reformule hyp_non en x = x → false,
  -- (La commande "On reformule" transforme une hypothèse en un énoncé
  --  équivalent par définition, Lean n'en a pas besoin ici, c'est juste
  --  pour nous)
  Par hyp_non il suffit de montrer que x = x,
  -- Or cela découle de la réflexivité de l'égalité.
  On calcule, 
end

-- Soit n un entier. On suppose que n est pair et que n n'est pas pair.
-- Montrons alors que 0 = 1.
example (n : ℤ) (h_pair : pair n) (h_non_pair : ¬ pair n) : 0 = 1 :=
begin
  sorry
end

/-
Pour la suite, on rappelle les définitions suivantes :

`def pair (n : ℤ) := ∃ k, n = 2*k`
`def impair (n : ℤ) := ∃ k, n = 2*k + 1`

et on a les deux lemmes :

`pair_ou_impair (n : ℤ) : pair n ∨ impair n`
`non_pair_et_impair (n : ℤ) : ¬ (pair n ∧ impair n)`
-/

-- Sans utiliser la définition de pair et impair, mais en utilisant les
-- deux lemmes, montrons qu'un nombre n'est pas pair ssi il est impair.
lemma non_pair_ssi (n : ℤ) : ¬ pair n ↔ impair n :=
begin
  sorry
end

/-
Muni de la définition de la négation, on montre facilement que
tout énoncé P implique sa double négation « non non P ».

En rajoutant l'axiome du tiers exclu, qui affirme que « P ou non P » est vrai
pour tout énoncé P, on montre facilement la réciproque : « non non P »
implique P.

Au final on a alors l'équivalence entre « non non P » et P, une propriété
connue sous le nom de « principe d'élimination des doubles négations ».

L'implication « non non P ⇒ P » est la base du raisonnement par l'absurde :
pour montrer P, il suffit de montrer « non non P », c'est-à-dire
« non P ⇒ Faux » donc il suffit de supposer « non P » et de démontrer Faux.
En pratique on ne décompose pas ce petit raisonnement et on écrit directement
« Par l'absurde, supposons non P » ou « Supposons par l'absurde non P ». 
Dans Lean on écrit `Supposons par l'absurde Hyp : ¬ P`,
qui transforme le but P en false et ajoute au contexte l'hypothèse Hyp : ¬ P.
-/

/-
Reprenons une démonstration de la feuille 5, l'unicité de la limite.
On ne peut pas démontrer ce résultat sans utiliser l'axiome du tiers exclu
quelque part. Dans la feuille 5, cette utilisation était cachée dans le lemme

`egal_si_abs_eps (x y : ℝ) : (∀ ε > 0, |x - y| ≤ ε) → x = y`

(dont on démontrera une variante plus bas à l'aide du tiers exclu).
-/
example (u : ℕ → ℝ) (l l' : ℝ) : limite_suite u l → limite_suite u l' → l = l' :=
begin
  -- Supposons que u tende vers l et vers l'
  Supposons (hl : limite_suite u l) (hl' : limite_suite u l'),
  -- Supposons par l'absurde que « non (l = l') », c'est à dire l ≠ l'.
  Supposons par l'absurde H : l ≠ l',
  -- En particulier |l-l'| > 0
  Fait ineg : |l - l'| > 0,
    -- (la démonstration ci-dessous n'est pas importante, il faut juste noter
    -- qu'elle fait bien intervenir l'hypothèse H)
    On réécrit via pos_abs,
    On conclut par sub_ne_zero_of_ne appliqué à H,
  -- On peut donc appliquer l'hypothèse de convergence vers l à ε = |l'-l|/4
  -- pour obtenir N tel que ∀ n ≥ N, |u n - l| ≤ |l - l'|/4.
  Fait quart_pos : |l - l'|/4 > 0,
     On conclut par ineg,
  Par hl appliqué à [|l - l'|/4, quart_pos] on obtient N 
      tel que hN : ∀ n ≥ N, |u n - l| ≤ |l - l'| / 4,
  -- On obtient de même N' tel que ∀ n ≥ N', |u n - l'| ≤ |l - l'|/4.
  Par hl' appliqué à [|l - l'|/4, quart_pos] on obtient N' 
      tel que hN' : ∀ n ≥ N', |u n - l'| ≤ |l - l'| / 4,
  -- Ainsi, pour l'indice N₀ = max(N, N'), on a |u N₀ - l| ≤ |l - l'|/4
  Posons N₀ := max N N', -- la commande « Posons » n'est jamais indispensable
                         -- mais elle économise quelques caractères.
  Par hN appliqué à [N₀, inferieur_max_gauche N N']
     on obtient hN₁ : |u N₀ - l| ≤ |l - l'| / 4,
  -- et |u N₀ - l'| ≤ |l - l'|/4.
  Par hN' appliqué à [N₀, inferieur_max_droite N N']
     on obtient hN'₁ : |u N₀ - l'| ≤ |l - l'| / 4,

  -- On démontre alors par calcul que |l - l'| < |l - l'|
  Fait clef : |l - l'| < |l - l'|,
    calc
    |l - l'| = |(l - u N₀) + (u N₀ - l')| : by On calcule
         ... ≤ |l - u N₀| + |u N₀ - l'|   : by On applique ineg_triangle
         ... = |u N₀ - l| + |u N₀ - l'|   : by On réécrit via abs_diff
         ... ≤ |l - l'|/4 + |l - l'|/4    : by On combine [hN₁, hN'₁]
         ... = |l - l'|/2                 : by On calcule
         ... < |l - l'|                   : by On conclut par ineg,
  -- ce qui est absurde.
  On conclut par non_strictement_inferieur_soi appliqué à clef,
end

/-
Une autre incarnation très utile de l'axiome du tiers exclu est le principe
de contraposition : pour démontrer « P ⇒ Q », il suffit de démontrer
« non Q ⇒ non P ».
-/

-- En utilisant un raisonnement par l'absurde, montrer le principe
-- de contraposition
example (P Q : Prop) (h : ¬ Q → ¬ P) : P → Q :=
begin
  sorry
end

/-
En fait la réciproque du principe de contraposition est vraie aussi (et se
démontre sans même utiliser l'axiome du tiers exclu). On a donc
(P ⇒ Q) ⇔ (non Q ⇒ non P)

On prendra bien garde à ne pas confondre :
  * la contraposée de « P ⇒ Q » qui est « non Q ⇒ non P »
  * la réciproque de « P ⇒ Q » qui est « Q ⇒ P ».

En général la réciproque d'une implication n'a aucun lien logique avec
l'implication de départ.

Comme pour le raisonnement par l'absurde, le principe de contraposition n'est
pas redécomposé à chaque fois, on se contente d'écrire `On contrapose` dans Lean
et « Montrons la contraposée » ou « Par contraposition, il suffit de montrer
que » ou quelque chose d'analogue sur papier.
-/

example (P Q : Prop) (h : ¬ Q → ¬ P) : P → Q :=
begin
  On contrapose,
  On conclut par h,
end

-- Dans l'exercice suivant, on raisonnera par contraposition pour une
-- des implications, et on utilisera les définitions de pair et impair ainsi
-- que le lemme `non_pair_ssi (n : ℤ ): ¬ pair n ↔ impair n` démontré plus
-- haut.
example (n : ℤ) : pair (n^2) ↔ pair n :=
begin
  sorry
end

/-
On termine ce tour d'horizon du tiers exclu en signalant qu'il est parfois utile
d'utiliser l'axiome du tiers exclu sous sa forme d'origine : pour tout énoncé P, 
soit P est vrai soit ¬ P est vrai. Plutôt que d'invoquer cet énoncé puis de faire une
disjonction de cas à l'aide de la commande `On discute en utilisant`, Lean introduit 
le raccourci

`On discute selon que P,`

qui combine les deux étapes et crée directement deux branches de la
démonstration : une dans laquelle il faut montrer `P → but initial` et 
l'autre dans laquelle il faut montrer `¬ P → but initial`.

Dans l'exemple suivant, il n'est pas utile de retenir les lemmes concernant
la valeur absolue, on se contentera d'en observer les effets.
-/

example (x y : ℝ) : |x + y| ≤ |x| + |y| :=
begin
  Fait hx : x ≤ |x|,
    On applique le_abs_self,
  Fait hx' : -x ≤ |x|,
    On applique neg_le_abs_self,
  Fait hy : y ≤ |y|, 
    On applique le_abs_self,
  Fait hy' : -y ≤ |y|, 
    On applique neg_le_abs_self,
  
  On discute selon que 0 ≤ x + y,
    Supposons h : 0 ≤ x + y,
    calc |x + y| = x + y : abs_of_nonneg h
          ...    ≤ |x| + |y| : by On combine [hx, hy],
  Supposons h : ¬ 0 ≤ x + y,
  On réécrit via not_le dans h qui devient x + y < 0,
  calc |x + y| = -(x + y) : abs_of_neg h
           ... = -x + (-y) : by On calcule
           ... ≤ |x| + |y| : by On combine [hx', hy'],
end

example (n : ℤ) : pair (n*(n+1)) :=
begin
  sorry
end


/-
Il est crucial de comprendre les négations d'énoncés comportant des
quantificateurs. Dans l'exercice suivant, on utilisera seulement la 
définition de la négation.
-/

example (n : ℤ) : ¬ (∃ k, n = 2*k) ↔ ∀ k, n ≠ 2*k :=
begin
  sorry
end


/-
L'exercice précédent cache en fait un résultat complètement général :
Pour tout prédicat P, `(¬ ∃ x, P x) ↔ (∀ x, ¬ P x)`, et la démonstration
n'est pas plus difficile que dans l'exercice précédent.

De façon analogue, `(¬ ∀ x, P x) ↔ (∃ x, ¬ P x)`. La démonstration est
plus délicate, et nécessite le tiers exclu pour une implication. 

En pratique on ne redémontre pas constamment ces règles de négation des énoncés
quantifiés (les démonstrations ne sont même pas si simples !), on les connait
par cœur.
Dans Lean on utilise `On pousse la négation` pour pousser les négations le plus
possible vers la droite (parfois elles disparaissent complètement
si l'énoncé le plus à droite a une négation qui s'exprime bien,
par exemple si c'est une inégalité).
-/

def paire (f : ℝ → ℝ) := ∀ x, f (-x) = f x

-- Montrons que la fonction x ↦ 2x n'est pas paire.
example : ¬ paire (λ x, 2*x) :=
begin
  On déplie paire, -- Cette ligne est facultative mais permet de bien voir ce qui se passe
  On pousse la négation,
  Montrons que 42 convient,
  Supposons hyp,
  On conclut par hyp, -- Il faut avouer que cette ligne est un peu étrange, mais la commande `On conclut par`
                      -- est capable de détecter ce type de contradiction dans une hypothèse
end

example (f : ℝ → ℝ) : ¬ paire f ↔ ∃ x, f (-x) ≠ f x :=
begin
  sorry
end

def majoree (f : ℝ → ℝ) := ∃ M, ∀ x, f x ≤ M

-- La fonction identité, x ↦ x, n'est pas majorée (le λ de l'énoncé est la notation des
-- informaticiens pour ↦ ).
example : ¬ majoree (λ x, x) :=
begin
  sorry
end
/-
La combinaison « contraposition puis pousser la négation » est tellement courante 
que la commande `On contrapose,` essaie automatiquement de pousser la négation après
la contraposition, comme vous le constaterez dans l'exercice suivant qui est la variante 
promise de egal_si_abs_eps.
-/

example (x : ℝ) : (∀ ε > 0, x ≤ ε) → x ≤ 0 :=
begin
  sorry
end

/-
Dans l'exercice suivant, on pourra utiliser le lemme
`eq_or_lt_of_le : a ≤ b → a = b ∨ a < b`
Ainsi, en ayant l'hypothèse `hxy : x ≤ y`, la commande
`On discute en utilisant eq_or_lt_of_le hxy` permet de scinder
la discussion en deux branches, l'une supposant x = y et l'autre x < y.
-/

example (f : ℝ → ℝ) : (∀ x y, x < y → f x < f y) ↔ (∀ x y, (x ≤ y ↔ f x ≤ f y)) :=
begin
  sorry
end

