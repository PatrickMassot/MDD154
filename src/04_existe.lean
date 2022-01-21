import lib.m154
open m154

/- # Le quantificateur existentiel

Dans ce fichier, on aborde la manipulation du quantificateur existentiel.
Pour démontrer un énoncé de la forme `∃ x, P x`,
on fournit un `x₀` qui convient à l'aide de la commande `Montrons que x₀ convient`.
Ce `x₀` peut être un objet du contexte, une constante ou une expression plus
compliquée. Ensuite il faut démontrer l'énoncé `P x₀`.
-/
example : ∃ x : ℝ, x*x = 4 :=
begin
  Montrons que -2 convient,  -- Est-ce la seule possibilité ?
  On calcule,
end

/-
Pour utiliser un énoncé de la forme « h : ∃ x, P x», on utilise la commande
« Par h on obtient x₀ tel que hx₀ : P x₀ »
qui fixe un x₀ et une hypothèse hx₀ affirmant P x₀.

Ici h peut être directement un énoncé du contexte ou une expression plus
compliquée. On peut aussi utiliser la forme 
`Par h appliqué à args on obtient ...` où `args` est un argument ou une liste d'arguments.

Il faut bien noter qu'en général il y a plusieurs `x` qui conviennent. Dans
l'exemple suivant, il y en a deux.
Pour insister sur le fait qu'on en a fixé un, on l'appelle `x₀`.
On utilise aussi les lemmes `pos_pos` et `neg_neg` de la feuille 2, et le lemme 
`le_total` de la feuille 3.
-/
example (y : ℝ) (h : ∃ x, y = x*x) : y ≥ 0 :=
begin
  Par h on obtient x₀ tel que hy₀ : y = x₀*x₀,
  On réécrit via hy₀,
  On discute en utilisant (le_total 0 x₀ : 0 ≤ x₀ ∨ 0 ≥ x₀),
    Supposons h' : 0 ≤ x₀,
    On conclut par pos_pos appliqué à [h', h'],
  Supposons h' : 0 ≥ x₀,
  On conclut par neg_neg appliqué à [h', h']
end

/-
Les exercices suivants utilisent la relation de divisibilité dans ℤ
(attention à la barre de divisibilité qui n'est pas celle du clavier
mais obtenue par ,|).
Contrairement au contexte de la feuille 2, le seul lemme utile est ici
divise_def (a b : ℤ) : a ∣ b ↔ ∃ k, b = a*k
-/

-- Dans toute la suite, a b et c désignent des entiers relatifs
variables (a b c : ℤ)

/-
Dans des démonstrations un peu longues, il peut être utile de rappeler au lecteur 
ce que « convient » signifie dans dans « Montrons que x₀ convient ». 
Pour cela on peut écrire : `Montrons que x₀ convient : P x₀` comme dans l'exmple suivant.

Cet exemple illustre aussi la commande `On renomme` qui permet de renommer une variable
liée dans le but. On peut aussi renommer dans une hypothèse `hyp` en terminant 
la commande par `dans hyp`. Ce renommage n'est jamais utile pour Lean, mais permet
de gagner en lisibilité.
-/

example (h1 : a ∣ b) (h2 : b ∣ c) : a ∣ c :=
begin
  Par h1 on obtient k tel que hk : b = a*k,
  Par h2 on obtient l tel que hl : c = b*l,
  -- Pour montrer que a ∣ c, il suffit de trouver m tel que c = a*m
  On réécrit via divise_def,
  -- Comme nous avons déjà fixé un entier nommé `k`, le nom de la variable muette
  -- dans le but est perturbant.
  On renomme k en m,
  
  Montrons que k*l convient : c = a * (k * l),
  calc c = b*l     : by On conclut par hl -- par (2)
     ... = (a*k)*l : by On réécrit via hk    -- par (1)
     ... = a*(k*l) : by On calcule,
end

/-
Dans la démonstration précédente, la commande « On renomme ... en ... (dans ...) »
est purement psychologique, elle renomme une variable liée pour éviter
un conflit apparent avec le k fixé dans le contexte.

En fait l'utilisation du lemme divise_def est aussi psychologique, Lean
sait que c'est la définition de la divisibilité.
Vous pouvez essayer de commenter ces deux lignes psychologiques en ajoutant
« -- » en début de ligne.

Voyons maintenant un autre énoncé semblable.
-/

example (h1 : a ∣ b) (h2 : a ∣ c) : a ∣ b+c :=
begin
  sorry
end

example : 0 ∣ a ↔ a = 0 :=
begin
  sorry
end

/-
L'exercice suivant utilise les définitions « pair » et « impair »

def pair (n : ℤ) := ∃ k, n = 2*k
def impair (n : ℤ) := ∃ k, n = 2*k + 1

et le lemme :

pair_ou_impair (n : ℤ) : pair n ∨ impair n
-/

example (n : ℤ) : pair (n*(n+1)) :=
begin
  sorry
end

/-
On commence maintenant à combiner explicitement les quantificateurs,
avec la définition de la surjectivité.
-/

def surjective (f : ℝ → ℝ) := ∀ y, ∃ x, f x = y

/-
Dans la démonstration suivante, il sera psychologiquement confortable de demander
à Lean de déplier cette définition, à l'aide de la commande `On déplie`.
-/

-- Dans la suite f et g sont des fonctions de ℝ dans ℝ.
variables(f g : ℝ → ℝ)

-- On suppose que g ∘ f est surjective. Alors g est surjective.
example (h : surjective (g ∘ f)) : surjective g :=
/- On commence par donner une démonstration très bavarde, mais
   cette discussion est très importante pour comprendre l'enjeu des
   variables liées et variables libres. -/
begin
  -- Il s'agit de montrer que ∀ y, ∃ x, g(x) = y
  On déplie surjective, -- On pourrait aussi écrire `Montrons que ∀ y, ∃ x, g x = y`
  -- Soit y un réel. On veut trouver x tel que g(x) = y
  Soit y,
  -- Or notre hypothèse sur g ∘ f garantit que ∀ y, ∃ x, (g ∘ f)(x) = y
  On déplie surjective dans h,
  -- A priori le symbole y apparaissant dans cette hypothèse n'a rien à voir
  -- avec le y que nous avons fixé. C'est une variable liée (ou muette),
  -- on peut la renommer z.
  On renomme y en z dans h,
  -- On a également des variables nommées x dans l'hypothèse et dans le but.
  -- Mais ce sont toutes deux des variables liées, n'ayant aucun rapport
  -- entre elles. En fait le (ou les) x promis par l'hypothèse ne conviennent
  -- pas pour notre but.
  -- Renommons donc la variable liée de l'hypothèse pour clarifier la situation.
  On renomme x en w dans h,
  -- On peut spécialiser l'hypothèse h au y que nous avons fixé,
  -- ce qui fournit w tel que (g ∘ f)(w) = y
  Par h appliqué à y on obtient w tel que hw : g (f w) = y,
  -- Montrons que f(w) convient pour notre but
  Montrons que f w convient,
  -- Il s'agit de montrer que g(f(w)) = y mais ce n'est rien d'autre
  -- que notre hypothèse sur w, par définition de la composition. 
  -- Sur papier on écrirait simplement « f(w) convient », sans le
  -- « Montrons que ».
  On conclut par hw,
end
/-
Bien sûr l'essentiel de la discussion ci-dessus est inutile d'un point
de vue logique. Ni Lean ni une rédaction pour experts n'ont besoin
de tous ces discours. Voici la même démonstration sans bavardage.
-/
example (h : surjective (g ∘ f)) : surjective g :=
begin
  Soit y,
  Par h appliqué à y on obtient w tel que hw : (g ∘ f) w = y,
  Montrons que f w convient,
  On conclut par hw,
end

/-
La démonstration précédente est sans doute trop concise. Avant de la transcrire sur papier,
il vaut mieux ajouter une ligne inutile explicitant quel est le but après la première ligne.
On peut aussi ajouter quelques annotations pour nos lecteurs distraits qui auraient oublié
que f et g sont des fonctions de ℝ dans ℝ. De plus l'hypothèse h ne serait
sans pas nommée dans une version papier de cet exercice donc on ajoute aussi
une annotation au moment de l'utiliser.
-/

example (h : surjective (g ∘ f)) : surjective g :=
begin
  Soit y : ℝ,
  Montrons que ∃ x, g x = y,
  Par (h : surjective (g ∘ f)) appliqué à y on obtient (w : ℝ) tel que hw : (g ∘ f) w = y,
  Montrons que f w convient,
  On conclut par hw,
end

/-
Et on peut passer à la rédaction « sur papier », par exemple :

  Soit y réel. Montrons qu'il existe x réel tel que g(x) = y. 
  Par l'hypothèse de surjectivité de g ∘ f appliquée à y, on obtient w réel tel que
  g ∘ f(w) = y. Le réel f(w) convient. 
-/

example (hf : surjective f) (hg : surjective g) : surjective (g ∘ f) :=
begin
  sorry
end

