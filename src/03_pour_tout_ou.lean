import lib.m154

/-
# Quantificateur universel et disjonctions

Ce fichier est consacré au quantificateur universel, symbolisé par `∀`
et au connecteur logique de disjonction, noté simplement « ou » sur papier
et `∨` dans Lean ainsi que dans les livres de logique pure. 

On rappelle qu'un *prédicat* sur un type d'objets mathématiques `X` est un énoncé
dépendant d'un objet `x` de type `X`. Le plus souvent pour nous `X = ℝ`, le type
des nombres réels. Un prédicat n'est donc pas un énoncé mathématique autonome.

À partir d'un prédicat `P` sur `X`, on peut former l'énoncé autonome : 
« Pour tout x, P x », qu'on note `∀ x, P x`. La définition suivante
construit un énoncé, portant sur une fonction `f` fixée, à partir du prédicat 
sur `ℝ` qui associe à tout nombre réel `x` l'énoncé `f (-x) = f x` 
(notons que Lean est économe en parenthèses ici).
-/

def paire (f : ℝ → ℝ) := ∀ x, f (-x) = f x

/-
Dans l'énoncé `∀ x, f(-x) = f x`, le type `ℝ` de `x` n'apparait pas explicitement
car on peut le déduire de l'information que `f` est une fonction de `ℝ` dans `ℝ`
qui est visiblement appliquée à `x`.

Cependant il peut être plus clair de l'indiquer explicitement, et ce serait
indispensable sans l'indication fournie par `f x`. Sur papier on écrit
« ∀ x ∈ ℝ, » plutôt que « ∀ x : ℝ, »
-/

def impaire (f : ℝ → ℝ) := ∀ x : ℝ, f (-x) = -f x

/-
Pour *démontrer* un énoncé de la forme `∀ x, P x` où `P` est un prédicat, 
il faut se donner un élément `x` arbitraire et démontrer l'énoncé `P x`.
Dans Lean on utilisera la commande `Soit x`, pour se donner un élément `x`.
Pour plus de clarté, on peut indiquer le type d'objet `x` considéré en écrivant
`Soit x : ℝ,`. Sur paper on écrirait plutôt : « Soit x un nombre réel »,
ou bien « Soit x ∈ ℝ ».

Pour *utiliser* un tel énoncé, on peut le spécialiser à n'importe quel objet `x`
de type `X`. Dans l'exemple suivant, on nomme `x₀` le nombre réel introduit
par la commande `Soit` pour insister sur le fait qu'il est fixé et bien voir 
qu'après la ligne `On applique hf à x₀`, l'hypothèse `hf` ne porte plus que 
sur ce seul nombre.
-/



-- Si f et g sont paires alors leur somme l'est aussi.
example (f g : ℝ → ℝ) : paire f → paire g →  paire (f + g) :=
begin
  Supposons (hf : ∀ x, f (-x) = f x) (hg : ∀ x, g (-x) = g x),
  Montrons que ∀ x, (f+g) (-x) = (f+g) x,
  Soit x₀ : ℝ,
  On applique hf à x₀,
  On applique hg à x₀,
  calc (f + g) (-x₀) = f (-x₀) + g (-x₀) : by On calcule
  ... = f x₀ + g (-x₀) : by On réécrit via hf 
  ... = f x₀ + g x₀ : by On réécrit via hg 
  ... = (f + g) x₀ : by On calcule
end

/-
Dans la démonstration précédente, la ligne commençant par "Montrons que"
est purement psychologique, Lean n'en a pas besoin du tout.
De plus on n'est pas obligé d'expliciter la définition de "paire"
dans la première ligne. On peut donc aussi utiliser la version ci-dessous.

De plus Lean n'a pas vraiment besoin qu'on lui dise
à quel réel appliquer les hypothèses de parité, il
lui suffit de chercher dans le but en cours donc les lignes
de spécialisation `On applique` sont inutiles.
-/

-- Si f et g sont paires alors leur somme l'est aussi, avec une démonstration moins bavarde.
example (f g : ℝ → ℝ) : paire f → paire g →  paire (f + g) :=
begin
  Supposons (hf : paire f) (hg : paire g),
  Soit x,
  calc (f + g) (-x) = f (-x) + g (-x) : by On calcule
  ... = f x + g (-x) : by On réécrit via hf
  ... = f x + g x : by On réécrit via hg
  ... = (f + g) x : by On calcule,
end

example (f g : ℝ → ℝ) : paire f → paire (g ∘ f) :=
begin
  sorry
end

example (f g : ℝ → ℝ) : impaire f → impaire g →  impaire (g ∘ f) :=
begin
  sorry
end

/-
Voyons maintenant comment manipuler des prédicats plus complexes. 
On se donne une fonction `f : ℝ → ℝ` et on forme le prédicat
portant sur deux nombres `x₁̀` et `x₂` auxquels on associe
l'énoncé `x₁ ≤ x₂ → f x₁ ≤ f x₂` (Si x₁ ≤ x₂ alors f(x₁) ≤ f(x₂)).

On peut emboîter deux quantificateurs universels pour obtenir la définition
de fonction croissante.
-/

def croissante (f : ℝ → ℝ) := ∀ x₁, (∀ x₂, x₁ ≤ x₂ → f x₁ ≤ f x₂)

/-
Un tel emboîtement est un peu lourd à lire, on peut l'abréger comme
dans la définition suivante.
-/

def decroissante (f : ℝ → ℝ) := ∀ x₁ x₂, x₁ ≤ x₂ → f x₁ ≥ f x₂

/-
Dans l'exemple suivant, la commande 
`On conclut par (hf : croissante f) appliqué à [x₁, x₂, h],`
spécialise en vol l'énoncé `hf` en lui fournissant deux nombres réels
et une hypothèse d'inégalité.
Le rappel du contenu de `hf` n'est là que pour faciliter la lecture, on
aurait pu écrire
`On conclut par hf appliqué à [x₁, x₂, h],`
-/

example (f g : ℝ → ℝ) (hf : croissante f) (hg : croissante g) : croissante (g ∘ f) :=
begin
  Soit x₁ x₂, 
  Supposons h : x₁ ≤ x₂,
  Montrons que g (f x₁) ≤ g (f x₂), -- Cette ligne est facultative mais facilite la lecture
  Fait F1 : f x₁ ≤ f x₂,
    On conclut par (hf : croissante f) appliqué à [x₁, x₂, h],
  On conclut par (hg : croissante g) appliqué à [f x₁, f x₂, F1],
end

/-
On peut aussi utiliser la commande `Par ... appliqué à ... on obtient`
pour spécialiser un énoncé quantifié universellement, comme dans 
la variante suivante.
-/

example (f g : ℝ → ℝ) (hf : croissante f) (hg : croissante g) : croissante (g ∘ f) :=
begin
  Soit x₁ x₂, 
  Supposons h : x₁ ≤ x₂,
  Montrons que g (f x₁) ≤ g (f x₂),
  Par hf appliqué à [x₁, x₂, h] on obtient hf' : f x₁ ≤ f x₂,
  On conclut par hg appliqué à [f x₁, f x₂, hf'],
end

/-
Dans le morceau de commande `on obtient hf' : f x₁ ≤ f x₂`,
la partie `: f x₁ ≤ f x₂` est facultative, car Lean sait bien
ce qu'on obtient en appliquant `hf`, mais elle aide à passer à
la rédaction sur papier. On peut donc commencer par ne pas 
l'utiliser lors de la recherche de démonstration puis la rajouter
avant de passer sur papier.

Voici encore une autre variante, avec `On applique` : 
-/
example (f g : ℝ → ℝ) (hf : croissante f) (hg : croissante g) : croissante (g ∘ f) :=
begin
  Soit x₁ x₂, 
  Supposons h : x₁ ≤ x₂,
  Montrons que g (f x₁) ≤ g (f x₂),
  On applique hf à [x₁, x₂, h],
  On conclut par hg appliqué à [f x₁, f x₂, hf],
end

/- Le même en raisonnant vers l'arrière. On remarquera que Lean se débrouille pour comprendre à
quels nombres réels appliquer les hypothèses de croissance. -/
example (f g : ℝ → ℝ) (hf : croissante f) (hg : croissante g) : croissante (g ∘ f) :=
begin
  Soit x₁ x₂, 
  Supposons h : x₁ ≤ x₂,
  Montrons que (g ∘ f) x₁ ≤ (g ∘ f) x₂,
  Par hg il suffit de montrer que f x₁ ≤ f x₂,
  Par hf il suffit de montrer que x₁ ≤ x₂,
  On conclut par h,
end

example (f g : ℝ → ℝ) (hf : croissante f) (hg : decroissante g) : decroissante (g ∘ f) :=
begin
  sorry
end

/-
Le symbole `∨` (qui n'est pas un v) désigne le connecteur logique « ou ».
Pour *utiliser* une hypothèse de la forme
`hyp : P ∨ Q`
lors de la démonstration d'un but `R`, on tape
`On discute en utilisant hyp,`
(ou bien `On discute en utilisant (hyp : P ∨ Q),` pour plus de clarté)
qui crée deux branches dans la démonstration :
une branche où il faut démontrer `P → R`
et l'autre où il faut démontrer `Q → R`.

Pour *démontrer* un but de la forme `P ∨ Q`, on utilise 
`Montrons que P` et on démontre P ou `Montrons que Q` et
on démontre Q (il faut donc faire un choix stratégique).

Dans l'exemple suivant, on utilise aussi
la commande `On combine` suivie d'une liste d'hypothèses,
qui cherche à démontrer une égalité ou une inégalité 
par combinaison linéaire de ces hypothèses. 
Si la liste ne consiste qu'en une seule hypothèse,
il est plus naturel d'utiliser `On conclut par`.
Cette commande permet aussi de déduire `a ≤ b` de `a < b`
ou d'autres trivialités de ce genre.

Enfin on utilise le lemme
`mul_eq_zero : a*b = 0 ↔ a = 0 ∨ b = 0`
qui servira aussi dans l'exercice suivant.
-/

example (a b : ℝ) : a = a*b → a = 0 ∨ b = 1 :=
begin
  Supposons hyp : a=a*b,
  Fait H : a*(1 - b) = 0,
    calc a*(1 - b) = a - a*b : by On calcule
               ... = 0       : by On conclut par hyp,
  On réécrit via mul_eq_zero dans H qui devient a = 0 ∨ 1 - b = 0,
  On discute en utilisant (H : a = 0 ∨ 1 - b = 0),
    Supposons H : a = 0,
    Montrons que a = 0,
    On conclut par H,
  Supposons H : 1 - b = 0,
  Montrons que b = 1,
  On conclut par H,
end

example (x y : ℝ) : x^2 = y^2 → x = y ∨ x = -y :=
begin
  sorry
end

/-
On va maintenant combiner le quantificateur universel
et la disjonction dans deux exercices plus intéressants.

Dans l'exercice suivant, on pourra utiliser le lemme
`eq_or_lt_of_le : x ≤ y → x = y ∨ x < y`
-/
example (f : ℝ → ℝ) : croissante f ↔ ∀ x y, x < y → f x ≤ f y :=
begin
  sorry
end

/-
Dans l'exercice suivant, on pourra utiliser le lemme
`le_total x y : x ≤ y ∨ y ≤ x`

Cet exercice nécessite de réfléchir un peu plus que les
précédents, l'énoncé n'étant pas complètement évident.
-/
example (f : ℝ → ℝ) (h : croissante f) (h' : ∀ x, f (f x) = x) : ∀ x, f x = x :=
begin
  sorry
end

