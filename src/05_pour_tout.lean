import lib.m154

/-
# Quantificateur universel 

Ce fichier est consacré au quantificateur universel, symbolisé par `∀`. 

On rappelle qu'un *prédicat* est un énoncé dépendant d'un objet `x` d'un type `X` fixé. 
Le plus souvent pour nous `X = ℝ`, le type des nombres réels. Un prédicat n'est donc 
pas un énoncé mathématique autonome.

À partir d'un prédicat `P`, on peut former l'énoncé autonome : 
« Pour tout x, P x », qu'on note `∀ x, P x`. La définition suivante
construit un énoncé, portant sur une fonction `f` fixée, à partir du prédicat 
qui associe à tout nombre réel `x` l'énoncé `f (-x) = f x` 
(notons que Lean est économe en parenthèses ici).
-/

def paire (f : ℝ → ℝ) := ∀ x, f (-x) = f x

/-
Dans l'énoncé `∀ x, f(-x) = f x`, le type `ℝ` de `x` n'apparait pas explicitement
car on peut le déduire de l'information que `f` est une fonction de `ℝ` dans `ℝ`
qui est visiblement appliquée à `x`.

Cependant il peut être plus clair de l'indiquer explicitement comme dans la 
définition suivante, et ce serait indispensable sans l'indication fournie par `f x`. 
-/

def impaire (f : ℝ → ℝ) := ∀ x : ℝ, f (-x) = -f x

/-
Sur papier on écrit « ∀ x ∈ ℝ, » plutôt que « ∀ x : ℝ, ».

Pour *démontrer* un énoncé de la forme `∀ x, P x` où `P` est un prédicat, 
il faut se donner un élément `x` arbitraire et démontrer l'énoncé `P x`.
Dans Lean on utilisera la commande `Soit x`, pour se donner un élément `x`.
Pour plus de clarté, on peut indiquer le type d'objet `x` considéré en écrivant
`Soit x : ℝ,`. Sur paper on écrirait plutôt : « Soit x un nombre réel »,
ou bien « Soit x ∈ ℝ ».
-/

-- La fonction qui envoie `x` sur `x²` est paire.
example : paire (fct x ↦ x^2) :=
begin
  Soit x : ℝ,
  On calcule,
end

-- La fonction qui envoie `x` sur `x³` est impaire.
example : impaire (fct x ↦ x^3) :=
begin
  sorry
end

/-
Pour *utiliser*  un énoncé de la forme `∀ x, P x` où `P` est un prédicat,  
on peut le spécialiser à n'importe quel objet `x` de type `X`. 
Voyons d'abord un exemple où on peut conclure immédiatement.
-/

example (f : ℝ → ℝ) (hf : paire f) : f (-5) = f 5 :=
begin
  On conclut par hf appliqué à 5,
end

/- On peut aussi spécialiser une hypothèse de la forme `∀ x, P x` à un
`x` donné et l'utiliser un peu plus tard. -/

example (f g : ℝ → ℝ) (hf : paire f) : g (f (-5)) = g (f 5) :=
begin
  On applique hf à 5,
  On réécrit via hf,
end

example (f : ℝ → ℝ) (hf : impaire f) : f (-3) = - f 3 :=
begin
  sorry
end

/-
Voyons maintenant un exemple qui démontre un énoncé quantifié en utilisant
deux hypothèses quantifiées.
Dans cet exemple, on nomme `x₀` le nombre réel introduit par la 
commande `Soit` pour insister sur le fait qu'il est fixé et bien voir 
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
  ... = (f + g) x₀ : by On calcule,
end

/-
Dans la démonstration précédente, la ligne commençant par "Montrons que"
est purement psychologique, Lean n'en a pas besoin du tout.

De plus on n'est pas obligé d'expliciter la définition de "paire"
dans la première ligne. 

Enfin Lean n'a pas vraiment besoin qu'on lui dise à quel réel appliquer 
les hypothèses de parité, il lui suffit de chercher dans le but en cours 
donc les lignes de spécialisation `On applique` sont inutiles.

On peut donc aussi utiliser la version ci-dessous.
-/

-- Si f et g sont paires alors leur somme l'est aussi,
-- avec une démonstration moins bavarde.
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
On peut aussi utiliser la commande `Par ... appliqué à ... on obtient ...`
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


