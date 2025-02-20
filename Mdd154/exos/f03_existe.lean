import Mdd154.Lib
setup_env
open m154

/-
# Feuille 3 : Quantificateur existentiel
-/

/-
Dans l'exemple suivant, on démontre un énoncé de la forme `∃ x, P x` au moyen de
la commande `Montrons que _ convient`.
-/
Exemple "Démonstration d’existence"
  Données :
  Hypothèses :
  Conclusion : ∃ x : ℝ, x*x = 4
Démonstration :
  Montrons que -2 convient  -- Est-ce la seule possibilité ?
  On calcule
QED

Exercice "03.1"
  Données :
  Hypothèses :
  Conclusion : ∃ x : ℝ, x*x = 16
Démonstration :
  sorry
QED

/-
Dans l'exemple suivant, on utilise une hypothèse de la forme `∃ x : X, P x`
au moyen de la commande `Comme _ on obtient _ tel que`.

On notera deux choses dans le calcul.

Tout d’abord on pourrait justifier la première ligne en écrivant
`n = n' + 1 puisque n = n' + 1`
mais on évite cette formulation embarassante en écrivant
`n = n' + 1 par hypothèse`.

Ensuite le fait que `n' + 1` soit strictement positif est vrai sans faire
d’hypothèse sur l’entier naturel `n'` donc on peut le justifier avec `par calcul`.
-/

Exemple "Utilisation d’une existence, suivie d’un calcul."
  Données : (n : ℕ)
  Hypothèses : (h : ∃ n', n = n' + 1)
  Conclusion : n > 0
Démonstration :
  Comme ∃ n', n = n' + 1 on obtient n' tel que hn' : n = n' + 1
  Calc
    n = n' + 1 par hypothèse
    _ > 0      par calcul
QED

/-
Alternativement, on peut utiliser `Comme … il suffit de montrer que …`
pour transformer le but courant par substitution en utilisant une égalité.
-/

Exemple "Utilisation d’une existence, suivie d’une substitution"
  Données : (n : ℕ)
  Hypothèses : (h : ∃ n', n = n' + 1)
  Conclusion : n > 0
Démonstration :
  Comme ∃ n', n = n' + 1 on obtient n' tel que hn' : n = n' + 1
  Comme n = n' + 1 il suffit de montrer que n' + 1 > 0
  On calcule
QED

/-
Vous pouvez maintenant choisir entre ces deux styles.
-/

Exercice "03.2 Utilisation d’un existence"
  Données : (n : ℕ)
  Hypothèses : (h : ∃ n', n = n' + 3)
  Conclusion : n > 0
Démonstration :
  sorry
QED

/-
Il faut bien noter qu'en général il y a plusieurs `x` qui conviennent. Dans
l'exemple suivant, il y en a deux (sauf si y est nul).
Pour insister sur le fait qu'on en a fixé un, on l'appelle `x₀`.

Cet exemple inclut une discussion selon le signe de x₀ mais à ce stade il n’est pas
utile de retenir la façon dont cette discussion est initiée.
La démonstration utilise également implicitement la règle des signes pour les produits.
-/
Exemple "Tout carré est positif."
  Données : (y : ℝ)
  Hypothèses : (h : ∃ x, y = x*x)
  Conclusion : y ≥ 0
Démonstration :
  Comme ∃ x, y = x*x on obtient x₀ tel que hy₀ : y = x₀*x₀
  Comme y = x₀*x₀ il suffit de montrer que x₀*x₀ ≥ 0
  On discute selon que 0 ≤ x₀ ou x₀ < 0
  Supposons h' : 0 ≤ x₀
  Comme 0 ≤ x₀ on conclut que x₀*x₀ ≥ 0
  Supposons h' : x₀ < 0
  Comme x₀ ≤ 0 on conclut que x₀*x₀ ≥ 0
QED

/-
Les exercices suivants utilisent la relation de divisibilité dans ℤ
Attention : la barre de divisibilité qui n'est pas celle du clavier
mais obtenue par ,|.

Dans l’exemple suivant, on améliore la lisibilité en précisant ce que
« convient » signifie.
-/

Exemple "La divisibilité est transitive."
  Données : (a b c : ℤ)
  Hypothèses : (h1 : a ∣ b) (h2 : b ∣ c)
  Conclusion : a ∣ c
Démonstration :
  Comme a ∣ b on obtient k tel que hk : b = a*k -- (1)
  Comme b ∣ c on obtient l tel que hl : c = b*l -- (2)
  -- Pour montrer que a ∣ c, il suffit de trouver m tel que c = a*m
  Montrons que ∃ m, c = a * m
  Montrons que k*l convient : c = a * (k * l)
  Calc
    c = b*l     puisque c = b*l
    _ = (a*k)*l puisque b = a*k
    _ = a*(k*l) par calcul
QED

/-
Voyons maintenant un autre énoncé semblable.
-/

Exercice "03.3 Divisibilité et somme"
  Données : (a b c : ℤ)
  Hypothèses : (h1 : a ∣ b) (h2 : a ∣ c)
  Conclusion : a ∣ b+c
Démonstration :
  sorry
QED

/-
On commence maintenant à combiner explicitement les quantificateurs
avec la définition de la surjectivité.

On rappelle que `f est surjective` signifie `∀ y, ∃ x, f x = y`
-/

/-
L'exemple suivant illustre l'utilisation de la commande `On renomme`.
-/

Exemple "On suppose que g ∘ f est surjective. Alors g est surjective."
  Données : (f g : ℝ → ℝ)
  Hypothèses : (hyp : (g ∘ f) est surjective)
  Conclusion : g est surjective
Démonstration :
/- On commence par donner une démonstration très bavarde, mais
   cette discussion est très importante pour comprendre l'enjeu des
   variables liées et variables libres. -/
  -- Il s'agit de montrer que ∀ y, ∃ x, g(x) = y
  Montrons que ∀ y, ∃ x, g x = y
  -- Soit y un réel. On veut trouver x tel que g(x) = y
  Soit y
  -- Or notre hypothèse sur g ∘ f garantit que ∀ y, ∃ x, (g ∘ f)(x) = y
  On reformule l'hypothèse hyp en ∀ y, ∃ x, (g ∘ f) x = y
  -- A priori le symbole y apparaissant dans cette hypothèse n'a rien à voir
  -- avec le y que nous avons fixé. C'est une variable liée (ou muette)
  -- on peut la renommer z.
  On renomme y en z dans l'hypothèse hyp
  -- On a également des variables nommées x dans l'hypothèse et dans le but.
  -- Mais ce sont toutes deux des variables liées, n'ayant aucun rapport
  -- entre elles. En fait le (ou les) x promis par l'hypothèse ne conviennent
  -- pas pour notre but.
  -- Renommons donc la variable liée de l'hypothèse pour clarifier la situation.
  On renomme x en w dans l'hypothèse hyp
  -- On peut spécialiser l'hypothèse h au y que nous avons fixé
  -- ce qui fournit w tel que (g ∘ f)(w) = y
  Comme ∀ z, ∃ w, (g ∘ f) w = z on obtient w : ℝ tel que hw : g (f w) = y
  -- Montrons que f(w) convient pour notre but
  Montrons que f w convient
  -- Il s'agit de montrer que g(f(w)) = y mais ce n'est rien d'autre
  -- que notre hypothèse sur w, par définition de la composition.
  -- Sur papier on écrirait simplement « f(w) convient », sans le
  -- « Montrons que ».
  On conclut par hypothèse
QED

/-
Bien sûr l'essentiel de la discussion ci-dessus est inutile d'un point
de vue logique. Ni Lean ni une rédaction pour experts n'ont besoin
de tous ces discours. Voici la même démonstration sans bavardage.
-/
Exemple "On suppose que g ∘ f est surjective. Alors g est surjective."
  Données : (f g : ℝ → ℝ)
  Hypothèses : (hyp : (g ∘ f) est surjective)
  Conclusion : g est surjective
Démonstration :
  Soit y
  Montrons que ∃ x, g x = y -- Cette ligne est optionnelle mais facilite la lecture
  Comme (g ∘ f) est surjective on obtient w : ℝ tel que hw : (g ∘ f) w = y
  Montrons que f w convient
  On conclut par hypothèse
QED

/-
Et on peut passer à la rédaction « sur papier », par exemple :

  Soit y réel. Montrons qu'il existe x réel tel que g(x) = y.
  Par l'hypothèse de surjectivité de g ∘ f appliquée à y, on obtient w réel tel que
  g ∘ f(w) = y. Le réel f(w) convient.
-/

Exercice "03.4"
  Données : (f g : ℝ → ℝ)
  Hypothèses : (hf : f est surjective) (hg : g est surjective)
  Conclusion : (g ∘ f) est surjective
Démonstration :
  Soit y
  Comme g est surjective on obtient w tel que hw : g w = y
  Comme f est surjective on obtient z tel que hz : f z = w
  Montrons que z convient
  sorry
QED

